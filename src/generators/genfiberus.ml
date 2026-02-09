(*
 * Genfiberus - Haxe to Fiberus C code generator
 *
 * Generates C code targeting the Fiberus fiber-based runtime.
 * Splits output into multiple files (one per class) for faster compilation.
 *)

open Globals
open Ast
open Type
open Gctx
open FiberusAst
open FiberusVtable
open FiberusStrings
open FiberusEscape
open FiberusBuiltins
open FiberusClosure
open FiberusGenClass
open FiberusGenEnum
open FiberusTypeUtils
open FiberusSourceWriter
open FiberusConvert

type ctx = {
	com : Gctx.t;
	buf : Buffer.t;
	mutable tabs : string;
	mutable current_ret_type : Type.t option;
	mutable current_class : tclass option;
	mutable class_id_counter : int;
	mutable class_ids : (path, int) Hashtbl.t;
	(* Stack tracking for source mapping *)
	debug_level : int;  (* 0=none, 1=trace, 2=line *)
	(* Closure support *)
	mutable closure_counter : int;
	mutable closures : tc_closure list;  (* Collected closures (C-AST) *)
	mutable in_fiber_spawn : bool;  (* True when generating a closure for Fiber.spawn *)
	mutable spawn_counter : int;  (* Counter for unique Fiber.spawn temp variable names *)
	(* GC root tracking: count of gc_push_temp_root calls in current function *)
	mutable gc_local_count : int;

	(* Escape analysis: set of variable IDs that can be stack-allocated *)
	mutable stack_alloc_vars : (int, tclass) Hashtbl.t;
	(* Fiber-escape analysis: variables needing mature allocation *)
	mutable fiber_mature_vars : (int, unit) Hashtbl.t;
	(* Vtable context for virtual method dispatch *)
	mutable vtable_ctx : FiberusVtable.vtable_context option;
	(* Method thunks: methods used as values, needing closure wrappers (C-AST pipeline).
	 * Shared across all conv_ctx invocations for a class; populated during convert_expr. *)
	mutable cast_method_thunks : (string, tc_method_thunk) Hashtbl.t;
}

(* Escape analysis functions (can_stack_alloc_class, analyze_escapes, 
   filter_void_args, extract_param_field_mapping) now imported from FiberusEscape *)

let spr ctx s =
	Buffer.add_string ctx.buf s

let print ctx =
	Printf.kprintf (fun s -> Buffer.add_string ctx.buf s)

let newline ctx =
	print ctx "\n%s" ctx.tabs

(* ===========================================================================
 * C-AST Pipeline Helpers
 * =========================================================================== *)

(* Create a conversion context from the genfiberus context *)
let make_conv_ctx ctx =
  {
    FiberusConvert.current_class = ctx.current_class;
    FiberusConvert.current_class_name = Option.map (fun c -> flat_path c.cl_path) ctx.current_class;
    FiberusConvert.vtable_ctx = ctx.vtable_ctx;
    FiberusConvert.current_ret_type = Option.map tc_type_of ctx.current_ret_type;
    FiberusConvert.gc_local_count = ctx.gc_local_count;
    FiberusConvert.loop_depth = 0;
    FiberusConvert.func_gc_root_count = -1;
    FiberusConvert.gc_frame_name = "_gc";
    FiberusConvert.gc_frame_slots = [];
    FiberusConvert.gc_frame_rooted_vars = Hashtbl.create 0;
    FiberusConvert.in_gc_frame = false;
    FiberusConvert.closure_counter = ctx.closure_counter;
    FiberusConvert.closures = [];
    FiberusConvert.in_fiber_spawn = ctx.in_fiber_spawn;
    FiberusConvert.spawn_counter = ctx.spawn_counter;
    FiberusConvert.fiber_mature_vars = ctx.fiber_mature_vars;
    FiberusConvert.stack_alloc_vars = ctx.stack_alloc_vars;
    FiberusConvert.method_thunks = ctx.cast_method_thunks;
    FiberusConvert.debug_level = ctx.debug_level;
    FiberusConvert.last_line = 0;
    FiberusConvert.has_stack_frame = false;
    FiberusConvert.temp_counter = 0;
  }

(* Sync closure state from conv_ctx back to genfiberus ctx, return collected closures *)
let sync_closures_from_conv ctx conv_ctx =
  ctx.closure_counter <- conv_ctx.FiberusConvert.closure_counter;
  ctx.spawn_counter <- conv_ctx.FiberusConvert.spawn_counter;
  FiberusConvert.get_closures conv_ctx

(* Get or assign a unique class ID *)
let get_class_id ctx path =
	try Hashtbl.find ctx.class_ids path
	with Not_found ->
		let id = ctx.class_id_counter in
		ctx.class_id_counter <- ctx.class_id_counter + 1;
		Hashtbl.add ctx.class_ids path id;
		id

(* Convert Haxe type to C type string - delegates to FiberusTypeUtils *)
let s_type _ctx t =
	tc_type_to_string (tc_type_of t)

(* Generate type declaration with name - handles function pointer syntax correctly
 * For function types: now just "FibClosure* name" since all functions are closures
 * For other types: "type name"
 *)
let s_type_with_name ctx t name =
	(* s_type already returns FibClosure* for TFun, so just use standard format *)
	Printf.sprintf "%s %s" (s_type ctx t) name

(* Generate a function declaration when the return type might be a function pointer
 * For normal return types: "ret func_name(args)"
 * For function pointer return types: now just "FibClosure* func_name(args)"
 * since all function values are FibClosure* in Fiberus.
 *)
let s_func_decl ctx ret_type func_name func_args =
	(* s_type returns FibClosure* for TFun, so use standard format *)
	Printf.sprintf "%s %s(%s)" (s_type ctx ret_type) func_name func_args

(* Check if type ends with '*' (is a pointer that needs GC marking) *)
let needs_gc_marking_tc = function
	| TCFibString | TCFibArray _ | TCFibClass _ | TCFibClosure 
	| TCFibObject | TCFibIntMap | TCFibStringMap 
	| TCFibInt64Map | TCFibObjectMap | TCFibBytesData -> true
	| TCPointer _ -> true
	(* Note: FibDynamic is NOT a pointer (struct), so excluded *)
	| _ -> false

(* ===========================================================================
 * Class / Function Generation (via C-AST pipeline)
 * =========================================================================== *)

(* Generate a static variable declaration *)
(* is_compile_time_constant now imported from FiberusGenClass *)

(* Check if a static field needs runtime initialization (non-constant initializer) *)
let needs_runtime_init cf =
	match cf.cf_kind, cf.cf_expr with
	| Var _, Some e when not (is_compile_time_constant e) ->
		(match e.eexpr with
		| TFunction _ -> false  (* Functions don't need runtime init *)
		| _ -> true)
	| _ -> false

(* Get list of static fields that need runtime initialization *)
let get_runtime_init_fields c =
	List.filter needs_runtime_init c.cl_ordered_statics

let gen_static_var_decl ctx c cf =
	let class_name = flat_path c.cl_path in
	let tc = tc_type_of cf.cf_type in
	let is_local_static = has_class_field_flag cf CfNoLookup in
	let init = match cf.cf_expr with
		| Some e when is_compile_time_constant e ->
			let conv_ctx = make_conv_ctx ctx in
			Some (FiberusConvert.convert_expr conv_ctx e)
		| _ ->
			(* Default zero-initialization for non-constant fields *)
			let zero = match tc with
				| TCInt32 -> "0" | TCFloat64 -> "0.0" | TCBool -> "false" | _ -> "NULL"
			in
			Some (mk_expr (TCERaw zero) tc)
	in
	TCDVar {
		vd_name = class_name ^ "_" ^ ident cf.cf_name;
		vd_type = tc;
		vd_init = init;
		vd_static = is_local_static;
		vd_const = false;
		vd_volatile = false;
	}

(* Generate a single class to its own .c file - returns the class implementation as string *)
let gen_class_impl ctx c =
	if has_class_flag c CExtern then "" else begin
		(* Set current class for super call resolution *)
		ctx.current_class <- Some c;
		let class_name = flat_path c.cl_path in
		let class_id = get_class_id ctx c.cl_path in

		(* Reset global counters for this class - ensures unique names per file *)
		FiberusConvert.reset_counters ();

		(* Clear C-AST method thunks table for this class *)
		Hashtbl.clear ctx.cast_method_thunks;

		(* Collect all declarations into a list *)
		let decls = ref [] in
		let add d = decls := d :: !decls in

		(* 1. Mark function — if there are GC pointer instance fields *)
		let gc_fields = List.filter (fun cf ->
			match cf.cf_kind with
			| Var _ when not (has_class_field_flag cf CfStatic) ->
				let type_tc = tc_type_of cf.cf_type in
				needs_gc_marking_tc type_tc
			| _ -> false
		) c.cl_ordered_fields in
		let has_mark_func = gc_fields <> [] in
		if has_mark_func then begin
			let body =
				[TCSRaw (Printf.sprintf "%s* this = (%s*)obj;" class_name class_name)]
				@ List.map (fun cf ->
					TCSRaw (Printf.sprintf "gc_mark_object(ctx, this->%s);" (ident cf.cf_name))
				) gc_fields
			in
			add (TCDFunc {
				fd_name = class_name ^ "_mark";
				fd_ret = TCVoid;
				fd_args = [
					{ fa_name = "obj"; fa_type = TCPointer (TCRaw "FibObject") };
					{ fa_name = "ctx"; fa_type = TCPointer (TCRaw "MarkContext") };
				];
				fd_body = body;
				fd_static = true;
				fd_inline = false;
				fd_attrs = [];
			})
		end;

		(* 2. Vtable array *)
		let vtable_methods = match ctx.vtable_ctx with
			| Some vctx -> FiberusVtable.get_vtable_methods vctx c
			| None -> []
		in
		let vtable_size = match vtable_methods with
			| [] -> 0
			| _ ->
				let max_slot = List.fold_left (fun acc (slot, _, _) -> max acc slot) 0 vtable_methods in
				max_slot + 1
		in
		if vtable_size > 0 then begin
			(* Build vtable entries, resolving implementation class for each method *)
			let entries = List.map (fun (slot, method_name, _cf) ->
				let rec find_impl c =
					if List.exists (fun cf2 -> cf2.cf_name = method_name && FiberusVtable.is_instance_method cf2) c.cl_ordered_fields then
						c
					else match c.cl_super with
						| Some (parent, _) -> find_impl parent
						| None -> c
				in
				let impl_class = find_impl c in
				let impl_class_name = flat_path impl_class.cl_path in
				{ ve_slot = slot;
				  ve_method_name = ident method_name;
				  ve_impl_name = impl_class_name ^ "_" ^ ident method_name }
			) vtable_methods in
			add (TCDVtable {
				vt_name = class_name ^ "_vtable";
				vt_size = vtable_size;
				vt_entries = entries;
			})
		end;

		(* 3. FibClass struct *)
		let tostring_func = FiberusGenClass.find_tostring_func c in
		add (TCDClassMeta {
			cm_name = s_type_path c.cl_path;
			cm_var_name = class_name;
			cm_class_id = class_id;
			cm_instance_size = Printf.sprintf "sizeof(%s)" class_name;
			cm_super = (match c.cl_super with Some (p, _) -> Some (flat_path p.cl_path) | None -> None);
			cm_mark_func = if has_mark_func then Some (class_name ^ "_mark") else None;
			cm_tostring_func = tostring_func;
			cm_vtable_name = if vtable_size > 0 then Some (class_name ^ "_vtable") else None;
			cm_vtable_size = vtable_size;
		});

		(* 4. Static variable declarations *)
		List.iter (fun cf ->
			match cf.cf_kind, cf.cf_expr with
			| Var _, None ->
				add (gen_static_var_decl ctx c cf)
			| Var _, Some { eexpr = TFunction _ } ->
				()
			| Var _, Some _ ->
				add (gen_static_var_decl ctx c cf)
			| _ -> ()
		) c.cl_ordered_statics;

		(* 5. Boot function for runtime static initialization *)
		let runtime_init_fields = get_runtime_init_fields c in
		if runtime_init_fields <> [] then begin
			let conv_ctx = make_conv_ctx ctx in
			conv_ctx.FiberusConvert.gc_local_count <- 0;
			let gc_ctx_stmt = TCSRaw "FIB_GC_CTX;" in
			let init_stmts = List.filter_map (fun cf ->
				match cf.cf_expr with
				| Some e ->
					let cexpr = FiberusConvert.convert_expr conv_ctx e in
					let lhs = mk_expr (TCERaw (class_name ^ "_" ^ ident cf.cf_name)) (tc_type_of cf.cf_type) in
					Some (TCSExpr (mk_expr (TCEAssign (lhs, cexpr)) (tc_type_of cf.cf_type)))
				| None -> None
			) runtime_init_fields in
			let gc_pop = if conv_ctx.FiberusConvert.gc_local_count > 0 then
				[TCSGCPop conv_ctx.FiberusConvert.gc_local_count]
			else [] in
			add (TCDFunc {
				fd_name = class_name ^ "___boot";
				fd_ret = TCVoid;
				fd_args = [];
				fd_body = [gc_ctx_stmt] @ init_stmts @ gc_pop;
				fd_static = false;
				fd_inline = false;
				fd_attrs = [];
			})
		end;

		(* 6. Constructor — inlined from gen_constructor *)
		(let conv_ctx = make_conv_ctx ctx in
		match FiberusConvert.convert_constructor conv_ctx c with
		| None -> ()
		| Some (init_func, new_func) ->
			add (TCDFunc init_func);
			add (TCDFunc new_func);
			let new_closures = sync_closures_from_conv ctx conv_ctx in
			ctx.closures <- new_closures @ ctx.closures);

		(* 7. Static methods — inlined from gen_function *)
		List.iter (fun cf ->
			match cf.cf_expr with
			| Some { eexpr = TFunction f } ->
				let conv_ctx = make_conv_ctx ctx in
				let func_def = FiberusConvert.convert_class_method conv_ctx cf.cf_name f true class_name in
				add (TCDFunc func_def);
				let new_closures = sync_closures_from_conv ctx conv_ctx in
				ctx.closures <- new_closures @ ctx.closures
			| _ -> ()
		) c.cl_ordered_statics;

		(* 8. Instance methods — inlined from gen_function *)
		List.iter (fun cf ->
			match cf.cf_expr with
			| Some { eexpr = TFunction f } ->
				let conv_ctx = make_conv_ctx ctx in
				let func_def = FiberusConvert.convert_class_method conv_ctx cf.cf_name f false class_name in
				add (TCDFunc func_def);
				let new_closures = sync_closures_from_conv ctx conv_ctx in
				ctx.closures <- new_closures @ ctx.closures
			| _ -> ()
		) c.cl_ordered_fields;

		(* Emit everything through a single SourceWriter *)
		let all_decls = List.rev !decls in
		let w = FiberusSourceWriter.create () in

		(* Closure/thunk forward declarations must come before main content *)
		let method_thunks = Hashtbl.fold (fun _name thunk acc -> thunk :: acc) ctx.cast_method_thunks [] in
		let has_closures = ctx.closures <> [] in
		let has_thunks = method_thunks <> [] in
		if has_closures then
			FiberusSourceWriter.write_closures_forward_decls w (List.rev ctx.closures);
		if has_thunks then
			FiberusSourceWriter.write_method_thunks_forward_decls w method_thunks;

		(* Main declarations *)
		List.iter (FiberusSourceWriter.write_decl w) all_decls;

		(* Closure/thunk implementations after main content *)
		if has_closures then
			FiberusSourceWriter.write_closures w (List.rev ctx.closures) ~debug_level:ctx.debug_level;
		if has_thunks then
			FiberusSourceWriter.write_method_thunks w method_thunks;
		ctx.closures <- [];

		(* Clear current class *)
		ctx.current_class <- None;

		FiberusSourceWriter.contents w
	end

let gen_enum_impl _ctx e =
	if has_enum_flag e EnExtern then "" else begin
		let info = build_enum_info e in
		let decls = gen_enum_decls info in
		(* Skip the first decl (TCDEnum struct def) — that goes in the header *)
		let impl_decls = List.filter (fun d -> match d with TCDEnum _ -> false | _ -> true) decls in
		let w = FiberusSourceWriter.create () in
		List.iter (FiberusSourceWriter.write_decl w) impl_decls;
		FiberusSourceWriter.contents w
	end

(* Generate the common header file *)
let gen_header ctx com =
	Buffer.clear ctx.buf;

	(* Header guard *)
	spr ctx "#ifndef FIBERUS_GENERATED_H\n";
	spr ctx "#define FIBERUS_GENERATED_H\n\n";

	(* Feature test macros - must come before includes *)
	spr ctx "#define _DEFAULT_SOURCE\n\n";

	(* Includes *)
	spr ctx "#include <stdint.h>\n";
	spr ctx "#include <stdbool.h>\n";
	spr ctx "#include <stdio.h>\n";
	spr ctx "#include <stdlib.h>\n";
	spr ctx "#include <string.h>\n";
	spr ctx "#include <setjmp.h>\n";
	spr ctx "#include <unistd.h>\n";
	spr ctx "#include <math.h>\n";
	spr ctx "#include \"fiber.h\"\n";
	spr ctx "#include \"scheduler.h\"\n";
	spr ctx "#include \"object.h\"\n";
	spr ctx "#include \"fibstring.h\"\n";
	spr ctx "#include \"array.h\"\n";
	spr ctx "#include \"bytes.h\"\n";
	spr ctx "#include \"hashmap.h\"\n";
	spr ctx "#include \"gc/gc.h\"\n";
	spr ctx "#include \"stack_macros.h\"\n";
	spr ctx "#include \"closure.h\"\n";
	spr ctx "#include \"scheduler.h\"\n";
	spr ctx "#include \"counter.h\"\n";
	spr ctx "#include \"iouring.h\"\n";
	spr ctx "#include \"date.h\"\n";
	spr ctx "\n";

	(* Runtime API headers - extracted from inline C to proper .h files *)
	spr ctx "#include \"anon.h\"\n";
	spr ctx "#include \"exception.h\"\n";
	spr ctx "#include \"fiber_api.h\"\n";
	spr ctx "#include \"gc_api.h\"\n";
	spr ctx "\n";

	(* Generate forward declarations for all classes - including extern ones *)
	spr ctx "/* Forward declarations */\n";
	List.iter (function
		| TClassDecl c ->
			(* Forward declare all classes, extern or not *)
			print ctx "typedef struct %s %s;" (flat_path c.cl_path) (flat_path c.cl_path);
			newline ctx;
			(* Only non-extern classes have FibClass metadata *)
			if not (has_class_flag c CExtern) then begin
				print ctx "extern FibClass %s_class;" (flat_path c.cl_path);
				newline ctx
			end
		| TEnumDecl e ->
			(* Forward declare all enums *)
			print ctx "typedef struct { int index; FibDynamic params[8]; } %s;" (flat_path e.e_path);
			newline ctx
		| _ -> ()
	) com.types;
	newline ctx;

	(* Generate full struct definitions - needed for inheritance embedding *)
	spr ctx "/* Struct definitions */\n";
	List.iter (function
		| TClassDecl c when not (has_class_flag c CExtern) ->
			let class_name = flat_path c.cl_path in
			print ctx "struct %s {" class_name;
			newline ctx;
			ctx.tabs <- "\t";
			(* Embed parent struct or FibObject at start *)
			(match c.cl_super with
			| Some (parent_c, _) ->
				print ctx "%s _parent;  /* Embedded parent */" (flat_path parent_c.cl_path)
			| None ->
				spr ctx "FibObject _obj;  /* Must be first */");
			newline ctx;
			(* Instance fields - only this class's own fields, not inherited *)
			List.iter (fun cf ->
				match cf.cf_kind with
				| Var _ ->
					print ctx "%s;" (s_type_with_name ctx cf.cf_type (ident cf.cf_name));
					newline ctx
				| Method MethDynamic ->
					(* Dynamic functions are stored as function pointers *)
					print ctx "void* %s;  /* dynamic function */" (ident cf.cf_name);
					newline ctx
				| _ -> ()
			) c.cl_ordered_fields;
			ctx.tabs <- "";
			spr ctx "};";
			newline ctx;
			newline ctx
		| _ -> ()
	) com.types;

	(* Generate extern declarations for class static variables (not local statics) *)
	spr ctx "/* Static variable extern declarations */\n";
	List.iter (function
		| TClassDecl c when not (has_class_flag c CExtern) ->
			let class_name = flat_path c.cl_path in
			List.iter (fun cf ->
				match cf.cf_kind, cf.cf_expr with
				| Var _, None when not (has_class_field_flag cf CfNoLookup) ->
					(* Regular class static variable - extern declaration *)
					let full_name = class_name ^ "_" ^ (ident cf.cf_name) in
					print ctx "extern %s;" (s_type_with_name ctx cf.cf_type full_name);
					newline ctx
				| Var _, Some { eexpr = TFunction _ } ->
					(* This is a function, skip *)
					()
				| Var _, Some _ when not (has_class_field_flag cf CfNoLookup) ->
					(* Regular class static variable with initializer - extern declaration *)
					let full_name = class_name ^ "_" ^ (ident cf.cf_name) in
					print ctx "extern %s;" (s_type_with_name ctx cf.cf_type full_name);
					newline ctx
				| _ -> ()
			) c.cl_ordered_statics
		| _ -> ()
	) com.types;
	newline ctx;

	(* Generate function forward declarations *)
	spr ctx "/* Function forward declarations */\n";
	List.iter (function
		| TClassDecl c when not (has_class_flag c CExtern) ->
			let class_name = flat_path c.cl_path in
			(* Constructor _init and _new *)
			let class_tc = TCFibClass class_name in
			let this_arg = { fa_name = "this"; fa_type = class_tc } in
			(match c.cl_constructor with
			| None ->
				(* No constructor: generate trivial inline _init and _new *)
				let init_func = { fd_name = class_name ^ "_init"; fd_ret = TCVoid;
					fd_args = [this_arg]; fd_body = [TCSRaw "(void)this;"];
					fd_static = true; fd_inline = true; fd_attrs = [] } in
				let new_body = [
					TCSRaw (Printf.sprintf "%s* this = gc_alloc_object_with_class(sizeof(%s), &%s_class);"
						class_name class_name class_name);
					TCSReturn (Some (mk_expr (TCELocal "this") class_tc));
				] in
				let new_func = { fd_name = class_name ^ "_new"; fd_ret = class_tc;
					fd_args = []; fd_body = new_body;
					fd_static = true; fd_inline = true; fd_attrs = [] } in
				let w = FiberusSourceWriter.create () in
				FiberusSourceWriter.write_decl w (TCDFunc init_func);
				FiberusSourceWriter.write_decl w (TCDFunc new_func);
				spr ctx (FiberusSourceWriter.contents w)
			| Some cf ->
				(match cf.cf_expr with
				| Some { eexpr = TFunction f } ->
					let filtered_args = filter_void_args f.tf_args in
					let is_simple = is_simple_constructor f in
					if is_simple then begin
						let conv_ctx = make_conv_ctx ctx in
						(* Build _init args: this + constructor params *)
						let ctor_args = List.map (fun (v, _) ->
							{ fa_name = ident v.v_name; fa_type = tc_type_of v.v_type }
						) filtered_args in
						(* Build init body: field assignments from constructor *)
						let init_body = ref [] in
						let extract_assigns e =
							match e.eexpr with
							| TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf2)) }, value)
							| TParenthesis { eexpr = TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf2)) }, value) } ->
								let cval = FiberusConvert.convert_expr conv_ctx value in
								let lhs = mk_expr (TCEArrow (mk_expr (TCELocal "this") class_tc, ident cf2.cf_name)) cval.ctype in
								init_body := TCSExpr (mk_expr (TCEAssign (lhs, cval)) cval.ctype) :: !init_body
							| _ -> ()
						in
						(match f.tf_expr.eexpr with
						| TBlock el -> List.iter extract_assigns el
						| _ -> extract_assigns f.tf_expr);
						let init_func = { fd_name = class_name ^ "_init"; fd_ret = TCVoid;
							fd_args = this_arg :: ctor_args; fd_body = List.rev !init_body;
							fd_static = true; fd_inline = true; fd_attrs = [] } in
						(* Build _new: alloc + init + return *)
						let arg_names = List.map (fun (v, _) -> ident v.v_name) filtered_args in
						let arg_refs = List.map (fun n -> mk_expr (TCELocal n) TCVoid) arg_names in
						let new_body = [
							TCSRaw (Printf.sprintf "%s* this = gc_alloc_object_with_class(sizeof(%s), &%s_class);"
								class_name class_name class_name);
							TCSExpr (mk_expr (TCECall (TCTFunc (class_name ^ "_init"),
								mk_expr (TCELocal "this") class_tc :: arg_refs)) TCVoid);
							TCSReturn (Some (mk_expr (TCELocal "this") class_tc));
						] in
						let new_func = { fd_name = class_name ^ "_new"; fd_ret = class_tc;
							fd_args = ctor_args; fd_body = new_body;
							fd_static = true; fd_inline = true; fd_attrs = [] } in
						let w = FiberusSourceWriter.create () in
						FiberusSourceWriter.write_decl w (TCDFunc init_func);
						FiberusSourceWriter.write_decl w (TCDFunc new_func);
						spr ctx (FiberusSourceWriter.contents w)
					end else begin
						(* Non-simple: just forward declarations *)
						let ctor_args = List.map (fun (v, _) ->
							{ fa_name = ident v.v_name; fa_type = tc_type_of v.v_type }
						) filtered_args in
						let arg_types = List.map (fun a -> a.fa_type) ctor_args in
						let w = FiberusSourceWriter.create () in
						FiberusSourceWriter.write_decl w (TCDForwardFunc {
							fs_name = class_name ^ "_init"; fs_ret = TCVoid;
							fs_args = class_tc :: arg_types });
						FiberusSourceWriter.write_decl w (TCDForwardFunc {
							fs_name = class_name ^ "_new"; fs_ret = class_tc;
							fs_args = arg_types });
						spr ctx (FiberusSourceWriter.contents w)
					end
				| _ -> ()));
			(* __boot function for static initialization *)
			let runtime_init_fields = get_runtime_init_fields c in
			if runtime_init_fields <> [] then begin
				print ctx "void %s___boot(void);" class_name;
				newline ctx
			end;
			(* Static methods *)
			List.iter (fun cf ->
				match cf.cf_expr with
				| Some { eexpr = TFunction f } ->
					let filtered_args = filter_void_args f.tf_args in
					let args = List.map (fun (v, _) ->
						s_type_with_name ctx v.v_type (ident v.v_name)
					) filtered_args in
					let args_str = if args = [] then "void" else String.concat ", " args in
					let func_name = Printf.sprintf "%s_%s" (flat_path c.cl_path) cf.cf_name in
					spr ctx (s_func_decl ctx f.tf_type func_name args_str);
					spr ctx ";";
					newline ctx
				| _ -> ()
			) c.cl_ordered_statics;
			(* Instance methods *)
			List.iter (fun cf ->
				match cf.cf_expr with
				| Some { eexpr = TFunction f } ->
					let filtered_args = filter_void_args f.tf_args in
					let args = List.map (fun (v, _) ->
						s_type_with_name ctx v.v_type (ident v.v_name)
					) filtered_args in
					let this_arg = Printf.sprintf "%s* this" (flat_path c.cl_path) in
					let args_str = if args = [] then this_arg else this_arg ^ ", " ^ String.concat ", " args in
					let func_name = Printf.sprintf "%s_%s" (flat_path c.cl_path) cf.cf_name in
					spr ctx (s_func_decl ctx f.tf_type func_name args_str);
					spr ctx ";";
					newline ctx
				| _ -> ()
			) c.cl_ordered_fields
		| TEnumDecl e when not (has_enum_flag e EnExtern) ->
			(* Enum constructor declarations *)
			PMap.iter (fun name ef ->
				match ef.ef_type with
				| TFun (args, _) ->
					(* Filter out void-typed enum constructor parameters *)
					let filtered_args = List.filter (fun (_, _, t) -> not (is_void_type t)) args in
					print ctx "%s %s_%s(" (flat_path e.e_path) (flat_path e.e_path) name;
					let args_str = String.concat ", " (List.map (fun (n, _, t) ->
						s_type_with_name ctx t (ident n)
					) filtered_args) in
					if args_str = "" then spr ctx "void" else spr ctx args_str;
					spr ctx ");";
					newline ctx
				| _ ->
					print ctx "extern const %s %s_%s;" (flat_path e.e_path) (flat_path e.e_path) name;
					newline ctx
			) e.e_constrs
		| _ -> ()
	) com.types;
	newline ctx;

	spr ctx "#endif /* FIBERUS_GENERATED_H */\n";

	Buffer.contents ctx.buf

(* Generate the runtime globals file *)
(* gc_roots is a list of (class_name, field_name, c_type) for static fields needing GC root registration *)
let gen_runtime_globals gc_roots =
	let buf = Buffer.create 1024 in
	Buffer.add_string buf "/* Runtime globals */\n";
	Buffer.add_string buf "#include \"fiberus_generated.h\"\n\n";
	Buffer.add_string buf "/* Exception handling - thread-local fallback stack and current exception */\n";
	Buffer.add_string buf "__thread jmp_buf* _fib_tls_exc_stack[FIB_TLS_EXC_STACK_SIZE];\n";
	Buffer.add_string buf "__thread int _fib_tls_exc_stack_top = 0;\n";
	Buffer.add_string buf "__thread FibDynamic _fib_current_exception = {0};\n\n";
	Buffer.add_string buf "void fib_throw(FibDynamic exc) {\n";
	Buffer.add_string buf "\t_fib_current_exception = exc;\n";
	Buffer.add_string buf "\tFiber* f = fiber_current();\n";
	Buffer.add_string buf "\tif (f && f->exc_stack_top > 0) {\n";
	Buffer.add_string buf "\t\tlongjmp(*(jmp_buf*)f->exc_stack[--f->exc_stack_top], 1);\n";
	Buffer.add_string buf "\t} else if (_fib_tls_exc_stack_top > 0) {\n";
	Buffer.add_string buf "\t\t/* Fallback to thread-local stack when no fiber context */\n";
	Buffer.add_string buf "\t\tlongjmp(*_fib_tls_exc_stack[--_fib_tls_exc_stack_top], 1);\n";
	Buffer.add_string buf "\t} else {\n";
	Buffer.add_string buf "\t\tfprintf(stderr, \"Uncaught exception\\n\");\n";
	Buffer.add_string buf "\t\texit(1);\n";
	Buffer.add_string buf "\t}\n";
	Buffer.add_string buf "}\n\n";
	Buffer.add_string buf "/* haxe.Exception implementation */\n";
	Buffer.add_string buf "FibClass haxe_Exception_class = {\n";
	Buffer.add_string buf "\t.name = \"haxe.Exception\",\n";
	Buffer.add_string buf "\t.classId = 9999,\n";
	Buffer.add_string buf "\t.instanceSize = sizeof(haxe_Exception),\n";
	Buffer.add_string buf "\t.super = NULL,\n";
	Buffer.add_string buf "\t.markFunc = NULL,\n";
	Buffer.add_string buf "\t.construct = NULL,\n";
	Buffer.add_string buf "\t.destruct = NULL,\n";
	Buffer.add_string buf "};\n\n";
	Buffer.add_string buf "void haxe_Exception_init(haxe_Exception* this, FibString* message, haxe_Exception* previous, FibDynamic native) {\n";
	Buffer.add_string buf "\t(void)previous; (void)native;\n";
	Buffer.add_string buf "\t/* clazz already set by gc_alloc_object_with_class */\n";
	Buffer.add_string buf "\tthis->message = message ? message : fib_string_new(\"Exception\");\n";
	Buffer.add_string buf "}\n\n";
	Buffer.add_string buf "haxe_Exception* haxe_Exception_new(FibString* message, haxe_Exception* previous, FibDynamic native) {\n";
	Buffer.add_string buf "\thaxe_Exception* this = gc_alloc_object_with_class(sizeof(haxe_Exception), &haxe_Exception_class);\n";
	Buffer.add_string buf "\thaxe_Exception_init(this, message, previous, native);\n";
	Buffer.add_string buf "\treturn this;\n";
	Buffer.add_string buf "}\n\n";
	(* Generate GC root registration function *)
	Buffer.add_string buf "/* GC root registration for static fields */\n";
	Buffer.add_string buf "void fiberus_register_gc_roots(void) {\n";
	List.iter (fun (class_name, field_name, c_type) ->
		(* For pointer types, register the address directly *)
		(* For FibDynamic types, we need to register the address of the value *)
		if String.length c_type > 0 && c_type.[String.length c_type - 1] = '*' then
			Buffer.add_string buf (Printf.sprintf "\tgc_add_root((void**)&%s_%s);\n" class_name field_name)
		else if c_type = "FibDynamic" then
			(* FibDynamic contains a union with pointer, register address of the whole value *)
			Buffer.add_string buf (Printf.sprintf "\tgc_add_root((void**)&%s_%s);\n" class_name field_name)
	) gc_roots;
	Buffer.add_string buf "}\n";
	Buffer.contents buf

let generate com =
	(* Determine debug level for stack tracking:
	   0 = no stack tracking
	   1 = function-level stack trace (FIBERUS_STACK_TRACE)
	   2 = line-level tracking (FIBERUS_STACK_LINE) *)
	let tracy_enabled = Gctx.raw_defined com "FIBERUS_TRACY" in
	let debug_level =
		if Gctx.defined com Define.Debug then 2
		else if com.debug then 1
		else if tracy_enabled then 1  (* Enable stack frames for Tracy zones *)
		else 0
	in
	let ctx = {
		com = com;
		buf = Buffer.create 16000;
		tabs = "";
		current_ret_type = None;
		current_class = None;
		class_id_counter = 100;  (* Start at 100 to reserve 0-99 for built-in classes *)
		class_ids = Hashtbl.create 0;
		debug_level = debug_level;
		closure_counter = 0;
		closures = [];
		in_fiber_spawn = false;
		spawn_counter = 0;
		gc_local_count = 0;
		stack_alloc_vars = Hashtbl.create 0;
		fiber_mature_vars = Hashtbl.create 0;
		vtable_ctx = None;
		cast_method_thunks = Hashtbl.create 16;
	} in

	(* Build vtables for all classes - enables virtual method dispatch *)
	ctx.vtable_ctx <- Some (FiberusVtable.build_all_vtables com.types);

	(* Create output directory and src subdirectory *)
	let dir = com.file in
	let src_dir = dir ^ "/src" in
	Path.mkdir_recursive "" (Str.split_delim (Str.regexp "[\\/]+") src_dir);

	(* Track generated files for Build.xml *)
	let generated_files = ref [] in

	(* Collect GC roots from all classes (static fields that can hold object references) *)
	let gc_roots = ref [] in
	List.iter (function
		| TClassDecl c when not (has_class_flag c CExtern) ->
			let class_name = flat_path c.cl_path in
			List.iter (fun cf ->
				match cf.cf_kind with
				| Var _ when not (has_class_field_flag cf CfNoLookup) ->
					(* Regular class static variable - check if it needs GC root *)
					if haxe_type_needs_gc_root cf.cf_type then begin
						let c_type = s_type ctx cf.cf_type in
						gc_roots := (class_name, ident cf.cf_name, c_type) :: !gc_roots
					end
				| _ -> ()
			) c.cl_ordered_statics
		| _ -> ()
	) com.types;

	(* Generate header file *)
	let header_content = gen_header ctx com in
	let header_file = src_dir ^ "/fiberus_generated.h" in
	let ch = open_out_bin header_file in
	output_string ch header_content;
	close_out ch;

	(* Generate runtime globals file with GC root registration *)
	let globals_content = gen_runtime_globals !gc_roots in
	let globals_file = src_dir ^ "/fiberus_globals.c" in
	let ch = open_out_bin globals_file in
	output_string ch globals_content;
	close_out ch;
	generated_files := "fiberus_globals.c" :: !generated_files;

	(* Generate one .c file per class *)
	List.iter (function
		| TClassDecl c when not (has_class_flag c CExtern) ->
			let class_name = flat_path c.cl_path in
			let impl = gen_class_impl ctx c in
			if impl <> "" then begin
				let filename = class_name ^ ".c" in
				let file_content = Printf.sprintf "/* Class: %s */\n#include \"fiberus_generated.h\"\n\n%s"
					(s_type_path c.cl_path) impl in
				let ch = open_out_bin (src_dir ^ "/" ^ filename) in
				output_string ch file_content;
				close_out ch;
				generated_files := filename :: !generated_files
			end
		| TEnumDecl e when not (has_enum_flag e EnExtern) ->
			let enum_name = flat_path e.e_path in
			let impl = gen_enum_impl ctx e in
			if impl <> "" then begin
				let filename = enum_name ^ ".c" in
				let file_content = Printf.sprintf "/* Enum: %s */\n#include \"fiberus_generated.h\"\n\n%s"
					(s_type_path e.e_path) impl in
				let ch = open_out_bin (src_dir ^ "/" ^ filename) in
				output_string ch file_content;
				close_out ch;
				generated_files := filename :: !generated_files
			end
		| _ -> ()
	) com.types;

	(* Collect classes that need boot functions *)
	let boot_classes = List.filter_map (function
		| TClassDecl c when not (has_class_flag c CExtern) ->
			let runtime_init_fields = get_runtime_init_fields c in
			if runtime_init_fields <> [] then Some (flat_path c.cl_path)
			else None
		| _ -> None
	) com.types in

	(* Generate Main.c with main function *)
	Buffer.clear ctx.buf;
	spr ctx "/* Entry point */\n";
	spr ctx "#include \"fiberus_generated.h\"\n";
	spr ctx "#include \"telemetry.h\"\n\n";

	(* Generate the main fiber entry function via C-AST pipeline *)
	let main_body = match com.main.main_expr with
		| Some e ->
			let conv_ctx = make_conv_ctx ctx in
			let stmts = FiberusConvert.convert_stmt conv_ctx e in
			(* Sync closures back *)
			let new_closures = sync_closures_from_conv ctx conv_ctx in
			if new_closures <> [] then ctx.closures <- new_closures @ ctx.closures;
			[TCSRaw "(void)arg;"] @ stmts
		| None ->
			[TCSRaw "(void)arg;"; TCSComment "No main expression"]
	in
	let main_entry_func = {
		fd_name = "_fiberus_main_entry";
		fd_ret = TCVoid;
		fd_args = [{ fa_name = "arg"; fa_type = TCPointer TCVoid }];
		fd_body = main_body;
		fd_static = true;
		fd_inline = false;
		fd_attrs = [];
	} in
	let w = FiberusSourceWriter.create () in
	FiberusSourceWriter.write_decl w (TCDRaw "/* Main fiber entry - runs the Haxe main code as a fiber.\n * This allows the main thread to participate in work-stealing\n * and provides a uniform execution model where all code runs in fibers. */");
	FiberusSourceWriter.write_decl w (TCDFunc main_entry_func);
	spr ctx (FiberusSourceWriter.contents w);

	spr ctx "int main(int argc, char** argv) {\n";
	spr ctx "\t(void)argc; (void)argv;\n";
	spr ctx "\tvolatile int _gc_stack_base_marker;\n\n";
	spr ctx "\t/* 1. Initialize GC (data structures only, no allocation yet) */\n";
	spr ctx "\tgc_init();\n\n";
	spr ctx "\t/* 2. Initialize scheduler (creates ThreadBlockCache + FiberGCContext for main)\n";
	spr ctx "\t *    Main thread becomes fiber 0 with proper context */\n";
	spr ctx "\tscheduler_init((void*)&_gc_stack_base_marker);\n\n";
	spr ctx "\t/* 3. Register permanent GC roots (static fields) */\n";
	spr ctx "\tfiberus_register_gc_roots();\n\n";
	(* Call boot functions to initialize static fields - must happen after scheduler_init *)
	if boot_classes <> [] then begin
		spr ctx "\t/* 4. Boot all classes (static field initialization)\n";
		spr ctx "\t *    Now safe to allocate - we have ThreadBlockCache and FiberGCContext */\n";
		List.iter (fun class_name ->
			print ctx "\t%s___boot();\n" class_name
		) boot_classes;
		spr ctx "\n"
	end;
	(* Spawn main as a fiber on thread 0 (main thread's queue) *)
	spr ctx "\t/* 5. Spawn main code as fiber on thread 0 (main thread's queue) */\n";
	spr ctx "\tscheduler_spawn(_fiberus_main_entry, NULL);\n\n";
	(* Tracy zone wraps scheduler_run which includes main fiber execution *)
	spr ctx "#ifdef FIBERUS_TRACY\n";
	spr ctx "\tTracyCZoneN(_main_zone, \"main\", 1);\n";
	spr ctx "#endif\n\n";
	spr ctx "\t/* 6. Run fibers until all complete (main thread participates in work-stealing) */\n";
	spr ctx "\tscheduler_run();\n\n";
	spr ctx "#ifdef FIBERUS_TRACY\n";
	spr ctx "\tTracyCZoneEnd(_main_zone);\n";
	spr ctx "#endif\n\n";
	spr ctx "\t/* 7. Cleanup */\n";
	spr ctx "\tscheduler_shutdown();\n";
	spr ctx "\tgc_shutdown();\n";
	spr ctx "\treturn 0;\n";
	spr ctx "}\n";

	let main_file = src_dir ^ "/fiberus_entry.c" in
	let ch = open_out_bin main_file in
	output_string ch (Buffer.contents ctx.buf);
	close_out ch;
	generated_files := "fiberus_entry.c" :: !generated_files;

	(* Check for Tracy profiler defines *)
	let tracy_enabled = Gctx.raw_defined com "FIBERUS_TRACY" in
	let tracy_no_exit = Gctx.raw_defined com "TRACY_NO_EXIT" in
	let tracy_on_demand = Gctx.raw_defined com "TRACY_ON_DEMAND" in
	(* Check for io_uring define *)
	let iouring_enabled = Gctx.raw_defined com "iouring" in

	(* Generate Build.xml *)
	let build_xml = Buffer.create 1024 in
	Buffer.add_string build_xml "<xml>\n";
	Buffer.add_string build_xml "<!-- Generated by Haxe Fiberus target -->\n\n";
	Buffer.add_string build_xml "<set name=\"FIBERUS\" value=\"${haxelib:fiberus}\" unless=\"FIBERUS\" />\n";
	if tracy_enabled then
		Buffer.add_string build_xml "<set name=\"FIBERUS_TRACY\" value=\"1\" />\n";
	if tracy_no_exit then
		Buffer.add_string build_xml "<set name=\"TRACY_NO_EXIT\" value=\"1\" />\n";
	if tracy_on_demand then
		Buffer.add_string build_xml "<set name=\"TRACY_ON_DEMAND\" value=\"1\" />\n";
	if iouring_enabled then
		Buffer.add_string build_xml "<set name=\"iouring\" value=\"1\" />\n";
	Buffer.add_string build_xml "<include name=\"${FIBERUS}/build-tool/BuildCommon.xml\"/>\n\n";
	Buffer.add_string build_xml "<!-- Generated Haxe code -->\n";
	Buffer.add_string build_xml "<files id=\"haxe\" dir=\"src\" tags=\"fiberus\">\n";
	(* Add Options.txt as a dependency for proper cache invalidation *)
	Buffer.add_string build_xml "  <options name=\"Options.txt\"/>\n";
	List.iter (fun filename ->
		Buffer.add_string build_xml (Printf.sprintf "  <file name=\"%s\"/>\n" filename)
	) (List.rev !generated_files);
	Buffer.add_string build_xml "</files>\n\n";
	Buffer.add_string build_xml "<!-- Build executable -->\n";
	Buffer.add_string build_xml "<target id=\"default\" output=\"Main\" tool=\"linker\" toolid=\"exe\">\n";
	Buffer.add_string build_xml "  <files id=\"haxe\"/>\n";
	Buffer.add_string build_xml "  <files id=\"runtime\"/>\n";
	Buffer.add_string build_xml "  <files id=\"gc\"/>\n";
	Buffer.add_string build_xml "  <files id=\"simdutf\"/>\n";
	if tracy_enabled then
		Buffer.add_string build_xml "  <files id=\"tracy\"/>\n";
	Buffer.add_string build_xml "  <lib name=\"-lpthread\" if=\"linux\"/>\n";
	Buffer.add_string build_xml "  <lib name=\"-ldl\" if=\"linux\"/>\n";
	if iouring_enabled then
		Buffer.add_string build_xml "  <lib name=\"-luring\" if=\"linux\"/>\n";
	Buffer.add_string build_xml "  <outdir name=\"./\"/>\n";
	Buffer.add_string build_xml "</target>\n\n";
	Buffer.add_string build_xml "</xml>\n";

	let build_file = dir ^ "/Build.xml" in
	let bch = open_out_bin build_file in
	output_string bch (Buffer.contents build_xml);
	close_out bch;

	(* Escape function for command-line and options file values *)
	let escape_command s =
		let b = Buffer.create 0 in
		String.iter (fun ch ->
			if ch == '"' || ch == '\\' then Buffer.add_string b "\\";
			Buffer.add_char b ch
		) s;
		Buffer.contents b
	in

	(* Write Options.txt for build dependency tracking *)
	let options_file = dir ^ "/Options.txt" in
	let och = open_out_bin options_file in
	PMap.iter (fun name value ->
		match name with
		| "true" | "sys" | "dce" | "fiberus" | "debug" -> ()
		| _ -> output_string och (Printf.sprintf "%s=%s\n" name (escape_command value))
	) com.defines.Define.values;
	(* Add fiberus path to Options.txt (like hxcpp does) *)
	let pin, pid = Process_helper.open_process_args_in_pid "haxelib" [|"haxelib"; "path"; "fiberus"|] in
	set_binary_mode_in pin false;
	(try
		output_string och (Printf.sprintf "fiberus=%s\n" (Stdlib.input_line pin))
	with _ -> ());
	ignore (Process_helper.close_process_in_pid (pin, pid));
	close_out och;

	com.print (Printf.sprintf "Generated %d source files\n" (List.length !generated_files));

	(* Run fiberus build tool unless -D no-compilation *)
	if not (Gctx.defined com Define.NoCompilation) then begin
		let old_dir = Sys.getcwd () in
		Sys.chdir dir;
		let cmd = ref ["run"; "fiberus"; "Build.xml"] in
		if com.debug then cmd := !cmd @ ["-Ddebug"];
		(* Forward all defines to the build tool (matching gencpp.ml behavior) *)
		PMap.iter (fun name value -> match name with
			| "true" | "sys" | "dce" | "fiberus" | "debug" -> ()
			| _ -> cmd := !cmd @ [Printf.sprintf "-D%s=\"%s\"" name (escape_command value)]
		) com.defines.Define.values;
		(* Forward class paths to the build tool *)
		com.class_paths#iter (fun path ->
			let path = path#path in
			cmd := !cmd @ [Printf.sprintf "-I%s" (escape_command path)]
		);
		com.print ("haxelib " ^ (String.concat " " !cmd) ^ "\n");
		if com.run_command_args "haxelib" !cmd <> 0 then failwith "Build failed";
		Sys.chdir old_dir
	end
