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

(* Check if a class is an abstract impl that wraps a class type (should be skipped).
   Abstract impls for value types like XmlType_Impl_ (wrapping Int) are kept,
   since they contain real static methods needed at runtime. *)
let is_skippable_abstract_impl c = match c.cl_kind with
  | KAbstractImpl a ->
    (match Type.follow a.a_this with
     | TInst _ ->
       (* Even for TInst-backed abstracts, we must NOT skip if there are
          static variables or static methods with expressions that survived DCE.
          These need extern declarations and definitions in the generated C code. *)
       not (List.exists (fun cf ->
         match cf.cf_kind with
         | Var _ when cf.cf_expr <> None -> true
         | Method _ when cf.cf_expr <> None -> true
         | _ -> false
       ) c.cl_ordered_statics)
     | _ -> false)
  | _ -> false

(* Extract default value C literals from tf_args for thunk null-substitution.
   Returns a list of string option, one per arg after filter_void_args.
   Only non-null primitive defaults produce Some "literal". *)
let extract_thunk_defaults filtered_args =
  List.map (fun (_, default_opt) ->
    match default_opt with
    | Some { Type.eexpr = Type.TConst c } -> begin match c with
        | Type.TInt i -> Some (Int32.to_string i)
        | Type.TFloat s -> Some s
        | Type.TBool true -> Some "true"
        | Type.TBool false -> Some "false"
        | _ -> None
      end
    | _ -> None
  ) filtered_args

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
    FiberusConvert.try_depth = 0;
    FiberusConvert.try_depth_at_loop = 0;
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
    FiberusConvert.var_type_overrides = Hashtbl.create 0;
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
	| Var _, Some e when is_compile_time_constant e ->
		(* Even compile-time constants need runtime init if the field type is
		   FibDynamic (Null<T>) but the value is a scalar — requires boxing *)
		let tc = tc_type_of cf.cf_type in
		tc = TCFibDynamic
	| _ -> false

(* Get list of static fields that need runtime initialization *)
let get_runtime_init_fields c =
	List.filter needs_runtime_init c.cl_ordered_statics

let gen_static_var_decl ctx c cf =
	let class_name = flat_path c.cl_path in
	let tc = tc_type_of cf.cf_type in
	let is_local_static = has_class_field_flag cf CfNoLookup in
	let init = match cf.cf_expr with
		| Some e when is_compile_time_constant e && tc <> TCFibDynamic ->
			let conv_ctx = make_conv_ctx ctx in
			Some (FiberusConvert.convert_expr conv_ctx e)
		| _ ->
			(* Default zero-initialization for non-constant fields *)
			(* Must use file-scope-valid initializers — no function calls *)
			let zero = match tc with
				| TCInt32 -> "0"
				| TCFloat64 -> "0.0"
				| TCBool -> "false"
				| TCFibDynamic -> "(FibDynamic){0}"
				| TCFibEnum name -> Printf.sprintf "(%s){ ._meta = NULL, .index = -1 }" name
				| _ -> "NULL"
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
			| Method MethDynamic when not (has_class_field_flag cf CfStatic) ->
				(* Dynamic methods store FibClosure* in void* fields — they need GC marking *)
				true
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

		(* 2. Vtable array — skip for interfaces (they have no method implementations) *)
		let vtable_methods = match ctx.vtable_ctx with
			| Some vctx when not (has_class_flag c CInterface) -> FiberusVtable.get_vtable_methods vctx c
			| _ -> []
		in
		let vtable_size = match vtable_methods with
			| [] -> 0
			| _ ->
				let max_slot = List.fold_left (fun acc (slot, _, _) -> max acc slot) 0 vtable_methods in
				max_slot + 1
		in
		let ivtable_name_ref = ref None in
		if vtable_size > 0 then begin
			(* Build vtable entries, resolving implementation class for each method.
			   For @:generic monomorphized classes that override parent methods, the
			   child's concrete function signature may differ from the parent's erased
			   calling convention (e.g. FibIntArray* vs FibDynamic). In such cases we
			   generate a vtable bridge thunk that converts between calling conventions. *)
			let bridge_decls = ref [] in
			let bridge_seen = Hashtbl.create 4 in
			let entries = List.map (fun (slot, method_name, _cf) ->
				let rec find_impl c =
					if List.exists (fun cf2 -> cf2.cf_name = method_name && FiberusVtable.is_instance_method cf2
						&& not (has_class_field_flag cf2 CfAbstract)) c.cl_ordered_fields then
						Some c
					else match c.cl_super with
						| Some (parent, _) -> find_impl parent
						| None -> None
				in
				match find_impl c with
				| Some impl_class ->
					let impl_class_name = flat_path impl_class.cl_path in
					let impl_func_name = impl_class_name ^ "_" ^ ident method_name in
				(* Check if a vtable bridge thunk is needed: compare the defining
				   class's erased method types with the implementation's concrete types *)
				let defining_class = find_defining_class c method_name in
				let bridge_needed =
					if defining_class.cl_path = impl_class.cl_path then false
					else
						(* Get defining class's method signature (erased types) *)
						match List.find_opt (fun cf -> cf.cf_name = method_name && is_instance_method cf) defining_class.cl_ordered_fields with
						| None -> false
						| Some def_cf ->
							(* Get implementation's concrete types from TFunction expr *)
							match List.find_opt (fun cf -> cf.cf_name = method_name) impl_class.cl_ordered_fields with
							| None -> false
							| Some impl_cf ->
								match impl_cf.cf_expr with
								| Some { eexpr = TFunction f } ->
									let def_arg_tc, def_ret_tc = match follow def_cf.cf_type with
										| TFun (args, ret) ->
											let arg_tcs = List.filter_map (fun (_, _, t) ->
												match follow t with
												| TAbstract ({ a_path = ([], "Void") }, []) -> None
												| _ -> Some (tc_type_of t)
											) args in
											(arg_tcs, tc_type_of ret)
										| _ -> ([], TCVoid)
									in
									let filtered = filter_void_args f.tf_args in
									let impl_arg_tc = List.map (fun (v, _) -> tc_type_of v.v_type) filtered in
									let impl_ret_tc = tc_type_of f.tf_type in
									def_arg_tc <> impl_arg_tc || def_ret_tc <> impl_ret_tc
								| _ -> false
				in
					if bridge_needed then begin
						(* Generate a vtable bridge thunk (dedup by bridge name) *)
						let bridge_name = Printf.sprintf "__%s_%s_vtbridge" impl_class_name (ident method_name) in
						if Hashtbl.mem bridge_seen bridge_name then
							{ ve_slot = slot; ve_method_name = ident method_name; ve_impl_name = bridge_name }
						else begin
						Hashtbl.add bridge_seen bridge_name true;
						let def_cf = match List.find_opt (fun cf -> cf.cf_name = method_name && is_instance_method cf) defining_class.cl_ordered_fields with
							| Some cf -> cf | None -> failwith ("vtbridge: no defining cf for " ^ method_name) in
						let impl_cf = match List.find_opt (fun cf -> cf.cf_name = method_name) impl_class.cl_ordered_fields with
							| Some cf -> cf | None -> failwith ("vtbridge: no impl cf for " ^ method_name) in
						let def_arg_tc, def_ret_tc = match follow def_cf.cf_type with
							| TFun (args, ret) ->
								let arg_tcs = List.filter_map (fun (_, _, t) ->
									match follow t with
									| TAbstract ({ a_path = ([], "Void") }, []) -> None
									| _ -> Some (tc_type_of t)
								) args in
								(arg_tcs, tc_type_of ret)
							| _ -> ([], TCVoid)
						in
						let f = match impl_cf.cf_expr with
							| Some { eexpr = TFunction f } -> f
							| _ -> failwith ("vtbridge: no TFunction for " ^ method_name) in
						let filtered = filter_void_args f.tf_args in
						let impl_arg_tc = List.map (fun (v, _) -> tc_type_of v.v_type) filtered in
						let impl_ret_tc = tc_type_of f.tf_type in
						let defining_class_name = flat_path defining_class.cl_path in
						(* Helper: convert an argument from the defining type to the impl type.
						   Handles three cases:
						   1. Same type: pass through
						   2. FibDynamic -> concrete: unbox from Dynamic
						   3. concrete -> concrete: C cast (e.g. int->double for covariance) *)
						let bridge_convert_arg arg_name src_tc dst_tc =
							if src_tc = dst_tc then arg_name
							else if src_tc = TCFibDynamic then
								(* Unbox from FibDynamic to concrete *)
								(match dst_tc with
								| TCFibArray _ ->
									Printf.sprintf "(%s)fib_dynamic_to_array(%s)" (tc_type_to_string dst_tc) arg_name
								| TCFibString ->
									Printf.sprintf "fib_dynamic_coerce_string(%s)" arg_name
								| TCInt32 -> Printf.sprintf "fib_dynamic_to_int(%s)" arg_name
								| TCInt64 -> Printf.sprintf "fib_dynamic_to_int64(%s)" arg_name
								| TCFloat64 -> Printf.sprintf "fib_dynamic_to_float(%s)" arg_name
								| TCBool -> Printf.sprintf "fib_dynamic_to_bool(%s)" arg_name
								| TCFibEnum name ->
									Printf.sprintf "*(%s*)fib_dynamic_to_ptr(%s)" name arg_name
								| _ ->
									Printf.sprintf "(%s)fib_dynamic_to_object(%s)" (tc_type_to_string dst_tc) arg_name)
							else
								(* Both are concrete but different: plain C cast *)
								Printf.sprintf "(%s)(%s)" (tc_type_to_string dst_tc) arg_name
						in
						(* Helper: convert a return value from the impl type back to the defining type.
						   Handles three cases:
						   1. Same type: pass through
						   2. concrete -> FibDynamic: box to Dynamic
						   3. concrete -> concrete: C cast *)
						let bridge_convert_ret expr_str src_tc dst_tc =
							if src_tc = dst_tc then expr_str
							else if dst_tc = TCFibDynamic then
								(* Box concrete to FibDynamic *)
								(match src_tc with
								| TCFibArray _ ->
									Printf.sprintf "fib_dynamic_array((FibArray*)%s)" expr_str
								| TCFibString ->
									Printf.sprintf "fib_dynamic_string(%s)" expr_str
								| TCInt32 -> Printf.sprintf "fib_dynamic_int(%s)" expr_str
								| TCInt64 -> Printf.sprintf "fib_dynamic_int64(%s)" expr_str
								| TCFloat64 -> Printf.sprintf "fib_dynamic_float(%s)" expr_str
								| TCBool -> Printf.sprintf "fib_dynamic_bool(%s)" expr_str
								| TCFibEnum name ->
									Printf.sprintf "({ %s _vb_tmp = %s; fib_dynamic_enum(&_vb_tmp, sizeof(%s)); })" (tc_type_to_string src_tc) expr_str name
								| TCVoid -> Printf.sprintf "((void)(%s), fib_dynamic_null())" expr_str
								| _ ->
									Printf.sprintf "(FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=%s}" expr_str)
							else
								(* Both concrete but different: C cast *)
								Printf.sprintf "(%s)(%s)" (tc_type_to_string dst_tc) expr_str
						in
					let buf = Buffer.create 512 in
					(* Function signature *)
					Buffer.add_string buf (Printf.sprintf "static %s %s(%s* this"
						(tc_type_to_string def_ret_tc) bridge_name defining_class_name);
						List.iteri (fun i tc ->
							Buffer.add_string buf (Printf.sprintf ", %s _arg%d" (tc_type_to_string tc) i)
						) def_arg_tc;
						Buffer.add_string buf ") {\n";
						(* Convert each argument from defining type to impl type *)
						let arg_pairs = List.combine def_arg_tc impl_arg_tc in
						List.iteri (fun i (def_tc, impl_tc) ->
							let converted = bridge_convert_arg (Printf.sprintf "_arg%d" i) def_tc impl_tc in
							Buffer.add_string buf (Printf.sprintf "\t%s _typed%d = %s;\n"
								(tc_type_to_string impl_tc) i converted)
						) arg_pairs;
						(* Build call to real implementation *)
						let call_args = Buffer.create 128 in
						Buffer.add_string call_args (Printf.sprintf "(%s*)this" impl_class_name);
						List.iteri (fun i _ ->
							Buffer.add_string call_args (Printf.sprintf ", _typed%d" i)
						) impl_arg_tc;
						let call_str = Printf.sprintf "%s(%s)" impl_func_name (Buffer.contents call_args) in
						(* Return with boxing if needed *)
						if def_ret_tc = TCVoid && impl_ret_tc = TCVoid then
							Buffer.add_string buf (Printf.sprintf "\t%s;\n" call_str)
						else if def_ret_tc = TCVoid then
							Buffer.add_string buf (Printf.sprintf "\t(void)%s;\n" call_str)
						else
							Buffer.add_string buf (Printf.sprintf "\treturn %s;\n"
								(bridge_convert_ret call_str impl_ret_tc def_ret_tc));
						Buffer.add_string buf "}\n";
						bridge_decls := (Buffer.contents buf) :: !bridge_decls;
						{ ve_slot = slot;
						  ve_method_name = ident method_name;
						  ve_impl_name = bridge_name }
						end (* begin dedup *)
					end else
						{ ve_slot = slot;
						  ve_method_name = ident method_name;
						  ve_impl_name = impl_func_name }
				| None ->
					(* Abstract method with no implementation in this class - emit NULL *)
					{ ve_slot = slot;
					  ve_method_name = ident method_name;
					  ve_impl_name = "NULL" }
			) vtable_methods in
			(* Emit bridge thunks before the vtable array *)
			List.iter (fun bridge_code -> add (TCDRaw bridge_code)) (List.rev !bridge_decls);
			add (TCDVtable {
				vt_name = class_name ^ "_vtable";
				vt_size = vtable_size;
				vt_entries = entries;
			});
			(* ABI category for a tc_type: types in the same category have the same
			   calling convention (size/register) and can be safely cast between without
			   an ivtable bridge. Only FibDynamic differs (16 bytes, RAX+RDX). *)
			let abi_category tc = match tc with
			  | TCFibDynamic -> `Dyn
			  | TCVoid -> `Void
			  | TCInt32 | TCBool -> `I32
			  | TCInt64 -> `I64
			  | TCFloat64 -> `F64
			  | TCFibEnum _ -> `Enum tc  (* each enum struct is its own ABI *)
			  | _ -> `Ptr  (* all pointer types: object, class, array, string, etc. *)
			in
			let abi_compatible a b = abi_category a = abi_category b in
			(* Check if all corresponding types in two lists are ABI-compatible *)
			let rec abi_compatible_lists l1 l2 = match l1, l2 with
			  | [], [] -> true
			  | a :: ra, b :: rb -> abi_compatible a b && abi_compatible_lists ra rb
			  | _ -> false  (* different lengths -> not compatible *)
			in
			(* 2b. Interface vtable (ivtable) generation.
			   For each vtable slot that was assigned by an interface method with a type-parameter
			   return type, the concrete implementation may return a typed value (pointer type)
			   while the interface call site expects FibDynamic (16-byte RAX+RDX). We generate a
			   separate ivtable with FibDynamic-returning wrappers for those slots, and the
			   remaining slots point to the same functions as the vtable. The ivtable pointer in
			   FibClass is only set when at least one slot differs from the main vtable. *)
			if not (has_class_flag c CInterface) then begin
			  let ifaces = collect_interfaces c in
			  (* Collect all interface methods that need ivtable bridges.
			     A bridge is needed when the interface declares a method with a type-parameter
			     return type (erased to TCFibDynamic) but the concrete implementation has a
			     non-Dynamic return type. *)
			  let ivtable_bridges = Hashtbl.create 4 in
			  let ivtable_seen = Hashtbl.create 4 in
			  List.iter (fun iface ->
			    List.iter (fun icf ->
			      if FiberusVtable.is_instance_method icf then begin
			        let method_name = icf.cf_name in
			        if not (Hashtbl.mem ivtable_seen method_name) then begin
			          Hashtbl.add ivtable_seen method_name true;
			          (* Get the slot for this interface method *)
			          let slot_opt = match ctx.vtable_ctx with
			            | Some vctx ->
			              (match FiberusVtable.get_interface_slot vctx iface icf with
			               | Some s -> Some s
			               | None -> None)
			            | None -> None
			          in
			          match slot_opt with
			          | None -> ()
			          | Some slot ->
			            (* Get the interface's erased return type *)
			            let iface_ret_tc = match follow icf.cf_type with
			              | TFun (_, ret) -> tc_type_of ret | _ -> TCVoid
			            in
			            (* Find the concrete implementation *)
			            let rec find_impl cls =
			              if List.exists (fun cf2 -> cf2.cf_name = method_name
			                && FiberusVtable.is_instance_method cf2
			                && not (has_class_field_flag cf2 CfAbstract)) cls.cl_ordered_fields
			              then Some cls
			              else match cls.cl_super with
			                | Some (p, _) -> find_impl p
			                | None -> None
			            in
			            (match find_impl c with
			            | None -> ()
			            | Some impl_class ->
			              let impl_class_name = flat_path impl_class.cl_path in
			              let impl_func_name = impl_class_name ^ "_" ^ ident method_name in
			              (match List.find_opt (fun cf2 -> cf2.cf_name = method_name) impl_class.cl_ordered_fields with
			              | None -> ()
			              | Some impl_cf ->
			                (match impl_cf.cf_expr with
			                | Some { eexpr = TFunction f } ->
			                  let impl_ret_tc = tc_type_of f.tf_type in
			                  let filtered = filter_void_args f.tf_args in
			                  let impl_arg_tc = List.map (fun (v, _) -> tc_type_of v.v_type) filtered in
			                  let iface_arg_tc = match follow icf.cf_type with
			                    | TFun (args, _) -> List.filter_map (fun (_, _, t) ->
			                        match follow t with
			                        | TAbstract ({ a_path = ([], "Void") }, []) -> None
			                        | _ -> Some (tc_type_of t)) args
			                    | _ -> []
			                  in
			                  (* Bridge needed only if ABI differs: e.g. FibDynamic 16 bytes vs
			                     pointer 8 bytes. Covariant pointer types share the same ABI. *)
			                  if not (abi_compatible iface_ret_tc impl_ret_tc && abi_compatible_lists iface_arg_tc impl_arg_tc) then begin
			                    let bridge_name = Printf.sprintf "__%s_%s_ivbridge" impl_class_name (ident method_name) in
			                    if not (Hashtbl.mem ivtable_bridges bridge_name) then begin
			                      Hashtbl.add ivtable_bridges bridge_name slot;
			                      (* Generate bridge with interface's return type and arg types.
			                         The bridge converts args from interface erased types to impl
			                         types, calls the impl, and converts the return value back to
			                         the interface's erased return type if they differ. *)
			                      let buf = Buffer.create 256 in
			                      let bridge_ret_type = tc_type_to_string iface_ret_tc in
			                      Buffer.add_string buf (Printf.sprintf
			                        "static %s %s(FibObject* this" bridge_ret_type bridge_name);
			                      List.iteri (fun i tc ->
			                        Buffer.add_string buf (Printf.sprintf ", %s _arg%d" (tc_type_to_string tc) i)
			                      ) iface_arg_tc;
			                      Buffer.add_string buf ") {\n";
			                      (* Convert each arg from iface type to impl type *)
			                      let safe_combine l1 l2 =
			                        let rec go a b = match a, b with
			                          | [], _ | _, [] -> []
			                          | x :: xs, y :: ys -> (x, y) :: go xs ys
			                        in go l1 l2
			                      in
			                      let arg_pairs = safe_combine iface_arg_tc impl_arg_tc in
			                      List.iteri (fun i (iface_tc, impl_tc) ->
			                        let converted =
			                          if iface_tc = impl_tc then Printf.sprintf "_arg%d" i
			                          else if iface_tc = TCFibDynamic then
			                            (match impl_tc with
			                            | TCFibArray _ ->
			                              Printf.sprintf "(%s)fib_dynamic_to_array(_arg%d)" (tc_type_to_string impl_tc) i
			                            | TCFibString ->
			                              Printf.sprintf "fib_dynamic_coerce_string(_arg%d)" i
			                            | TCInt32 -> Printf.sprintf "fib_dynamic_to_int(_arg%d)" i
			                            | TCInt64 -> Printf.sprintf "fib_dynamic_to_int64(_arg%d)" i
			                            | TCFloat64 -> Printf.sprintf "fib_dynamic_to_float(_arg%d)" i
			                            | TCBool -> Printf.sprintf "fib_dynamic_to_bool(_arg%d)" i
			                            | TCFibEnum name ->
			                              Printf.sprintf "*(%s*)fib_dynamic_to_ptr(_arg%d)" name i
			                            | _ -> Printf.sprintf "(%s)fib_dynamic_to_object(_arg%d)" (tc_type_to_string impl_tc) i)
			                          else Printf.sprintf "(%s)_arg%d" (tc_type_to_string impl_tc) i
			                        in
			                        Buffer.add_string buf (Printf.sprintf "\t%s _t%d = %s;\n"
			                          (tc_type_to_string impl_tc) i converted)
			                      ) arg_pairs;
			                      (* Build call *)
			                      let call_args = Buffer.create 64 in
			                      Buffer.add_string call_args (Printf.sprintf "(%s*)this" impl_class_name);
			                      List.iteri (fun i _ ->
			                        Buffer.add_string call_args (Printf.sprintf ", _t%d" i)
			                      ) impl_arg_tc;
			                      let call_str = Printf.sprintf "%s(%s)" impl_func_name (Buffer.contents call_args) in
			                      (* Convert return value from impl type to interface type *)
			                      let ret_expr =
			                        if iface_ret_tc = impl_ret_tc then call_str
			                        else if iface_ret_tc = TCFibDynamic then
			                          (* Box impl return to FibDynamic *)
			                          (match impl_ret_tc with
			                          | TCFibArray _ ->
			                            Printf.sprintf "fib_dynamic_array((FibArray*)%s)" call_str
			                          | TCFibString -> Printf.sprintf "fib_dynamic_string(%s)" call_str
			                          | TCInt32 -> Printf.sprintf "fib_dynamic_int(%s)" call_str
			                          | TCInt64 -> Printf.sprintf "fib_dynamic_int64(%s)" call_str
			                          | TCFloat64 -> Printf.sprintf "fib_dynamic_float(%s)" call_str
			                          | TCBool -> Printf.sprintf "fib_dynamic_bool(%s)" call_str
			                          | TCFibEnum name ->
			                            Printf.sprintf "({ %s _vb_tmp = %s; fib_dynamic_enum(&_vb_tmp, sizeof(%s)); })" name call_str name
			                          | TCVoid ->
			                            Printf.sprintf "((void)%s, fib_dynamic_null())" call_str
			                          | _ ->
			                            Printf.sprintf "(FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=%s}" call_str)
			                        else if impl_ret_tc = TCFibDynamic then
			                          (* Unbox FibDynamic to interface type *)
			                          (match iface_ret_tc with
			                          | TCInt32 -> Printf.sprintf "fib_dynamic_to_int(%s)" call_str
			                          | TCInt64 -> Printf.sprintf "fib_dynamic_to_int64(%s)" call_str
			                          | TCFloat64 -> Printf.sprintf "fib_dynamic_to_float(%s)" call_str
			                          | TCBool -> Printf.sprintf "fib_dynamic_to_bool(%s)" call_str
			                          | TCFibString -> Printf.sprintf "fib_dynamic_coerce_string(%s)" call_str
			                          | _ -> Printf.sprintf "(%s)fib_dynamic_to_object(%s)" bridge_ret_type call_str)
			                        else
			                          (* Neither is FibDynamic: simple C cast between typed values *)
			                          Printf.sprintf "(%s)%s" bridge_ret_type call_str
			                      in
			                      (if iface_ret_tc = TCVoid then
			                        Buffer.add_string buf (Printf.sprintf "\t%s;\n}\n" ret_expr)
			                      else
			                        Buffer.add_string buf (Printf.sprintf "\treturn %s;\n}\n" ret_expr));
			                      add (TCDRaw (Buffer.contents buf))
			                    end
			                  end
			                | _ -> ())))
			        end
			      end
			    ) iface.cl_ordered_fields
			  ) ifaces;
			  (* If any bridges were generated, build the ivtable array *)
			  if Hashtbl.length ivtable_bridges > 0 then begin
			    (* Build the ivtable: same size as vtable, with bridges for affected slots
			       and the same functions as vtable for unaffected slots *)
			    let ivtable_entries = Array.make vtable_size "NULL" in
			    (* Fill in bridges *)
			    Hashtbl.iter (fun bridge_name slot ->
			      if slot < vtable_size then
			        ivtable_entries.(slot) <- bridge_name
			    ) ivtable_bridges;
			    (* Fill in non-bridge slots from the vtable entries *)
			    List.iter (fun entry ->
			      if entry.ve_impl_name <> "NULL" && ivtable_entries.(entry.ve_slot) = "NULL" then
			        ivtable_entries.(entry.ve_slot) <- entry.ve_impl_name
			    ) entries;
			    let ivtable_name = class_name ^ "_ivtable" in
			    let ivt_code = Buffer.create 256 in
			    Buffer.add_string ivt_code (Printf.sprintf "static void* %s[%d] = {\n" ivtable_name vtable_size);
			    Array.iteri (fun i fn_name ->
			      Buffer.add_string ivt_code (Printf.sprintf "\t%s%s\n" fn_name (if i < vtable_size - 1 then "," else ""))
			    ) ivtable_entries;
			    Buffer.add_string ivt_code "};\n";
			    add (TCDRaw (Buffer.contents ivt_code));
			    ivtable_name_ref := Some ivtable_name
			  end
			end
		end;

		(* 3. FibClass struct *)
		let tostring_func = FiberusGenClass.find_tostring_func c in
		(* Extract instance field descriptors for Reflect.
		   Only include physical var fields -- properties with (get,set) without @:isVar
		   should NOT appear in getInstanceFields or Reflect.field, matching hxcpp behavior. *)
		let field_descs = List.filter_map (fun cf ->
			match cf.cf_kind with
			| Var _ when is_physical_var_field cf -> Some (cf.cf_name, tc_type_of cf.cf_type)
			| Method MethDynamic ->
				(* Dynamic methods are fields (closure pointers), visible to Reflect *)
				Some (cf.cf_name, TCPointer TCVoid)
			| _ -> None
		) c.cl_ordered_fields in
		(* Extract instance method descriptors for dynamic dispatch (fib_dynamic_get_field).
		   We generate thunks for ALL instance methods so that runtime dynamic field lookup
		   can create closures on the fly (needed by Lambda, Dynamic dispatch, etc.). *)
		let method_descs = List.filter_map (fun cf ->
			match cf.cf_kind with
			| Method MethNormal | Method MethInline ->
				(match cf.cf_expr with
			| Some { eexpr = TFunction f } ->
				let method_name = ident cf.cf_name in
				let thunk_name = Printf.sprintf "__%s_%s_thunk" class_name method_name in
				let dyn_thunk_name = thunk_name ^ "_dyn" in
				(* Derive parameter types from the TFunction expression's tf_args rather than
				   cf.cf_type — for @:generic specializations, cf.cf_type may have stale type
				   parameters while tf_args has the actual concrete types. *)
				let filtered_args = filter_void_args f.tf_args in
				let arg_types = List.map (fun (v, _) -> (v.v_name, tc_type_of v.v_type)) filtered_args in
				let ret_type = tc_type_of f.tf_type in
				let arg_count = List.length arg_types in
				(* Register the thunk so it gets generated *)
				let thunk = {
					mth_thunk_name = thunk_name;
					mth_dyn_thunk_name = dyn_thunk_name;
					mth_is_static = false;
					mth_class_name = class_name;
					mth_method_name = method_name;
					mth_args = arg_types;
					mth_ret_type = ret_type;
					mth_c_func = None;
					mth_this_expr = None;
					mth_vtable_slot = None;
					mth_defaults = extract_thunk_defaults filtered_args;
				} in
				Hashtbl.replace ctx.cast_method_thunks thunk_name thunk;
				Some {
					md_name = cf.cf_name;
					md_thunk_name = thunk_name;
					md_dyn_thunk_name = dyn_thunk_name;
					md_arg_count = arg_count;
				}
			| _ when has_class_flag c CInterface ->
				(* Interface abstract methods have no body, but we still need
				   descriptors so Type.getInstanceFields returns their names. *)
				let arg_count = match Type.follow cf.cf_type with
					| TFun (args, _) -> List.length args | _ -> 0 in
				Some {
					md_name = cf.cf_name;
					md_thunk_name = "NULL";
					md_dyn_thunk_name = "NULL";
					md_arg_count = arg_count;
				}
			| _ -> None)
			| _ -> None
		) c.cl_ordered_fields in
		(* Extract static field descriptors for Type.getClassFields and Reflect.field on Class values.
		   Only include physical var fields, matching hxcpp behavior. *)
		let static_field_descs = List.filter_map (fun cf ->
			match cf.cf_kind with
			| Var _ when not (has_class_field_flag cf CfNoLookup) && is_physical_var_field cf ->
				Some (cf.cf_name, tc_type_of cf.cf_type)
			| Method MethDynamic when has_class_field_flag cf CfStatic ->
				(* Static dynamic methods are stored as closure pointer globals *)
				Some (cf.cf_name, TCPointer TCVoid)
			| _ -> None
		) c.cl_ordered_statics in
		(* Extract static method descriptors for class-as-value dispatch.
		   When a class is used as a value (e.g. var t:Dynamic = MyClass), runtime needs to
		   look up static methods by name. Same thunk pattern as instance methods but with
		   mth_is_static = true (no 'this' capture). *)
		let static_method_descs = List.filter_map (fun cf ->
			match cf.cf_kind with
			| Method MethNormal | Method MethInline ->
				(match cf.cf_expr with
				| Some { eexpr = TFunction f } ->
					let method_name = ident cf.cf_name in
					let thunk_name = Printf.sprintf "__%s_%s_sthunk" class_name method_name in
					let dyn_thunk_name = thunk_name ^ "_dyn" in
					let filtered_args = filter_void_args f.tf_args in
					let arg_types = List.map (fun (v, _) -> (v.v_name, tc_type_of v.v_type)) filtered_args in
					let ret_type = tc_type_of f.tf_type in
					let arg_count = List.length arg_types in
					let thunk = {
						mth_thunk_name = thunk_name;
						mth_dyn_thunk_name = dyn_thunk_name;
						mth_is_static = true;
						mth_class_name = class_name;
						mth_method_name = method_name;
						mth_args = arg_types;
						mth_ret_type = ret_type;
						mth_c_func = None;
						mth_this_expr = None;
						mth_vtable_slot = None;
						mth_defaults = extract_thunk_defaults filtered_args;
					} in
					Hashtbl.replace ctx.cast_method_thunks thunk_name thunk;
					Some {
						md_name = cf.cf_name;
						md_thunk_name = thunk_name;
						md_dyn_thunk_name = dyn_thunk_name;
						md_arg_count = arg_count;
					}
				| _ -> None)
			| _ -> None
		) c.cl_ordered_statics in
		(* Generate constructor thunk for Type.createInstance reflection.
		   The constructor thunk calls ClassName_new(...) which allocates and initializes.
		   Like static thunks, there is no 'this' capture — _new handles allocation. *)
		let ctor_desc = match c.cl_constructor with
			| Some cf ->
				(match cf.cf_expr with
				| Some { eexpr = TFunction f } ->
					let thunk_name = Printf.sprintf "__%s_ctor_thunk" class_name in
					let dyn_thunk_name = thunk_name ^ "_dyn" in
					let filtered_args = filter_void_args f.tf_args in
					let arg_types = List.map (fun (v, _) -> (ident v.v_name, tc_type_of v.v_type)) filtered_args in
					let arg_count = List.length arg_types in
					let thunk = {
						mth_thunk_name = thunk_name;
						mth_dyn_thunk_name = dyn_thunk_name;
						mth_is_static = true;  (* No 'this' capture -- _new allocates its own *)
						mth_class_name = class_name;
						mth_method_name = "new";
						mth_args = arg_types;
						mth_ret_type = TCFibClass class_name;
						mth_c_func = Some (class_name ^ "_new");
						mth_this_expr = None;
						mth_vtable_slot = None;
						mth_defaults = extract_thunk_defaults filtered_args;
					} in
					Hashtbl.replace ctx.cast_method_thunks thunk_name thunk;
					Some {
						md_name = "new";
						md_thunk_name = thunk_name;
						md_dyn_thunk_name = dyn_thunk_name;
						md_arg_count = arg_count;
					}
				| _ -> None)
			| None ->
				(* No constructor: generate a 0-arg thunk that calls ClassName_new() *)
				let thunk_name = Printf.sprintf "__%s_ctor_thunk" class_name in
				let dyn_thunk_name = thunk_name ^ "_dyn" in
				let thunk = {
					mth_thunk_name = thunk_name;
					mth_dyn_thunk_name = dyn_thunk_name;
					mth_is_static = true;
					mth_class_name = class_name;
					mth_method_name = "new";
					mth_args = [];
					mth_ret_type = TCFibClass class_name;
					mth_c_func = Some (class_name ^ "_new");
					mth_this_expr = None;
					mth_vtable_slot = None;
					mth_defaults = [];
				} in
				Hashtbl.replace ctx.cast_method_thunks thunk_name thunk;
				Some {
					md_name = "new";
					md_thunk_name = thunk_name;
					md_dyn_thunk_name = dyn_thunk_name;
					md_arg_count = 0;
				}
		in
		(* Collect interfaces this class directly implements (including parent interfaces).
		   The runtime walks the super chain, so we only need interfaces declared on THIS class
		   plus any parent interfaces of those interfaces (transitive closure). *)
		let iface_names =
			let seen = Hashtbl.create 8 in
			let result = ref [] in
			let rec collect_ifaces iface =
				if not (Hashtbl.mem seen iface.cl_path) then begin
					Hashtbl.add seen iface.cl_path true;
					result := flat_path iface.cl_path :: !result;
					List.iter (fun (parent_iface, _) -> collect_ifaces parent_iface) iface.cl_implements
				end
			in
			List.iter (fun (iface, _) -> collect_ifaces iface) c.cl_implements;
			List.rev !result
		in
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
			cm_ivtable_name = !ivtable_name_ref;
			cm_fields = field_descs;
			cm_methods = method_descs;
			cm_static_fields = static_field_descs;
			cm_static_methods = static_method_descs;
			cm_ctor = ctor_desc;
			cm_interfaces = iface_names;
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
			| Method MethDynamic, _ when has_class_field_flag cf CfStatic ->
				(* Static dynamic function — declare a void* global to hold the closure pointer *)
				add (TCDVar {
					vd_name = class_name ^ "__dyn_" ^ ident cf.cf_name;
					vd_type = TCPointer TCVoid;
					vd_init = Some (mk_expr (TCERaw "NULL") (TCPointer TCVoid));
					vd_static = false;
					vd_const = false;
					vd_volatile = false;
				})
			| _ -> ()
		) c.cl_ordered_statics;

		(* 5. Boot function for runtime static initialization + __init__ *)
		let runtime_init_fields = get_runtime_init_fields c in
		let cl_init_expr = TClass.get_cl_init c in
		(* Collect static MethDynamic fields that need boot-time closure initialization *)
		let static_dyn_methods = List.filter (fun cf ->
			match cf.cf_kind with
			| Method MethDynamic when has_class_field_flag cf CfStatic -> true
			| _ -> false
		) c.cl_ordered_statics in
		if runtime_init_fields <> [] || cl_init_expr <> None || static_dyn_methods <> [] then begin
			let conv_ctx = make_conv_ctx ctx in
			conv_ctx.FiberusConvert.gc_local_count <- 0;
			conv_ctx.FiberusConvert.in_gc_frame <- true;
			conv_ctx.FiberusConvert.gc_frame_name <- "_gc";
			conv_ctx.FiberusConvert.gc_frame_slots <- [];
			conv_ctx.FiberusConvert.gc_frame_rooted_vars <- Hashtbl.create 8;
			let init_stmts = List.filter_map (fun cf ->
				match cf.cf_expr with
				| Some e ->
					let cexpr = FiberusConvert.convert_expr conv_ctx e in
					let field_tc = tc_type_of cf.cf_type in
					let cexpr = coerce_to_type cexpr field_tc in
					let lhs = mk_expr (TCERaw (class_name ^ "_" ^ ident cf.cf_name)) field_tc in
					Some (TCSExpr (mk_expr_inherit (TCEAssign (lhs, cexpr)) field_tc [cexpr]))
				| None -> None
			) runtime_init_fields in
			(* Generate closure initialization for static MethDynamic fields *)
			let dyn_init_stmts = List.map (fun cf ->
				let method_name = ident cf.cf_name in
				let thunk_name = Printf.sprintf "__%s_%s_thunk" class_name method_name in
				let dyn_thunk_name = thunk_name ^ "_dyn" in
				let arg_types, ret_type = match Type.follow cf.cf_type with
					| TFun (args, ret) ->
						(List.map (fun (n, _, t) -> (n, tc_type_of t)) args,
						 tc_type_of ret)
					| _ -> ([], TCFibDynamic)
				in
				let arg_count = List.length arg_types in
				(* Register the thunk so it gets generated in the .c file *)
				let thunk = {
					mth_thunk_name = thunk_name;
					mth_dyn_thunk_name = dyn_thunk_name;
					mth_is_static = true;
					mth_class_name = class_name;
					mth_method_name = method_name;
					mth_args = arg_types;
					mth_ret_type = ret_type;
					mth_c_func = None;
					mth_this_expr = None;
					mth_vtable_slot = None;
					mth_defaults = [];
				} in
				Hashtbl.replace ctx.cast_method_thunks thunk_name thunk;
				let var_name = Printf.sprintf "%s__dyn_%s" class_name method_name in
				TCSExpr (mk_expr (TCERaw (Printf.sprintf
					"%s = (void*)fib_closure_create((void*)%s, (void*)%s, 0, %d)"
					var_name thunk_name dyn_thunk_name arg_count)) TCVoid)
			) static_dyn_methods in
			(* Append __init__ body (cl_init) after field assignments *)
			let cl_init_stmts = match cl_init_expr with
				| Some e ->
					FiberusConvert.convert_stmt conv_ctx e
				| None -> []
			in
			(* Build GCFrame prologue/epilogue from accumulated slots *)
			let frame_info = FiberusConvert.gc_frame_build_info conv_ctx in
			let has_gc_slots = frame_info.gfi_slots <> [] in
			let prologue = [TCSGCCtx] @ (if has_gc_slots then [TCSGCFrameDecl frame_info] else []) in
			let epilogue = if has_gc_slots then [TCSGCFramePop "_gc"] else [] in
			add (TCDFunc {
				fd_name = class_name ^ "___boot";
				fd_ret = TCVoid;
				fd_args = [];
				fd_body = prologue @ dyn_init_stmts @ init_stmts @ cl_init_stmts @ epilogue;
				fd_static = false;
				fd_inline = false;
				fd_attrs = [];
			});
			(* Sync closures from boot function conversion back to class context.
			   Static field initializers and __init__ may contain lambdas/IIFEs
			   (e.g., haxe.xml.Parser.escapes block init) that create closure
			   definitions which must be emitted as top-level functions in the .c file. *)
			let new_closures = sync_closures_from_conv ctx conv_ctx in
			ctx.closures <- new_closures @ ctx.closures
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

let gen_enum_thunks (info : enum_info) : string =
	let buf = Buffer.create 512 in
	(* Unbox expression: convert FibDynamic arg to the typed C parameter *)
	let unbox_arg (tc_t : tc_type) (arg : string) : string =
		match tc_t with
		| TCInt32 -> Printf.sprintf "fib_dynamic_to_int(%s)" arg
		| TCInt64 -> Printf.sprintf "fib_dynamic_to_int64(%s)" arg
		| TCFloat64 | TCFloat32 -> Printf.sprintf "fib_dynamic_to_float(%s)" arg
		| TCBool -> Printf.sprintf "fib_dynamic_to_bool(%s)" arg
		| TCFibString -> Printf.sprintf "fib_dynamic_extract_string(%s)" arg
		| TCFibArray _ -> Printf.sprintf "((FibArray*)fib_dynamic_to_array(%s))" arg
		| TCFibClosure -> Printf.sprintf "((FibClosure*)fib_dynamic_to_object(%s))" arg
		| TCFibObject | TCFibClass _ -> Printf.sprintf "((FibObject*)fib_dynamic_to_object(%s))" arg
		| TCFibEnum _ -> Printf.sprintf "(*(%s*)fib_dynamic_to_ptr(%s))" (tc_type_to_string tc_t) arg
		| TCFibDynamic -> arg  (* Already FibDynamic, no conversion needed *)
		| _ -> arg  (* Default: pass through *)
	in
	(* Generate typed and dynamic thunks for each enum constructor.
	   These are used by Reflect.field to create callable closures for enum constructors.
	   - Typed thunk: returns the enum struct (for typed closure dispatch via _fc->fn)
	   - Dynamic thunk: returns FibDynamic (for dynamic dispatch via fib_closure_call_dynamic) *)
	List.iter (fun ci ->
		let n_params = List.length ci.eci_params in
		let constr_full = Printf.sprintf "%s_%s" info.ei_name ci.eci_name in
		(* Build parameter list for the thunk signatures: (FibClosure* _closure, FibDynamic arg0, ...) *)
		let params_sig = String.concat ", " (
			"FibClosure* _closure" ::
			List.mapi (fun i _ -> Printf.sprintf "FibDynamic arg%d" i) ci.eci_params
		) in
		let params_sig = if n_params = 0 then "FibClosure* _closure" else params_sig in
		(* Build argument list with unboxing for calling the actual constructor *)
		let call_args = String.concat ", " (
			List.mapi (fun i (_, tc_t, _) -> unbox_arg tc_t (Printf.sprintf "arg%d" i)) ci.eci_params
		) in
		(* Typed thunk - returns enum struct *)
		Buffer.add_string buf (Printf.sprintf "static %s _enum_typed_%s(%s) {\n" info.ei_name constr_full params_sig);
		Buffer.add_string buf "\t(void)_closure;\n";
		if ci.eci_has_params then
			Buffer.add_string buf (Printf.sprintf "\treturn %s(%s);\n" constr_full call_args)
		else
			Buffer.add_string buf (Printf.sprintf "\treturn %s;\n" constr_full);
		Buffer.add_string buf "}\n\n";
		(* Dynamic thunk - returns FibDynamic via fib_dynamic_enum *)
		Buffer.add_string buf (Printf.sprintf "static FibDynamic _enum_dyn_%s(%s) {\n" constr_full params_sig);
		Buffer.add_string buf "\t(void)_closure;\n";
		if ci.eci_has_params then
			Buffer.add_string buf (Printf.sprintf "\treturn fib_dynamic_enum_val(%s, %s(%s));\n" info.ei_name constr_full call_args)
		else
			Buffer.add_string buf (Printf.sprintf "\treturn fib_dynamic_enum_val(%s, %s);\n" info.ei_name constr_full);
		Buffer.add_string buf "}\n\n"
	) info.ei_constructors;
	Buffer.contents buf

let gen_enum_meta (info : enum_info) ~(has_haxe_meta : bool) : string =
	let buf = Buffer.create 256 in
	(* Emit constructor metadata array - includes typed/dynamic thunk pointers *)
	Buffer.add_string buf (Printf.sprintf "static const FibEnumConstrMeta %s_constrs[] = {\n" info.ei_name);
	List.iter (fun ci ->
		let constr_full = Printf.sprintf "%s_%s" info.ei_name ci.eci_name in
		Buffer.add_string buf (Printf.sprintf "\t{ \"%s\", %d, %d, (void*)_enum_typed_%s, (void*)_enum_dyn_%s },\n"
			ci.eci_name ci.eci_index (List.length ci.eci_params) constr_full constr_full)
	) info.ei_constructors;
	Buffer.add_string buf "};\n";
	(* Emit __meta__ global for RTTI if this enum has Haxe metadata annotations *)
	if has_haxe_meta then
		Buffer.add_string buf (Printf.sprintf "FibDynamic %s___meta__ = (FibDynamic){0};\n" info.ei_name);
	(* Emit enum metadata struct - includes FIB_ENUM_META_MAGIC discriminator *)
	let haxe_name = s_type_path info.ei_path in
	let meta_ptr = if has_haxe_meta then Printf.sprintf "&%s___meta__" info.ei_name else "NULL" in
	Buffer.add_string buf (Printf.sprintf "const FibEnumMeta %s_meta = { \"%s\", FIB_ENUM_META_MAGIC, %d, %s_constrs, %s };\n\n"
		info.ei_name haxe_name (List.length info.ei_constructors) info.ei_name meta_ptr);
	Buffer.contents buf

let gen_enum_impl ctx e =
	if has_enum_flag e EnExtern then ("", false) else begin
		let info = build_enum_info e in
		let decls = gen_enum_decls info in
		(* Skip the first decl (TCDEnum struct def) - that goes in the header *)
		let impl_decls = List.filter (fun d -> match d with TCDEnum _ -> false | _ -> true) decls in
		(* Generate constructor functions and constants first (referenced by thunks) *)
		let w = FiberusSourceWriter.create () in
		List.iter (FiberusSourceWriter.write_decl w) impl_decls;
		let constr_str = FiberusSourceWriter.contents w in
		(* Generate thunks (reference constructors, referenced by constrs array) *)
		let thunks_str = gen_enum_thunks info in
		(* Check if this enum has Haxe metadata annotations (for haxe.rtti.Meta) *)
		let meta_expr = Texpr.build_metadata ctx.com.basic (TEnumDecl e) in
		let has_haxe_meta = meta_expr <> None in
		(* Generate metadata tables last (references thunks) *)
		let meta_str = gen_enum_meta info ~has_haxe_meta in
		(* Generate boot function if enum has RTTI metadata *)
		let boot_str = match meta_expr with
			| Some expr ->
				let enum_name = info.ei_name in
				let conv_ctx = make_conv_ctx ctx in
				conv_ctx.FiberusConvert.gc_local_count <- 0;
				conv_ctx.FiberusConvert.in_gc_frame <- true;
				conv_ctx.FiberusConvert.gc_frame_name <- "_gc";
				conv_ctx.FiberusConvert.gc_frame_slots <- [];
				conv_ctx.FiberusConvert.gc_frame_rooted_vars <- Hashtbl.create 8;
				let cexpr = FiberusConvert.convert_expr conv_ctx expr in
				let lhs = mk_expr (TCERaw (enum_name ^ "___meta__")) TCFibDynamic in
				let assign = TCSExpr (mk_expr_inherit (TCEAssign (lhs, cexpr)) TCFibDynamic [cexpr]) in
				let frame_info = FiberusConvert.gc_frame_build_info conv_ctx in
				let has_gc_slots = frame_info.gfi_slots <> [] in
				let prologue = [TCSGCCtx] @ (if has_gc_slots then [TCSGCFrameDecl frame_info] else []) in
				let epilogue = if has_gc_slots then [TCSGCFramePop "_gc"] else [] in
				let boot_func = TCDFunc {
					fd_name = enum_name ^ "___boot";
					fd_ret = TCVoid;
					fd_args = [];
					fd_body = prologue @ [assign] @ epilogue;
					fd_static = false;
					fd_inline = false;
					fd_attrs = [];
				} in
				let bw = FiberusSourceWriter.create () in
				(* Emit any closures generated during metadata conversion *)
				let new_closures = sync_closures_from_conv ctx conv_ctx in
				ctx.closures <- new_closures @ ctx.closures;
				FiberusSourceWriter.write_decl bw boot_func;
				FiberusSourceWriter.contents bw
			| None -> ""
		in
		(constr_str ^ thunks_str ^ meta_str ^ boot_str, has_haxe_meta)
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
	spr ctx "#include <dirent.h>\n";
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
	spr ctx "#include \"process.h\"\n";
	spr ctx "#include \"reflect.h\"\n";
	spr ctx "#include \"ereg.h\"\n";
	spr ctx "#include \"json.h\"\n";
	spr ctx "#include \"compress.h\"\n";
	spr ctx "#include \"base64.h\"\n";
	spr ctx "#include \"resource.h\"\n";
	spr ctx "#include \"ssl.h\"\n";
	spr ctx "#include \"thread.h\"\n";
	spr ctx "#include \"sqlite_fib.h\"\n";
	spr ctx "#include \"simdutf_c.h\"\n";
	spr ctx "\n";

	(* Runtime API headers - extracted from inline C to proper .h files *)
	spr ctx "#include \"anon.h\"\n";
	spr ctx "#include \"exception.h\"\n";
	spr ctx "#include \"fiber_api.h\"\n";
	spr ctx "#include \"gc_api.h\"\n";
	spr ctx "\n";

	(* Cross-platform attribute for functions used only via function pointer *)
	spr ctx "/* Mark static functions whose address is taken (closures) */\n";
	spr ctx "#if defined(__GNUC__) || defined(__clang__)\n";
	spr ctx "#define FIB_USED __attribute__((used))\n";
	spr ctx "#else\n";
	spr ctx "#define FIB_USED\n";
	spr ctx "#endif\n\n";

	(* Generate forward declarations for all classes - including extern ones *)
	spr ctx "/* Forward declarations */\n";
	List.iter (function
		| TClassDecl c when not (is_skippable_abstract_impl c) ->
			(* Forward declare all classes, extern or not (skip abstract impl classes) *)
			print ctx "typedef struct %s %s;" (flat_path c.cl_path) (flat_path c.cl_path);
			newline ctx;
			(* Only non-extern classes have FibClass metadata *)
			if not (has_class_flag c CExtern) then begin
				print ctx "extern FibClass %s_class;" (flat_path c.cl_path);
				newline ctx
			end
		| TEnumDecl e ->
			(* Forward declare all enums - includes _meta pointer for reflection *)
			print ctx "typedef struct { const FibEnumMeta* _meta; int index; FibDynamic params[8]; } %s;" (flat_path e.e_path);
			newline ctx;
			(* Forward declare the metadata *)
			print ctx "extern const FibEnumMeta %s_meta;" (flat_path e.e_path);
			newline ctx;
			(* Forward declare __meta__ global and boot function if enum has Haxe metadata *)
			if not (has_enum_flag e EnExtern) && Texpr.build_metadata com.basic (TEnumDecl e) <> None then begin
				print ctx "extern FibDynamic %s___meta__;" (flat_path e.e_path);
				newline ctx;
				print ctx "void %s___boot(void);" (flat_path e.e_path);
				newline ctx
			end
		| _ -> ()
	) com.types;
	(* Extern declarations for primitive type class stubs *)
	spr ctx "/* Primitive type class stubs */\n";
	List.iter (fun name ->
		print ctx "extern FibClass %s_class;" name;
		newline ctx
	) ["Int"; "Float"; "Bool"; "Dynamic"; "Class"; "Enum"];
	newline ctx;

	(* Generate full struct definitions - needed for inheritance embedding *)
	spr ctx "/* Struct definitions */\n";
	List.iter (function
		| TClassDecl c when not (has_class_flag c CExtern) && not (is_skippable_abstract_impl c) ->
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
		| TClassDecl c when not (has_class_flag c CExtern) && not (is_skippable_abstract_impl c) ->
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
				| Method MethDynamic, _ when has_class_field_flag cf CfStatic ->
					(* Static dynamic function — extern for the closure variable *)
					print ctx "extern void* %s__dyn_%s;" class_name (ident cf.cf_name);
					newline ctx
				| _ -> ()
			) c.cl_ordered_statics
		| _ -> ()
	) com.types;
	newline ctx;

	(* Generate function forward declarations *)
	spr ctx "/* Function forward declarations */\n";
	List.iter (function
		| TClassDecl c when not (has_class_flag c CExtern) && not (is_skippable_abstract_impl c) ->
			let class_name = flat_path c.cl_path in
			(* Constructor _init and _new *)
			let class_tc = TCFibClass class_name in
			let this_arg = { fa_name = "this"; fa_type = class_tc } in
			(* Check if class has MethDynamic instance fields — these need non-trivial _init *)
			let has_dyn_methods = List.exists (fun cf2 ->
				match cf2.cf_kind with Method MethDynamic -> true | _ -> false
			) c.cl_ordered_fields in
			(match c.cl_constructor with
			| None when has_dyn_methods ->
				(* No constructor but has MethDynamic fields: forward-declare _init and _new
				   (they will be generated by convert_constructor in the .c file) *)
				let w = FiberusSourceWriter.create () in
				FiberusSourceWriter.write_decl w (TCDForwardFunc {
					fs_name = class_name ^ "_init"; fs_ret = TCVoid;
					fs_args = [class_tc] });
				FiberusSourceWriter.write_decl w (TCDForwardFunc {
					fs_name = class_name ^ "_new"; fs_ret = class_tc;
					fs_args = [] });
				spr ctx (FiberusSourceWriter.contents w)
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
					(* Classes with MethDynamic instance fields need full constructor path
					   to generate closure initialization for those fields *)
					let has_dyn_methods = List.exists (fun cf2 ->
						match cf2.cf_kind with Method MethDynamic -> true | _ -> false
					) c.cl_ordered_fields in
					let is_simple = is_simple_constructor f && not has_dyn_methods in
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
							| TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (decl_c, _, cf2)) }, value)
							| TParenthesis { eexpr = TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (decl_c, _, cf2)) }, value) } ->
								let cval = FiberusConvert.convert_expr conv_ctx value in
								let decl_name = flat_path decl_c.cl_path in
								let this_expr = mk_expr (TCELocal "this") class_tc in
								let lhs = if decl_name <> class_name then
									(* Inherited field: cast this to declaring class pointer type *)
									let cast_expr = mk_expr (TCECast (TCFibClass decl_name, this_expr)) (TCFibClass decl_name) in
									mk_expr (TCEArrow (cast_expr, ident cf2.cf_name)) cval.ctype
								else
									mk_expr (TCEArrow (this_expr, ident cf2.cf_name)) cval.ctype
								in
								init_body := TCSExpr (mk_expr (TCEAssign (lhs, cval)) cval.ctype) :: !init_body
							| _ -> ()
						in
						(match f.tf_expr.eexpr with
						| TBlock el -> List.iter extract_assigns el
						| _ -> extract_assigns f.tf_expr);
					(* Add (void)this if body is empty to suppress -Wunused-parameter *)
					let final_init_body = match !init_body with
						| [] -> [TCSRaw "(void)this;"]
						| body -> List.rev body
					in
					let init_func = { fd_name = class_name ^ "_init"; fd_ret = TCVoid;
						fd_args = this_arg :: ctor_args; fd_body = final_init_body;
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
			let has_static_dyn_methods = List.exists (fun cf ->
				match cf.cf_kind with Method MethDynamic when has_class_field_flag cf CfStatic -> true | _ -> false
			) c.cl_ordered_statics in
			let has_cl_init = TClass.get_cl_init c <> None in
			if runtime_init_fields <> [] || has_static_dyn_methods || has_cl_init then begin
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
					let func_name = Printf.sprintf "%s_%s" (flat_path c.cl_path) (ident cf.cf_name) in
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
					let func_name = Printf.sprintf "%s_%s" (flat_path c.cl_path) (ident cf.cf_name) in
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

(* Generate IMap vtable wrappers and arrays for the 4 hash map extern classes.
 * Hash maps (IntMap, StringMap, Int64Map, ObjectMap) are extern classes with no
 * codegen-generated vtables. When they flow through IMap-typed code paths, vtable
 * dispatch needs real function pointers. This generates bridge wrappers from the
 * erased IMap calling convention (FibDynamic keys/values) to concrete C runtime
 * functions, plus vtable arrays and an init function to patch the sentinel FibClasses. *)
let gen_map_imap_vtables vtable_ctx =
	let imap_slots = FiberusVtable.get_imap_slots vtable_ctx in
	if imap_slots = [] then ""  (* IMap not used in this build *)
	else begin
		let buf = Buffer.create 4096 in
		let b s = Buffer.add_string buf s in
		let bf fmt = Printf.kprintf (Buffer.add_string buf) fmt in

		(* Find the max slot index to size the vtable arrays *)
		let max_slot = List.fold_left (fun acc (_, slot) -> max acc slot) 0 imap_slots in
		let vtable_size = max_slot + 1 in

		b "\n/* ===== IMap vtable wrappers for hash map extern classes ===== */\n\n";

		(* Map kind definitions: (prefix, c_struct, class_var, key_unbox, key_type, key_box) *)
		let map_kinds = [
			("int", "FibIntMap", "haxe_ds_IntMap_class",
			 "fib_dynamic_to_int", "int32_t", "fib_dynamic_int");
			("string", "FibStringMap", "haxe_ds_StringMap_class",
			 "fib_dynamic_coerce_string", "FibString*", "fib_dynamic_string");
			("int64", "FibInt64Map", "haxe_ds_Int64Map_class",
			 "fib_dynamic_to_int64", "int64_t", "fib_dynamic_int64");
			("object", "FibObjectMap", "haxe_ds_ObjectMap_class",
			 "(FibObject*)fib_dynamic_to_object", "FibObject*",
			 "(FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=")
		] in

		List.iter (fun (prefix, c_struct, _class_var, key_unbox, _key_type, _key_box) ->
			(* For each IMap method, generate a wrapper if its slot exists *)
			List.iter (fun (mname, _slot) ->
				match mname with
				| "get" ->
					(* FibDynamic wrapper_get(void* self, FibDynamic key) *)
					bf "static FibDynamic _fib_imap_%s_get(void* self, FibDynamic key) {\n" prefix;
					bf "\treturn fib_%s_map_get_dynamic((%s*)self, %s(key));\n" prefix c_struct key_unbox;
					b "}\n"
				| "set" ->
					(* void wrapper_set(void* self, FibDynamic key, FibDynamic value) *)
					bf "static void _fib_imap_%s_set(void* self, FibDynamic key, FibDynamic value) {\n" prefix;
					bf "\tfib_%s_map_set_dynamic((%s*)self, %s(key), value);\n" prefix c_struct key_unbox;
					b "}\n"
				| "exists" ->
					(* bool wrapper_exists(void* self, FibDynamic key) *)
					bf "static bool _fib_imap_%s_exists(void* self, FibDynamic key) {\n" prefix;
					bf "\treturn fib_%s_map_exists((%s*)self, %s(key));\n" prefix c_struct key_unbox;
					b "}\n"
				| "remove" ->
					(* bool wrapper_remove(void* self, FibDynamic key) *)
					bf "static bool _fib_imap_%s_remove(void* self, FibDynamic key) {\n" prefix;
					bf "\treturn fib_%s_map_remove((%s*)self, %s(key));\n" prefix c_struct key_unbox;
					b "}\n"
				| "keys" ->
					(* FibDynamic wrapper_keys(void* self) -- returns iterator boxed as object *)
					bf "static FibDynamic _fib_imap_%s_keys(void* self) {\n" prefix;
					bf "\treturn (FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=fib_%s_map_keys((%s*)self)};\n" prefix c_struct;
					b "}\n"
				| "iterator" ->
					(* FibDynamic wrapper_iterator(void* self) -- returns iterator boxed as object *)
					bf "static FibDynamic _fib_imap_%s_iterator(void* self) {\n" prefix;
					bf "\treturn (FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=fib_%s_map_iterator((%s*)self)};\n" prefix c_struct;
					b "}\n"
				| "copy" ->
					(* FibDynamic wrapper_copy(void* self) -- returns map boxed as object *)
					bf "static FibDynamic _fib_imap_%s_copy(void* self) {\n" prefix;
					bf "\treturn (FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=fib_%s_map_copy((%s*)self)};\n" prefix c_struct;
					b "}\n"
				| "toString" ->
					(* FibString* wrapper_toString(void* self) *)
					bf "static FibString* _fib_imap_%s_toString(void* self) {\n" prefix;
					bf "\treturn fib_%s_map_to_string((%s*)self);\n" prefix c_struct;
					b "}\n"
				| "clear" ->
					(* void wrapper_clear(void* self) *)
					bf "static void _fib_imap_%s_clear(void* self) {\n" prefix;
					bf "\tfib_%s_map_clear((%s*)self);\n" prefix c_struct;
					b "}\n"
				| "keyValueIterator" ->
					(* Not implemented in hash map runtime - skip *)
					()
				| "size" ->
					(* FibDynamic wrapper_size(void* self) -- returns int boxed *)
					bf "static FibDynamic _fib_imap_%s_size(void* self) {\n" prefix;
					bf "\treturn fib_dynamic_int((int32_t)fib_%s_map_size((%s*)self));\n" prefix c_struct;
					b "}\n"
				| _ -> ()  (* Unknown IMap method - skip *)
			) imap_slots;
			b "\n"
		) map_kinds;

		(* Generate vtable arrays *)
		List.iter (fun (prefix, _c_struct, _class_var, _key_unbox, _key_type, _key_box) ->
			bf "static void* _fib_imap_%s_vtable[%d] = {\n" prefix vtable_size;
			for i = 0 to max_slot do
				let entry = List.find_opt (fun (_, slot) -> slot = i) imap_slots in
				match entry with
				| Some (mname, _) ->
					(* Check if this method has a wrapper (skip keyValueIterator) *)
					let has_wrapper = match mname with
						| "keyValueIterator" -> false
						| _ -> true
					in
					if has_wrapper then
						bf "\t(void*)_fib_imap_%s_%s%s /* slot %d: %s */\n"
							prefix mname (if i < max_slot then "," else "") i mname
					else
						bf "\tNULL%s /* slot %d: %s (not implemented) */\n"
							(if i < max_slot then "," else "") i mname
				| None ->
					bf "\tNULL%s /* slot %d */\n" (if i < max_slot then "," else "") i
			done;
			b "};\n\n"
		) map_kinds;

		(* ===== Method descriptor thunks for fib_dynamic_get_field ===== *)
		(* These are closure-style thunks: typed_thunk(FibClosure* _c, typed_args...)
		   where _c->captures[0] holds the map pointer as FibDynamic.
		   Plus dynamic_thunks: FibDynamic dyn(FibClosure* _c, FibDynamic...) *)
		b "\n/* ===== Hash map method descriptor thunks for dynamic field access ===== */\n\n";

		(* All methods to generate for each map kind *)
		let map_methods = [
			(* (name, arg_count, needs_key) *)
			("get", 1, true);
			("set", 2, true);
			("exists", 1, true);
			("remove", 1, true);
			("keys", 0, false);
			("iterator", 0, false);
			("keyValueIterator", 0, false);
			("copy", 0, false);
			("toString", 0, false);
			("clear", 0, false);
		] in

		List.iter (fun (prefix, c_struct, _class_var, key_unbox, _key_type, _key_box) ->
			List.iter (fun (mname, _arg_count, _needs_key) ->
				match mname with
				| "get" ->
					(* typed: FibDynamic _md_int_get(FibClosure* _c, FibDynamic key) *)
					bf "static FibDynamic _fib_md_%s_get(FibClosure* _c, FibDynamic key) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\treturn fib_%s_map_get_dynamic(self, %s(key));\n" prefix key_unbox;
					b "}\n";
					(* dynamic: FibDynamic _md_int_get_dyn(FibClosure* _c, FibDynamic _arg0) *)
					bf "static FibDynamic _fib_md_%s_get_dyn(FibClosure* _c, FibDynamic _arg0) {\n" prefix;
					bf "\treturn _fib_md_%s_get(_c, _arg0);\n" prefix;
					b "}\n"
				| "set" ->
					bf "static void _fib_md_%s_set(FibClosure* _c, FibDynamic key, FibDynamic value) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\tfib_%s_map_set_dynamic(self, %s(key), value);\n" prefix key_unbox;
					b "}\n";
					bf "static FibDynamic _fib_md_%s_set_dyn(FibClosure* _c, FibDynamic _arg0, FibDynamic _arg1) {\n" prefix;
					bf "\t_fib_md_%s_set(_c, _arg0, _arg1);\n" prefix;
					b "\treturn fib_dynamic_null();\n}\n"
				| "exists" ->
					bf "static bool _fib_md_%s_exists(FibClosure* _c, FibDynamic key) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\treturn fib_%s_map_exists(self, %s(key));\n" prefix key_unbox;
					b "}\n";
					bf "static FibDynamic _fib_md_%s_exists_dyn(FibClosure* _c, FibDynamic _arg0) {\n" prefix;
					bf "\treturn fib_dynamic_bool(_fib_md_%s_exists(_c, _arg0));\n" prefix;
					b "}\n"
				| "remove" ->
					bf "static bool _fib_md_%s_remove(FibClosure* _c, FibDynamic key) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\treturn fib_%s_map_remove(self, %s(key));\n" prefix key_unbox;
					b "}\n";
					bf "static FibDynamic _fib_md_%s_remove_dyn(FibClosure* _c, FibDynamic _arg0) {\n" prefix;
					bf "\treturn fib_dynamic_bool(_fib_md_%s_remove(_c, _arg0));\n" prefix;
					b "}\n"
				| "keys" ->
					bf "static FibDynamic _fib_md_%s_keys(FibClosure* _c) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\treturn (FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=fib_%s_map_keys(self)};\n" prefix;
					b "}\n";
					bf "static FibDynamic _fib_md_%s_keys_dyn(FibClosure* _c) {\n" prefix;
					bf "\treturn _fib_md_%s_keys(_c);\n" prefix;
					b "}\n"
				| "iterator" ->
					bf "static FibDynamic _fib_md_%s_iterator(FibClosure* _c) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\treturn (FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=fib_%s_map_iterator(self)};\n" prefix;
					b "}\n";
					bf "static FibDynamic _fib_md_%s_iterator_dyn(FibClosure* _c) {\n" prefix;
					bf "\treturn _fib_md_%s_iterator(_c);\n" prefix;
					b "}\n"
				| "keyValueIterator" ->
					(* keyValueIterator creates a MapKeyValueIterator, passing the map as FibDynamic *)
					bf "static FibDynamic _fib_md_%s_keyValueIterator(FibClosure* _c) {\n" prefix;
					b "\tFibDynamic self_dyn = _c->captures[0];\n";
					b "\treturn (FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=haxe_iterators_MapKeyValueIterator_new(self_dyn)};\n";
					b "}\n";
					bf "static FibDynamic _fib_md_%s_keyValueIterator_dyn(FibClosure* _c) {\n" prefix;
					bf "\treturn _fib_md_%s_keyValueIterator(_c);\n" prefix;
					b "}\n"
				| "copy" ->
					bf "static FibDynamic _fib_md_%s_copy(FibClosure* _c) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\treturn (FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=fib_%s_map_copy(self)};\n" prefix;
					b "}\n";
					bf "static FibDynamic _fib_md_%s_copy_dyn(FibClosure* _c) {\n" prefix;
					bf "\treturn _fib_md_%s_copy(_c);\n" prefix;
					b "}\n"
				| "toString" ->
					bf "static FibString* _fib_md_%s_toString(FibClosure* _c) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\treturn fib_%s_map_to_string(self);\n" prefix;
					b "}\n";
					bf "static FibDynamic _fib_md_%s_toString_dyn(FibClosure* _c) {\n" prefix;
					bf "\treturn fib_dynamic_string(_fib_md_%s_toString(_c));\n" prefix;
					b "}\n"
				| "clear" ->
					bf "static void _fib_md_%s_clear(FibClosure* _c) {\n" prefix;
					bf "\t%s* self = (%s*)fib_dynamic_to_object(_c->captures[0]);\n" c_struct c_struct;
					bf "\tfib_%s_map_clear(self);\n" prefix;
					b "}\n";
					bf "static FibDynamic _fib_md_%s_clear_dyn(FibClosure* _c) {\n" prefix;
					bf "\t_fib_md_%s_clear(_c);\n" prefix;
					b "\treturn fib_dynamic_null();\n}\n"
				| _ -> ()
			) map_methods;
			b "\n"
		) map_kinds;

		(* Generate FibMethodDesc arrays for each map kind *)
		List.iter (fun (prefix, _c_struct, _class_var, _key_unbox, _key_type, _key_box) ->
			bf "static const FibMethodDesc _fib_md_%s_methods[] = {\n" prefix;
			List.iter (fun (mname, arg_count, _needs_key) ->
				bf "\t{ \"%s\", (void*)_fib_md_%s_%s, (void*)_fib_md_%s_%s_dyn, %d },\n"
					mname prefix mname prefix mname arg_count
			) map_methods;
			b "};\n\n"
		) map_kinds;

		(* Generate init function *)
		let method_count = List.length map_methods in
		b "void fib_map_vtables_init(void) {\n";
		List.iter (fun (prefix, _c_struct, class_var, _key_unbox, _key_type, _key_box) ->
			bf "\t%s.vtable = _fib_imap_%s_vtable;\n" class_var prefix;
			bf "\t%s.vtableSize = %d;\n" class_var vtable_size;
			bf "\t%s.methods = _fib_md_%s_methods;\n" class_var prefix;
			bf "\t%s.methodCount = %d;\n" class_var method_count
		) map_kinds;
		b "}\n";

		Buffer.contents buf
	end

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
	Buffer.add_string buf "\t\tfprintf(stderr, \"Uncaught exception (type=%d\", exc.type);\n";
	Buffer.add_string buf "\t\tif (exc.type == FIB_TYPE_OBJECT) {\n";
	Buffer.add_string buf "\t\t\tFibObject* obj = exc.data.objectVal;\n";
	Buffer.add_string buf "\t\t\tif (obj && obj->clazz && obj->clazz->name)\n";
	Buffer.add_string buf "\t\t\t\tfprintf(stderr, \", class=%s\", obj->clazz->name);\n";
	Buffer.add_string buf "\t\t} else if (exc.type == FIB_TYPE_STRING) {\n";
	Buffer.add_string buf "\t\t\tFibString* s = exc.data.stringVal;\n";
	Buffer.add_string buf "\t\t\tif (s) fprintf(stderr, \", str=\\\"%.*s\\\"\", (int)(s->byte_length < 200 ? s->byte_length : 200), (const char*)(s + 1));\n";
	Buffer.add_string buf "\t\t}\n";
	Buffer.add_string buf "\t\tfprintf(stderr, \")\\n\");\n";
	Buffer.add_string buf "\t\texit(1);\n";
	Buffer.add_string buf "\t}\n";
	Buffer.add_string buf "}\n\n";
	Buffer.add_string buf "/* haxe.Exception is generated by the codegen from Exception.hx */\n\n";
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
		| TClassDecl c when not (has_class_flag c CExtern) && not (is_skippable_abstract_impl c) ->
			let class_name = flat_path c.cl_path in
			List.iter (fun cf ->
				match cf.cf_kind with
				| Var _ when not (has_class_field_flag cf CfNoLookup) ->
					(* Regular class static variable - check if it needs GC root *)
					if haxe_type_needs_gc_root cf.cf_type then begin
						let c_type = s_type ctx cf.cf_type in
						gc_roots := (class_name, ident cf.cf_name, c_type) :: !gc_roots
					end
				| Method MethDynamic when has_class_field_flag cf CfStatic ->
					(* Static dynamic function — the closure pointer needs GC root *)
					gc_roots := (class_name, "_dyn_" ^ ident cf.cf_name, "void*") :: !gc_roots
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
	(* Generate IMap vtable wrappers for hash map extern classes *)
	let map_vtable_content = match ctx.vtable_ctx with
		| Some vctx -> gen_map_imap_vtables vctx
		| None -> ""
	in
	let globals_file = src_dir ^ "/fiberus_globals.c" in
	let ch = open_out_bin globals_file in
	output_string ch globals_content;
	output_string ch map_vtable_content;
	close_out ch;
	generated_files := "fiberus_globals.c" :: !generated_files;

	(* Generate embedded resources file (always emitted, even if empty) *)
	let resources = Hashtbl.fold (fun name data acc -> (name, data) :: acc) com.resources [] in
	let resources = List.sort (fun (a, _) (b, _) -> String.compare a b) resources in
	Buffer.clear ctx.buf;
	spr ctx "/* Embedded resources - generated by genfiberus */\n";
	spr ctx "#include \"fiberus_generated.h\"\n\n";
	(* Emit each resource as a static const byte array *)
	List.iteri (fun i (_name, data) ->
		print ctx "static const unsigned char __fib_res_%d[] = {" i;
		let len = String.length data in
		for j = 0 to len - 1 do
			if j > 0 then spr ctx ",";
			if j mod 16 = 0 then spr ctx "\n\t";
			print ctx "0x%02x" (Char.code (String.get data j))
		done;
		spr ctx "\n};\n\n"
	) resources;
	(* Emit the resource registry array *)
	spr ctx "const FibResource fiberus_resources[] = {\n";
	List.iteri (fun i (name, data) ->
		(* Escape the resource name for C string literal: backslashes first, then quotes *)
		let escaped_name = String.concat "\\\\" (Str.split_delim (Str.regexp "\\\\") name) in
		let escaped_name = String.concat "\\\"" (Str.split_delim (Str.regexp "\"") escaped_name) in
		print ctx "\t{ \"%s\", %d, __fib_res_%d },\n" escaped_name (String.length data) i
	) resources;
	spr ctx "\t{ NULL, 0, NULL }\n";
	spr ctx "};\n";
	print ctx "const int fiberus_resource_count = %d;\n" (List.length resources);
	let res_file = src_dir ^ "/fiberus_resources.c" in
	let ch = open_out_bin res_file in
	output_string ch (Buffer.contents ctx.buf);
	close_out ch;
	generated_files := "fiberus_resources.c" :: !generated_files;

	(* Generate one .c file per class *)
	List.iter (function
		| TClassDecl c when not (has_class_flag c CExtern) && not (is_skippable_abstract_impl c) ->
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
			let (impl, _has_meta) = gen_enum_impl ctx e in
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

	(* Collect classes that need boot functions (runtime-init statics, __init__, or static dynamic methods) *)
	let boot_classes = List.filter_map (function
		| TClassDecl c when not (has_class_flag c CExtern) && not (is_skippable_abstract_impl c) ->
			let has_runtime_init = get_runtime_init_fields c <> [] in
			let has_cl_init = TClass.get_cl_init c <> None in
			let has_static_dyn = List.exists (fun cf ->
				match cf.cf_kind with Method MethDynamic when has_class_field_flag cf CfStatic -> true | _ -> false
			) c.cl_ordered_statics in
			if has_runtime_init || has_cl_init || has_static_dyn then Some (flat_path c.cl_path)
			else None
		| _ -> None
	) com.types in

	(* Collect enums that need boot functions (those with Haxe metadata annotations) *)
	let boot_enums = List.filter_map (function
		| TEnumDecl e when not (has_enum_flag e EnExtern) ->
			if Texpr.build_metadata com.basic (TEnumDecl e) <> None then Some (flat_path e.e_path)
			else None
		| _ -> None
	) com.types in

	(* Collect all non-extern class names for registration *)
	let reg_classes = List.filter_map (function
		| TClassDecl c when not (has_class_flag c CExtern) && not (is_skippable_abstract_impl c) -> Some (flat_path c.cl_path)
		| _ -> None
	) com.types in

	(* Collect all non-extern enum names for registration *)
	let reg_enums = List.filter_map (function
		| TEnumDecl e when not (has_enum_flag e EnExtern) -> Some (flat_path e.e_path)
		| _ -> None
	) com.types in

	(* Generate Main.c with main function *)
	Buffer.clear ctx.buf;
	spr ctx "/* Entry point */\n";
	spr ctx "#include \"fiberus_generated.h\"\n";
	spr ctx "#include \"telemetry.h\"\n\n";
	(* Stub FibClass definitions for primitive types (Int, Float, Bool, String, Dynamic).
	   These allow TTypeExpr boxing to FibDynamic and runtime type checks via
	   fib_dynamic_instanceof when the type is passed as a Dynamic value. *)
	spr ctx "/* Primitive type class stubs for runtime type reflection */\n";
	List.iter (fun (name, display) ->
		print ctx "FibClass %s_class = { .name = \"%s\", .classId = 0, .instanceSize = 0 };\n" name display
	) [("Int", "Int"); ("Float", "Float"); ("Bool", "Bool"); ("Dynamic", "Dynamic"); ("Class", "Class"); ("Enum", "Enum")];
	spr ctx "\n";
	(* Forward declarations for functions defined in fiberus_globals.c *)
	if map_vtable_content <> "" then
		spr ctx "extern void fib_map_vtables_init(void);\n\n";

	(* Generate the main fiber entry function via C-AST pipeline *)
	let main_body = match com.main.main_expr with
		| Some e ->
			let conv_ctx = make_conv_ctx ctx in
			conv_ctx.FiberusConvert.gc_local_count <- 0;
			conv_ctx.FiberusConvert.in_gc_frame <- true;
			conv_ctx.FiberusConvert.gc_frame_name <- "_gc";
			conv_ctx.FiberusConvert.gc_frame_slots <- [];
			conv_ctx.FiberusConvert.gc_frame_rooted_vars <- Hashtbl.create 8;
			let stmts = FiberusConvert.convert_stmt conv_ctx e in
			(* Sync closures back *)
			let new_closures = sync_closures_from_conv ctx conv_ctx in
			if new_closures <> [] then ctx.closures <- new_closures @ ctx.closures;
			(* Build GCFrame prologue/epilogue from accumulated slots *)
			let frame_info = FiberusConvert.gc_frame_build_info conv_ctx in
			let has_gc_slots = frame_info.gfi_slots <> [] in
			let prologue = [TCSRaw "(void)arg;"; TCSGCCtx] @ (if has_gc_slots then [TCSGCFrameDecl frame_info] else []) in
			let epilogue = if has_gc_slots then [TCSGCFramePop "_gc"] else [] in
			prologue @ stmts @ epilogue
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
	(* Register all classes and enums with the runtime *)
	if reg_classes <> [] || reg_enums <> [] then begin
		spr ctx "\t/* 3b. Register classes and enums for Type reflection */\n";
		(* Register sentinel/builtin classes for Type reflection *)
		spr ctx "\tfib_class_register(&String_class);\n";
		spr ctx "\tfib_class_register(&Array_class);\n";
		List.iter (fun class_name ->
			print ctx "\tfib_class_register(&%s_class);\n" class_name
		) reg_classes;
		List.iter (fun enum_name ->
			print ctx "\tfib_enum_register(&%s_meta);\n" enum_name
		) reg_enums;
		spr ctx "\n"
	end;
	(* Register dynamic iterator factory if ArrayIterator was compiled *)
	if List.mem "haxe_iterators_ArrayIterator" reg_classes then begin
		spr ctx "\t/* 3c. Register array iterator factory for dynamic dispatch */\n";
		spr ctx "\tfib_array_dynamic_iterator_new = (FibObject*(*)(FibArray*))haxe_iterators_ArrayIterator_new;\n\n"
	end;
	(* Initialize IMap vtables for hash map extern classes *)
	if map_vtable_content <> "" then begin
		spr ctx "\t/* 3d. Initialize IMap vtables for hash map extern classes */\n";
		spr ctx "\tfib_map_vtables_init();\n\n"
	end;
	(* Initialize array method descriptors for dynamic dispatch *)
	spr ctx "\t/* 3e. Initialize array method descriptors for dynamic dispatch */\n";
	spr ctx "\tfib_array_methods_init();\n\n";
	(* Call boot functions to initialize static fields - must happen after scheduler_init *)
	if boot_classes <> [] || boot_enums <> [] then begin
		spr ctx "\t/* 4. Boot all classes and enums (static field / metadata initialization)\n";
		spr ctx "\t *    Now safe to allocate - we have ThreadBlockCache and FiberGCContext */\n";
		List.iter (fun class_name ->
			print ctx "\t%s___boot();\n" class_name
		) boot_classes;
		List.iter (fun enum_name ->
			print ctx "\t%s___boot();\n" enum_name
		) boot_enums;
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
	Buffer.add_string build_xml "<!-- Append generated code to fiberus target and build as executable -->\n";
	Buffer.add_string build_xml "<target id=\"fiberus\" output=\"Main\" toolid=\"exe\">\n";
	Buffer.add_string build_xml "  <files id=\"haxe\"/>\n";
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
