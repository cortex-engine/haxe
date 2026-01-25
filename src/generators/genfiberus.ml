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
open GenfiberusVtable

type ctx = {
	com : Gctx.t;
	buf : Buffer.t;
	mutable tabs : string;
	mutable in_value : bool;
	mutable id_counter : int;
	mutable local_types : (int, string) Hashtbl.t;
	mutable current_ret_type : Type.t option;
	mutable current_class : tclass option;
	mutable class_id_counter : int;
	mutable class_ids : (path, int) Hashtbl.t;
	(* Stack tracking for source mapping *)
	debug_level : int;  (* 0=none, 1=trace, 2=line *)
	mutable last_line : int;  (* Track last emitted line to avoid duplicates *)
	(* Closure support *)
	mutable closure_counter : int;
	mutable closures : (string * tfunc * tvar list) list;  (* name, function, captured vars *)
	mutable in_closure_impl : bool;  (* True when generating closure implementations *)
	mutable closure_fwd_decls : Buffer.t;  (* Buffer for forward declarations during impl phase *)
	mutable in_fiber_spawn : bool;  (* True when generating a closure for Fiber.spawn *)
	(* GC root tracking: count of gc_push_temp_root calls in current function *)
	mutable gc_local_count : int;
	(* Loop depth tracking: skip yield points in deeply nested loops *)
	mutable loop_depth : int;
	(* GC context: has FIB_GC_CTX been emitted in this function? *)
	mutable has_gc_ctx : bool;
	(* Escape analysis: set of variable IDs that can be stack-allocated *)
	mutable stack_alloc_vars : (int, tclass) Hashtbl.t;
	(* Vtable context for virtual method dispatch *)
	mutable vtable_ctx : GenfiberusVtable.vtable_context option;
	(* Method thunks: methods that are used as values and need closure wrappers *)
	(* Maps thunk_name -> (is_static, class_path, method_name, arg_types, ret_type) *)
	mutable method_thunks : (string, bool * path * string * (string * Type.t) list * Type.t) Hashtbl.t;
}

(*
 * Escape Analysis for Stack Allocation
 *
 * Determines which local variables holding newly allocated objects can be
 * stack-allocated instead of heap-allocated. A variable can be stack-allocated if:
 * 1. It's assigned directly from a TNew expression
 * 2. It has no super-class
 * 3. The object never "escapes" - i.e., it's never:
 *    - Stored in a field of another object
 *    - Stored in an array
 *    - Passed to a function call (except for field access on 'this')
 *    - Returned from the function
 *    - Captured by a closure
 *    - Thrown as an exception
 *
 * Stack-allocated objects:
 * - Don't need gc_alloc (allocated on C stack)
 * - Don't need gc_push_temp_root (stack is scanned conservatively)
 * - Are automatically freed when the function returns
 *)

(* Check if a class is suitable for stack allocation (simple value-like class) *)
let can_stack_alloc_class (c : tclass) : bool =
	(* Must not have a custom destructor/mark function that needs special handling *)
	not (has_class_flag c CExtern) &&
	(* Must not be an interface *)
	not (has_class_flag c CInterface) &&
	(* Must not extend another class (so it has _obj directly, not _parent) *)
	(match c.cl_super with
	| None -> true
	| Some _ -> false)

(* Analyze a function and return a set of variable IDs that can be stack-allocated *)
let analyze_escapes (f : tfunc) : (int, tclass) Hashtbl.t =
	let stack_vars = Hashtbl.create 16 in
	let escaped_vars = Hashtbl.create 16 in
	
	(* Mark a variable as escaped *)
	let mark_escaped v_id =
		Hashtbl.replace escaped_vars v_id true;
		Hashtbl.remove stack_vars v_id
	in
	
	(* Check if an expression references a tracked variable *)
	let rec get_local_var_id e =
		match e.eexpr with
		| TLocal v -> Some v.v_id
		| TParenthesis e -> get_local_var_id e
		| _ -> None
	in
	
	(* Mark variable as escaped if it's a tracked allocation *)
	let mark_if_tracked e =
		match get_local_var_id e with
		| Some v_id when Hashtbl.mem stack_vars v_id -> mark_escaped v_id
		| _ -> ()
	in
	
	(* Recursively analyze an expression for escapes *)
	let rec analyze e =
		match e.eexpr with
		(* Track new allocations assigned to local variables *)
		| TVar (v, Some { eexpr = TNew (c, _, args) }) when can_stack_alloc_class c ->
			(* Only track if not already escaped *)
			if not (Hashtbl.mem escaped_vars v.v_id) then
				Hashtbl.replace stack_vars v.v_id c;
			(* Analyze constructor arguments - they might reference tracked vars *)
			List.iter analyze args
		
		(* Reassignment to a tracked variable - the NEW value might escape *)
		| TBinop (OpAssign, { eexpr = TLocal v }, ({ eexpr = TNew (c, _, args) } as rhs)) 
			when can_stack_alloc_class c ->
			(* If reassigning, keep tracking if it's still a direct TNew *)
			if not (Hashtbl.mem escaped_vars v.v_id) then
				Hashtbl.replace stack_vars v.v_id c;
			List.iter analyze args
		
		(* Assignment to field - RHS escapes *)
		| TBinop (OpAssign, { eexpr = TField _ }, rhs) ->
			mark_if_tracked rhs;
			analyze rhs
		
		(* Assignment to array - RHS escapes *)
		| TBinop (OpAssign, { eexpr = TArray _ }, rhs) ->
			mark_if_tracked rhs;
			analyze rhs
		
		(* Return - value escapes *)
		| TReturn (Some e) ->
			mark_if_tracked e;
			analyze e
		
		(* Throw - value escapes *)
		| TThrow e ->
			mark_if_tracked e;
			analyze e
		
		(* Function call - all arguments escape (conservative) *)
		(* Exception: field access on tracked var is OK (e.g., val.i) *)
		| TCall (func, args) ->
			(* The function itself might be a tracked var (if it's a closure field) *)
			analyze func;
			(* All arguments escape *)
			List.iter (fun arg ->
				mark_if_tracked arg;
				analyze arg
			) args
		
		(* Closure/function expression - captured variables escape *)
		| TFunction tf ->
			(* Any variable used in the closure body that's from outer scope escapes *)
			let rec find_captures e =
				match e.eexpr with
				| TLocal v ->
					(* If this variable is tracked, it's being captured - mark escaped *)
					if Hashtbl.mem stack_vars v.v_id then
						mark_escaped v.v_id
				| _ -> Type.iter find_captures e
			in
			find_captures tf.tf_expr
		
		(* Field access is OK - we're just reading from the object *)
		| TField (obj, _) ->
			analyze obj
		
		(* Array access is OK for reading *)
		| TArray (arr, idx) ->
			analyze arr;
			analyze idx
		
		(* Default: recurse into sub-expressions *)
		| _ ->
			Type.iter analyze e
	in
	
	(* Analyze the function body *)
	analyze f.tf_expr;
	
	(* Return only non-escaped variables *)
	stack_vars

(* Check if a type is void *)
let is_void_type t =
	match follow t with
	| TAbstract ({ a_path = ([], "Void") }, []) -> true
	| _ -> false

(* Filter function arguments to exclude void-typed parameters *)
let filter_void_args args =
	List.filter (fun (v, _) -> not (is_void_type v.v_type)) args

(* Extract parameter-to-field mapping from a simple constructor body.
   Returns a list of (param_var_id, field_name) pairs *)
let extract_param_field_mapping (f : tfunc) : (int * string) list =
	let mappings = ref [] in
	let filtered_args = filter_void_args f.tf_args in
	let param_ids = List.map (fun (v, _) -> v.v_id) filtered_args in
	let rec find_mapping e =
		match e.eexpr with
		| TBlock el -> List.iter find_mapping el
		| TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, 
		          { eexpr = TLocal param_v })
		| TParenthesis { eexpr = TBinop (OpAssign, 
		          { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, 
		          { eexpr = TLocal param_v }) } ->
			(* Found: this.field = param *)
			if List.mem param_v.v_id param_ids then
				mappings := (param_v.v_id, cf.cf_name) :: !mappings
		| _ -> ()
	in
	find_mapping f.tf_expr;
	!mappings

(* C keywords that need escaping *)
let c_kwds =
	let h = Hashtbl.create 0 in
	List.iter (fun s -> Hashtbl.add h s ()) [
		"auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do";
		"double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if";
		"int"; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static";
		"struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"; "while";
		"inline"; "restrict"; "_Bool"; "_Complex"; "_Imaginary";
		"bool"; "true"; "false"; "NULL";
	];
	h

let ident s =
	if Hashtbl.mem c_kwds s then "_hx_" ^ s else s

let spr ctx s =
	Buffer.add_string ctx.buf s

let print ctx =
	Printf.kprintf (fun s -> Buffer.add_string ctx.buf s)

let newline ctx =
	print ctx "\n%s" ctx.tabs

let temp ctx =
	ctx.id_counter <- ctx.id_counter + 1;
	"_hx_tmp" ^ string_of_int ctx.id_counter

(* Check if an expression ends with a return statement.
 * Used to avoid generating redundant gc_pop_temp_roots after returns,
 * since return statements already handle their own cleanup. *)
let rec ends_with_return e =
	match e.eexpr with
	| TReturn _ -> true
	| TBlock el when el <> [] -> ends_with_return (List.hd (List.rev el))
	| TIf (_, then_e, Some else_e) -> ends_with_return then_e && ends_with_return else_e
	| TSwitch sw ->
		(* All cases must end with return, including default *)
		let cases_return = List.for_all (fun c -> ends_with_return c.case_expr) sw.switch_cases in
		let default_returns = match sw.switch_default with
			| Some d -> ends_with_return d
			| None -> false
		in
		cases_return && default_returns
	| TTry (try_e, catches) ->
		ends_with_return try_e && List.for_all (fun (_, e) -> ends_with_return e) catches
	| TWhile (_, body, DoWhile) -> ends_with_return body  (* do-while might fall through *)
	| _ -> false

let open_block ctx =
	let old_tabs = ctx.tabs in
	let saved_gc_count = ctx.gc_local_count in
	ctx.tabs <- ctx.tabs ^ "\t";
	spr ctx "{";
	newline ctx;
	(fun () ->
		(* Pop GC roots that were pushed in this block *)
		let to_pop = ctx.gc_local_count - saved_gc_count in
		if to_pop > 0 then begin
			print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" to_pop;
			newline ctx;
			ctx.gc_local_count <- saved_gc_count
		end;
		ctx.tabs <- old_tabs;
		newline ctx;
		spr ctx "}")

(* Open a block for an expression list, checking if it ends with return.
 * If it ends with return, skip the gc_pop since return handles its own cleanup. *)
let open_block_for_exprs ctx el =
	let old_tabs = ctx.tabs in
	let saved_gc_count = ctx.gc_local_count in
	ctx.tabs <- ctx.tabs ^ "\t";
	spr ctx "{";
	newline ctx;
	(fun () ->
		(* Pop GC roots that were pushed in this block, but only if block doesn't end with return *)
		let to_pop = ctx.gc_local_count - saved_gc_count in
		let block_returns = match el with
			| [] -> false
			| _ -> 
				let last_expr = List.hd (List.rev el) in
				ends_with_return last_expr
		in
		if to_pop > 0 && not block_returns then begin
			print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" to_pop;
			newline ctx
		end;
		ctx.gc_local_count <- saved_gc_count;
		ctx.tabs <- old_tabs;
		newline ctx;
		spr ctx "}")

(* Get or assign a unique class ID *)
let get_class_id ctx path =
	try Hashtbl.find ctx.class_ids path
	with Not_found ->
		let id = ctx.class_id_counter in
		ctx.class_id_counter <- ctx.class_id_counter + 1;
		Hashtbl.add ctx.class_ids path id;
		id

let s_path (p, s) =
	match p with
	| [] -> s
	| _ -> String.concat "_" p ^ "_" ^ s

let flat_path path =
	let p, s = path in
	let escape str = String.concat "__" (ExtString.String.nsplit str "_") in
	match p with
	| [] -> escape s
	| _ -> String.concat "_" (List.map escape p) ^ "_" ^ escape s

(* Strip common prefix from file path for cleaner source refs *)
let strip_file file =
	(* Just use the filename for now - could strip common prefix later *)
	Filename.basename file

(* Escape string for C string literal *)
let escape_string s =
	let b = Buffer.create (String.length s) in
	String.iter (fun c ->
		match c with
		| '\\' -> Buffer.add_string b "\\\\"
		| '"' -> Buffer.add_string b "\\\""
		| '\n' -> Buffer.add_string b "\\n"
		| '\r' -> Buffer.add_string b "\\r"
		| '\t' -> Buffer.add_string b "\\t"
		| c -> Buffer.add_char b c
	) s;
	Buffer.contents b

(*
 * gen_stack_push - Generate stack frame setup at function entry
 *
 * Emits FIB_LOCAL_STACK_FRAME to define static position data,
 * then FIB_STACKFRAME to create the runtime frame.
 *)
let gen_stack_push ctx class_name func_name pos =
	if ctx.debug_level > 0 then begin
		let file = strip_file pos.pfile in
		let esc_file = escape_string file in
		let line = Lexer.get_error_line pos in
		let full_name = class_name ^ "." ^ func_name in
		(* Generate unique position variable name *)
		let var_name = Printf.sprintf "_fib_pos_%s_%d_%s" class_name line func_name in
		(* Define static position data *)
		print ctx "FIB_LOCAL_STACK_FRAME(%s, \"%s\", \"%s\", \"%s\", \"%s\", %d)"
			var_name class_name func_name full_name esc_file line;
		newline ctx;
		(* Create runtime frame *)
		print ctx "FIB_STACKFRAME(&%s)" var_name;
		newline ctx;
		(* Initialize line tracking *)
		ctx.last_line <- line
	end

(*
 * gen_line - Emit line number marker for source mapping
 *
 * Only emits FIBLINE if debug_level >= 2 and line changed.
 *)
let gen_line ctx pos =
	if ctx.debug_level >= 2 then begin
		let line = Lexer.get_error_line pos in
		if line <> ctx.last_line then begin
			print ctx "FIBLINE(%d)" line;
			newline ctx;
			ctx.last_line <- line
		end
	end

let rec s_type ctx t =
	match t with
	| TAbstract ({ a_path = ([], "Void") }, []) -> "void"
	| TAbstract ({ a_path = ([], "Int") }, []) -> "int32_t"
	| TAbstract ({ a_path = ([], "Float") }, []) -> "double"
	| TAbstract ({ a_path = ([], "Bool") }, []) -> "bool"
	| TAbstract ({ a_path = ([], "Null") }, [t]) ->
		(* Nullable primitives need FibDynamic to hold null, nullable objects stay as pointers *)
		(match follow t with
		| TAbstract ({ a_path = ([], "Int") }, [])
		| TAbstract ({ a_path = ([], "Float") }, [])
		| TAbstract ({ a_path = ([], "Bool") }, []) -> "FibDynamic"
		| _ -> s_type ctx t)
	| TInst ({ cl_path = ([], "String") }, []) -> "FibString*"
	| TInst ({ cl_path = ([], "Array") }, [elem_t]) ->
		(* Specialized arrays for primitive types *)
		(match follow elem_t with
		| TAbstract ({ a_path = ([], "Int") }, []) -> "FibIntArray*"
		| TAbstract ({ a_path = ([], "Float") }, []) -> "FibFloatArray*"
		| TAbstract ({ a_path = ([], "Bool") }, []) -> "FibBoolArray*"
		(* Fiberus specialized arrays *)
		| TAbstract ({ a_path = (["fiberus"], "UInt8") }, []) -> "FibUInt8Array*"
		| TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "FibInt64Array*"
		| TAbstract ({ a_path = (["fiberus"], "UInt64") }, []) -> "FibUInt64Array*"
		| TAbstract ({ a_path = (["fiberus"], "Float32") }, []) -> "FibFloat32Array*"
		| _ -> "FibArray*")
	| TInst ({ cl_path = ([], "Array") }, _) -> "FibArray*"
	(* Hash map types *)
	| TInst ({ cl_path = (["haxe"; "ds"], "IntMap") }, _) -> "FibIntMap*"
	| TInst ({ cl_path = (["haxe"; "ds"], "StringMap") }, _) -> "FibStringMap*"
	| TInst ({ cl_path = (["haxe"; "ds"], "Int64Map") }, _) -> "FibInt64Map*"
	| TInst ({ cl_path = (["haxe"; "ds"], "ObjectMap") }, _) -> "FibObjectMap*"
	| TInst ({ cl_kind = KTypeParameter _ }, _) ->
		(* Type parameter T, K, V etc -> generic value *)
		"FibDynamic"
	| TInst (c, params) ->
		(* Check if any type parameter is unresolved - use FibDynamic for generics *)
		let has_type_param = List.exists (fun p ->
			match follow p with
			| TMono { tm_type = None } -> true
			| TInst ({ cl_kind = KTypeParameter _ }, _) -> true
			| _ -> false
		) params in
		if has_type_param then "FibDynamic"
		else flat_path c.cl_path ^ "*"
	| TEnum (e, _) -> flat_path e.e_path
	| TDynamic _ -> "FibDynamic"
	| TFun (args, ret) ->
		(* Function types are always FibClosure* in Fiberus.
		 * Raw function pointer syntax is only needed in casts (s_func_ptr_cast).
		 * This allows passing lambdas, method references, and closures uniformly. *)
		ignore args; ignore ret;
		"FibClosure*"
	| TAnon _ -> "FibDynamic"
	| TMono r -> (match r.tm_type with None -> "FibDynamic" | Some t -> s_type ctx t)
	| TType (td, tl) -> s_type ctx (apply_typedef td tl)
	| TAbstract (a, tl) ->
		(* Check for type parameters in abstract *)
		(match a.a_path with
		| ([], name) when String.length name = 1 && name.[0] >= 'A' && name.[0] <= 'Z' ->
			(* Single uppercase letter likely a type parameter *)
			"FibDynamic"
		| (["haxe"; "io"], "BytesData") ->
			(* Native bytes data pointer *)
			"FibBytesData*"
		(* Fiberus native types *)
		| (["fiberus"], "Char") -> "char"
		| (["fiberus"], "Int8") -> "int8_t"
		| (["fiberus"], "Int16") -> "int16_t"
		| (["fiberus"], "Int32") -> "int32_t"
		| (["fiberus"], "Int64") -> "int64_t"
		| (["fiberus"], "UInt8") -> "uint8_t"
		| (["fiberus"], "UInt16") -> "uint16_t"
		| (["fiberus"], "UInt32") -> "uint32_t"
		| (["fiberus"], "UInt64") -> "uint64_t"
		| (["fiberus"], "Float32") -> "float"
		| (["fiberus"], "Float64") -> "double"
		| (["fiberus"], "SizeT") -> "size_t"
		| (["fiberus"], "AtomicInt") -> "_Atomic int"
		| _ -> s_type ctx (Abstract.get_underlying_type a tl))
	| TLazy f -> s_type ctx (lazy_type f)

(* Generate type declaration with name - handles function pointer syntax correctly
 * For function types: now just "FibClosure* name" since all functions are closures
 * For other types: "type name"
 *)
and s_type_with_name ctx t name =
	(* s_type already returns FibClosure* for TFun, so just use standard format *)
	Printf.sprintf "%s %s" (s_type ctx t) name

(* Generate a function declaration when the return type might be a function pointer
 * For normal return types: "ret func_name(args)"
 * For function pointer return types: now just "FibClosure* func_name(args)"
 * since all function values are FibClosure* in Fiberus.
 *)
and s_func_decl ctx ret_type func_name func_args =
	(* s_type returns FibClosure* for TFun, so use standard format *)
	Printf.sprintf "%s %s(%s)" (s_type ctx ret_type) func_name func_args

(* Generate a function pointer CAST expression for closure calls.
 * For normal return types: "(ret_type (*)(fn_args))"
 * For closure return types (TFun): returns FibClosure* since all closures are FibClosure
 *)
and s_func_ptr_cast ctx ret_type fn_args_str =
	let full_args = if fn_args_str = "" then "FibClosure*" else "FibClosure*, " ^ fn_args_str in
	match follow ret_type with
	| TFun _ ->
		(* Return type is a function - closures return FibClosure* for other closures *)
		Printf.sprintf "(FibClosure* (*)(%s))" full_args
	| _ ->
		(* Normal return type - standard function pointer cast *)
		Printf.sprintf "(%s (*)(%s))" (s_type ctx ret_type) full_args

(* Check if a type needs GC root registration (can hold object references) *)
let rec needs_gc_root ctx t =
	match t with
	| TAbstract ({ a_path = ([], "Void") }, []) -> false
	| TAbstract ({ a_path = ([], "Int") }, []) -> false
	| TAbstract ({ a_path = ([], "Float") }, []) -> false
	| TAbstract ({ a_path = ([], "Bool") }, []) -> false
	| TAbstract ({ a_path = ([], "Null") }, [t]) ->
		(* Nullable primitives become FibDynamic which can hold refs *)
		(match follow t with
		| TAbstract ({ a_path = ([], "Int") }, [])
		| TAbstract ({ a_path = ([], "Float") }, [])
		| TAbstract ({ a_path = ([], "Bool") }, []) -> true
		| _ -> needs_gc_root ctx t)
	| TInst ({ cl_path = ([], "String") }, []) -> true  (* FibString* *)
	| TInst ({ cl_path = ([], "Array") }, _) -> true    (* FibArray* *)
	| TInst ({ cl_kind = KTypeParameter _ }, _) -> true (* FibDynamic can hold refs *)
	| TInst (_, _) -> true  (* Class pointer *)
	| TEnum (_, _) -> false (* Enums are typically integers *)
	| TDynamic _ -> true    (* FibDynamic can hold refs *)
	| TFun _ -> false       (* void* function pointers *)
	| TAnon _ -> true       (* FibDynamic can hold refs *)
	| TMono r -> (match r.tm_type with None -> true | Some t -> needs_gc_root ctx t)
	| TType (td, tl) -> needs_gc_root ctx (apply_typedef td tl)
	| TAbstract (a, tl) ->
		(* Fiberus native types don't need GC roots *)
		(match a.a_path with
		| (["fiberus"], "Char")
		| (["fiberus"], "Int8")
		| (["fiberus"], "Int16")
		| (["fiberus"], "Int32")
		| (["fiberus"], "Int64")
		| (["fiberus"], "UInt8")
		| (["fiberus"], "UInt16")
		| (["fiberus"], "UInt32")
		| (["fiberus"], "UInt64")
		| (["fiberus"], "Float32")
		| (["fiberus"], "Float64")
		| (["fiberus"], "SizeT")
		| (["fiberus"], "AtomicInt") -> false
		| _ -> needs_gc_root ctx (Abstract.get_underlying_type a tl))
	| TLazy f -> needs_gc_root ctx (lazy_type f)

(* Check if constructor body is simple enough to inline in header.
   A simple constructor:
   1. Only has field assignments (TBinop OpAssign to TField on this)
   2. No allocations (TNew)
   3. No local variables that need GC roots
   4. No function calls (except simple field accessors)
*)
let is_simple_constructor ctx f =
	(* Check if expression is a simple field assignment: this.field = value *)
	let rec is_simple_expr e =
		match e.eexpr with
		| TBlock el -> List.for_all is_simple_expr el
		| TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, _) }, value) ->
			is_simple_value value
		| TParenthesis e -> is_simple_expr e
		| _ -> false
	and is_simple_value e =
		match e.eexpr with
		| TConst _ -> true
		| TLocal _ -> true
		| TField ({ eexpr = TConst TThis }, _) -> true
		| TBinop (_, e1, e2) -> is_simple_value e1 && is_simple_value e2
		| TUnop (_, _, e) -> is_simple_value e
		| TParenthesis e -> is_simple_value e
		| _ -> false
	in
	(* Check all arguments are primitive types (no GC roots needed) *)
	let all_args_primitive = List.for_all (fun (v, _) ->
		not (needs_gc_root ctx v.v_type)
	) f.tf_args in
	all_args_primitive && is_simple_expr f.tf_expr

let gen_constant ctx = function
	| TInt i -> print ctx "%ld" i
	| TFloat s -> spr ctx s
	| TString s ->
		spr ctx "fib_string_new(\"";
		spr ctx (StringHelper.s_escape s);
		spr ctx "\")"
	| TBool b -> spr ctx (if b then "true" else "false")
	| TNull -> spr ctx "NULL"
	| TThis -> spr ctx "this"
	| TSuper -> spr ctx "this"  (* super calls use this in C *)

(* Generate FibDynamic struct initializer for array literals *)
let gen_fib_dynamic_constant ctx = function
	| TInt i -> print ctx "{.type=FIB_TYPE_INT, .data.intVal=%ld}" i
	| TFloat s -> print ctx "{.type=FIB_TYPE_FLOAT, .data.floatVal=%s}" s
	| TString s ->
		spr ctx "{.type=FIB_TYPE_STRING, .data.stringVal=fib_string_new(\"";
		spr ctx (StringHelper.s_escape s);
		spr ctx "\")}"
	| TBool b -> print ctx "{.type=FIB_TYPE_BOOL, .data.boolVal=%s}" (if b then "true" else "false")
	| TNull -> spr ctx "{.type=FIB_TYPE_NULL, .data.ptrVal=NULL}"
	| TThis -> spr ctx "{.type=FIB_TYPE_OBJECT, .data.objectVal=(FibObject*)this}"
	| TSuper -> spr ctx "{.type=FIB_TYPE_OBJECT, .data.objectVal=(FibObject*)this}"

let gen_binop ctx op =
	match op with
	| OpAdd -> spr ctx " + "
	| OpMult -> spr ctx " * "
	| OpDiv -> spr ctx " / "
	| OpSub -> spr ctx " - "
	| OpAssign -> spr ctx " = "
	| OpEq -> spr ctx " == "
	| OpNotEq -> spr ctx " != "
	| OpGt -> spr ctx " > "
	| OpGte -> spr ctx " >= "
	| OpLt -> spr ctx " < "
	| OpLte -> spr ctx " <= "
	| OpAnd -> spr ctx " & "
	| OpOr -> spr ctx " | "
	| OpXor -> spr ctx " ^ "
	| OpBoolAnd -> spr ctx " && "
	| OpBoolOr -> spr ctx " || "
	| OpShl -> spr ctx " << "
	| OpShr -> spr ctx " >> "
	| OpUShr -> spr ctx " >> "  (* Handled specially in TBinop case above *)
	| OpMod -> spr ctx " % "
	| OpAssignOp op ->
		spr ctx " ";
		(match op with
		| OpAdd -> spr ctx "+="
		| OpMult -> spr ctx "*="
		| OpDiv -> spr ctx "/="
		| OpSub -> spr ctx "-="
		| OpAnd -> spr ctx "&="
		| OpOr -> spr ctx "|="
		| OpXor -> spr ctx "^="
		| OpShl -> spr ctx "<<="
		| OpShr -> spr ctx ">>="
		| OpUShr -> spr ctx ">>="  (* Handled specially in TBinop case *)
		| OpMod -> spr ctx "%="
		| _ -> spr ctx "=");
		spr ctx " "
	| OpInterval -> spr ctx " ... "
	| OpArrow -> spr ctx " => "
	| OpIn -> spr ctx " in "
	| OpNullCoal -> spr ctx " ?? "

let gen_unop ctx op flag =
	match op, flag with
	| Increment, Prefix -> spr ctx "++"
	| Decrement, Prefix -> spr ctx "--"
	| Not, Prefix -> spr ctx "!"
	| Neg, Prefix -> spr ctx "-"
	| NegBits, Prefix -> spr ctx "~"
	| Spread, Prefix -> spr ctx "..."
	| Increment, Postfix -> spr ctx "++"
	| Decrement, Postfix -> spr ctx "--"
	| _ -> ()

(* Check if type is String *)
let is_string_type t =
	match follow t with
	| TInst ({ cl_path = ([], "String") }, []) -> true
	| _ -> false

(* Check if type is FibDynamic (dynamic) *)
let is_dynamic_type t =
	match follow t with
	| TDynamic _ -> true
	| TAnon _ -> true
	| TMono { tm_type = None } -> true
	| TAbstract ({ a_path = ([], "Dynamic") }, _) -> true
	| TType ({ t_path = ([], "Dynamic") }, _) -> true
	| _ -> false

(* Check if type is Array *)
let is_array_type t =
	match follow t with
	| TInst ({ cl_path = ([], "Array") }, _) -> true
	| _ -> false

(* Get array element type as C type string *)
let get_array_elem_type ctx t =
	match follow t with
	| TInst ({ cl_path = ([], "Array") }, [elem_t]) -> s_type ctx elem_t
	| _ -> "FibDynamic"

(* Check if a type is a class pointer type - ends with asterisk *)
let is_class_pointer_type s =
	String.length s > 1 && s.[String.length s - 1] = '*' &&
	s <> "FibString*" && s <> "FibArray*" && s <> "FibDynamic*"

(* Check if a type string represents a GC-managed pointer that needs marking *)
let needs_gc_marking type_str =
	let len = String.length type_str in
	len > 0 && type_str.[len - 1] = '*'

(* Check if a type is an enum struct type (not a pointer, not a primitive) *)
let is_enum_struct_type s =
	s <> "int32_t" && s <> "double" && s <> "bool" && s <> "void" &&
	s <> "FibDynamic" && s <> "FibString*" && s <> "FibArray*" &&
	(String.length s = 0 || s.[String.length s - 1] <> '*')

(* Generate FibDynamic field access suffix for unboxing based on element type *)
let fib_dynamic_unbox_suffix elem_type =
	if elem_type = "int32_t" then ".data.intVal"
	else if elem_type = "double" then ".data.floatVal"
	else if elem_type = "FibString*" then ".data.stringVal"
	else if elem_type = "bool" then ".data.boolVal"
	else ""

(* Generate boxing wrapper for value to FibDynamic. gen_inner is called to generate the inner value. *)
let gen_box_to_fib_dynamic ctx type_str gen_inner =
	if type_str = "FibDynamic" then begin
		(* Already boxed, output as-is *)
		gen_inner ()
	end else if type_str = "int32_t" then begin
		spr ctx "fib_dynamic_int("; gen_inner (); spr ctx ")"
	end else if type_str = "double" then begin
		spr ctx "fib_dynamic_float("; gen_inner (); spr ctx ")"
	end else if type_str = "bool" then begin
		spr ctx "fib_dynamic_bool("; gen_inner (); spr ctx ")"
	end else if type_str = "FibString*" then begin
		spr ctx "fib_dynamic_string("; gen_inner (); spr ctx ")"
	end else if type_str = "FibArray*" then begin
		spr ctx "fib_dynamic_array("; gen_inner (); spr ctx ")"
	end else if is_class_pointer_type type_str then begin
		spr ctx "fib_dynamic_object((FibObject*)"; gen_inner (); spr ctx ")"
	end else if is_enum_struct_type type_str then begin
		(* Enum struct - box with fib_dynamic_enum.
		   Use statement expression with temp var since we can't take address of function return. *)
		print ctx "({ %s _enum_tmp = " type_str; gen_inner (); print ctx "; fib_dynamic_enum(&_enum_tmp, sizeof(%s)); })" type_str
	end else
		gen_inner ()

(* Get actual C type from expression, unwrapping casts/meta *)
let rec get_actual_c_type ctx e =
	match e.eexpr with
	(* TCast explicitly changes the type - return the cast's target type, not the inner type *)
	| TCast (_, _) -> Some (s_type ctx e.etype)
	| TMeta (_, inner) -> get_actual_c_type ctx inner
	| TParenthesis inner -> get_actual_c_type ctx inner
	| TBlock exprs when exprs <> [] ->
		(* Block expressions evaluate to the last expression *)
		get_actual_c_type ctx (List.hd (List.rev exprs))
	(* Local variable - use the variable's type directly *)
	| TLocal v -> Some (s_type ctx v.v_type)
	(* Dynamic/anonymous field access returns FibDynamic *)
	| TField (_, FAnon _) | TField (_, FDynamic _) -> Some "FibDynamic"
	(* Static field: use actual field type *)
	| TField (_, FStatic (_, cf)) -> Some (s_type ctx cf.cf_type)
	(* Instance field: use actual field type *)
	| TField (_, FInstance (_, _, cf)) -> Some (s_type ctx cf.cf_type)
	(* Closure: use actual field type *)
	| TField (_, FClosure (_, cf)) -> Some (s_type ctx cf.cf_type)
	(* Array literals produce specialized type based on expression type *)
	| TArrayDecl _ -> Some (s_type ctx e.etype)
	(* Array element access returns the element type for typed arrays *)
	| TArray (e1, _) ->
		let elem_type = get_array_elem_type ctx e1.etype in
		Some elem_type
	(* Dynamic method calls - toString returns FibString* *)
	| TCall ({ eexpr = TField (_, FAnon cf) }, _) when cf.cf_name = "toString" -> Some "FibString*"
	| TCall ({ eexpr = TField (_, FDynamic "toString") }, _) -> Some "FibString*"
	(* Static method calls - use the method's return type *)
	| TCall ({ eexpr = TField (_, FStatic (_, cf)) }, _) ->
		(match follow cf.cf_type with
		| TFun (_, ret) -> Some (s_type ctx ret)
		| _ -> None)
	(* Instance method calls - use the method's return type *)
	(* Special case: specialized array methods return primitive types, not Null<T> *)
	| TCall ({ eexpr = TField (obj, FInstance (c, _, cf)) }, _) ->
		(* Check if this is a specialized array method that returns a primitive *)
		let obj_c_type = s_type ctx obj.etype in
		let is_int_array = obj_c_type = "FibIntArray*" in
		let is_float_array = obj_c_type = "FibFloatArray*" in
		let is_bool_array = obj_c_type = "FibBoolArray*" in
		let is_string = is_string_type obj.etype in
		let is_int_map = c.cl_path = (["haxe"; "ds"], "IntMap") in
		let is_string_map = c.cl_path = (["haxe"; "ds"], "StringMap") in
		let is_int64_map = c.cl_path = (["haxe"; "ds"], "Int64Map") in
		let is_object_map = c.cl_path = (["haxe"; "ds"], "ObjectMap") in
		(* Methods that return the element type (not Null<T>) for specialized arrays *)
		(match cf.cf_name with
		(* String methods that return int in C (not FibDynamic) *)
		| "charCodeAt" when is_string -> Some "int32_t"
		| "indexOf" | "lastIndexOf" when is_string -> Some "int32_t"
		| "pop" | "shift" | "__get" | "__unsafe_get" when is_int_array -> Some "int32_t"
		| "pop" | "shift" | "__get" | "__unsafe_get" when is_float_array -> Some "double"
		| "pop" | "shift" | "__get" | "__unsafe_get" when is_bool_array -> Some "bool"
		(* Map get methods return type-specialized values *)
		| "get" when is_int_map || is_string_map || is_int64_map ->
			(* Get the value type parameter from the map type *)
			(match follow obj.etype with
			| TInst (_, [t]) ->
				(match follow t with
				| TAbstract ({ a_path = ([], "Int") }, []) -> Some "int32_t"
				| TAbstract ({ a_path = ([], "Float") }, []) -> Some "double"
				| TInst ({ cl_path = ([], "String") }, []) -> Some "FibString*"
				| TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> Some "int64_t"
				| _ -> Some "FibDynamic")
			| _ -> Some "FibDynamic")
		(* ObjectMap.get returns type-specialized values based on second type parameter *)
		| "get" when is_object_map ->
			(match follow obj.etype with
			| TInst (_, [_; t]) ->  (* ObjectMap<K, V> has two type params, V is second *)
				(match follow t with
				| TAbstract ({ a_path = ([], "Int") }, []) -> Some "int32_t"
				| TAbstract ({ a_path = ([], "Float") }, []) -> Some "double"
				| TInst ({ cl_path = ([], "String") }, []) -> Some "FibString*"
				| TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> Some "int64_t"
				| _ -> Some "FibDynamic")
			| _ -> Some "FibDynamic")
		| _ ->
			(match follow cf.cf_type with
			| TFun (_, ret) -> Some (s_type ctx ret)
			| _ -> None))
	(* __fiberus__ calls return the expression's declared type (from inline function) *)
	| TCall ({ eexpr = TIdent "__fiberus__" }, _) ->
		Some (s_type ctx e.etype)
	(* Any function call - try to get return type from callee's type *)
	| TCall (callee, _) ->
		(match follow callee.etype with
		| TFun (_, ret) -> Some (s_type ctx ret)
		| _ -> None)
	| _ -> None

(* Check if a type is an enum *)
let is_enum_type t =
	match follow t with
	| TEnum _ -> true
	| _ -> false

(* Check if expression is a __fiberus__ call (produces raw C code with correct type) *)
let rec is_fiberus_call expr =
	match expr with
	| Some { eexpr = TCall ({ eexpr = TIdent "__fiberus__" }, _) } -> true
	| Some { eexpr = TCast (inner, _) } -> is_fiberus_call (Some inner)
	| Some { eexpr = TParenthesis inner } -> is_fiberus_call (Some inner)
	| Some { eexpr = TMeta (_, inner) } -> is_fiberus_call (Some inner)
	| _ -> false

(* Generate coercion wrapper if needed *)
let gen_coerce_with_expr ctx from_type to_type expr gen_inner =
	(* Compare C types directly *)
	let from_c = s_type ctx from_type in
	let to_c = s_type ctx to_type in
	(* Check for null expression being passed to FibDynamic *)
	let is_null_expr = match expr with
		| Some { eexpr = TConst TNull } -> true
		| _ -> false
	in
	(* Check for __fiberus__ calls - these produce raw C code with correct type *)
	let is_fiberus = is_fiberus_call expr in
	(* Handle null being passed to enum types - use default struct initializer *)
	if is_fiberus then
		(* __fiberus__ calls produce raw C with correct type, no coercion needed *)
		gen_inner ()
	else if is_null_expr && is_enum_type to_type then begin
		(* Enum types in fiberus are structs, so generate a struct initializer *)
		print ctx "((%s){ .index = 0 })" to_c;
		(* Don't call gen_inner - we've already generated the value *)
	end else if is_null_expr && to_c = "FibDynamic" then begin
		spr ctx "fib_dynamic_null()";
		(* Don't call gen_inner - we've already generated the value *)
	end else if is_null_expr && to_c = "int32_t" then begin
		(* null -> int defaults to 0 (for optional parameters) *)
		spr ctx "0";
	end else if is_null_expr && to_c = "double" then begin
		(* null -> float defaults to 0.0 *)
		spr ctx "0.0";
	end else if is_null_expr && to_c = "bool" then begin
		(* null -> bool defaults to false *)
		spr ctx "false";
	end else begin
	(* Determine actual C type based on expression kind *)
	let from_c = match expr with
		| Some e -> (match get_actual_c_type ctx e with
			| Some t -> t
			| None -> from_c)
		| None -> from_c
	in
	if from_c = to_c then
		gen_inner ()
	else if from_c = "FibDynamic" && to_c = "FibString*" then begin
		spr ctx "fib_dynamic_to_string(";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "FibDynamic" && to_c = "FibArray*" then begin
		spr ctx "fib_dynamic_to_array(";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "FibString*" && to_c = "FibDynamic" then begin
		spr ctx "fib_string_to_dynamic(";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "FibArray*" && to_c = "FibDynamic" then begin
		spr ctx "fib_dynamic_array(";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "int32_t" && to_c = "FibDynamic" then begin
		spr ctx "fib_dynamic_int(";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "double" && to_c = "FibDynamic" then begin
		spr ctx "fib_dynamic_float(";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "bool" && to_c = "FibDynamic" then begin
		spr ctx "fib_dynamic_bool(";
		gen_inner ();
		spr ctx ")"
	end else if is_class_pointer_type from_c && is_class_pointer_type to_c then begin
		(* Cast between class pointer types (subclass to parent class) *)
		print ctx "((%s)" to_c;
		gen_inner ();
		spr ctx ")"
	end else if is_class_pointer_type from_c && to_c = "FibDynamic" then begin
		spr ctx "fib_dynamic_object((FibObject*)";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "FibDynamic" && is_class_pointer_type to_c then begin
		(* Unwrap FibDynamic to class pointer *)
		print ctx "((%s)fib_dynamic_to_object(" to_c;
		gen_inner ();
		spr ctx "))"
	end else if from_c = "FibDynamic" && to_c = "double" then begin
		(* Unwrap FibDynamic to float *)
		spr ctx "fib_dynamic_to_float(";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "FibDynamic" && to_c = "int32_t" then begin
		(* Unwrap FibDynamic to int *)
		spr ctx "fib_dynamic_to_int(";
		gen_inner ();
		spr ctx ")"
	end else if from_c = "FibDynamic" && to_c = "bool" then begin
		(* Unwrap FibDynamic to bool *)
		spr ctx "fib_dynamic_to_bool(";
		gen_inner ();
		spr ctx ")"
	end else
		gen_inner ()
	end

let gen_coerce ctx from_type to_type gen_inner =
	gen_coerce_with_expr ctx from_type to_type None gen_inner

(* Get parameter types from a function type *)
let get_param_types t =
	match follow t with
	| TFun (args, _) -> List.map (fun (_, _, t) -> t) args
	| _ -> []

(* Collect free variables in an expression (variables referenced but not defined locally) *)
let collect_free_vars tf_args tf_expr =
	(* Variables defined as function parameters *)
	let bound = Hashtbl.create 10 in
	List.iter (fun (v, _) -> Hashtbl.add bound v.v_id ()) tf_args;
	(* Track locally defined variables *)
	let local = Hashtbl.create 10 in
	(* Free variables found *)
	let free = ref [] in
	let rec scan e =
		match e.eexpr with
		| TLocal v ->
			if not (Hashtbl.mem bound v.v_id) && not (Hashtbl.mem local v.v_id) then begin
				if not (List.exists (fun v2 -> v2.v_id = v.v_id) !free) then
					free := v :: !free
			end
		| TVar (v, eo) ->
			Hashtbl.add local v.v_id ();
			(match eo with Some e -> scan e | None -> ())
		| TTry (try_e, catches) ->
			(* Scan try block normally *)
			scan try_e;
			(* For each catch, the catch variable is local to that catch block only *)
			List.iter (fun (v, catch_e) ->
				(* Add catch var as local for scanning catch block *)
				Hashtbl.add local v.v_id ();
				scan catch_e;
				(* Remove it after - it's not visible outside the catch *)
				Hashtbl.remove local v.v_id
			) catches
		| TFunction f ->
			(* Scan nested function bodies too - we need to capture any variables
			   they use from our scope so we can pass them to the inner closure *)
			let inner_bound = Hashtbl.create 10 in
			List.iter (fun (v, _) -> Hashtbl.add inner_bound v.v_id ()) f.tf_args;
			let rec scan_inner e =
				match e.eexpr with
				| TLocal v ->
					(* Check if this var is free relative to outer function *)
					if not (Hashtbl.mem bound v.v_id) && not (Hashtbl.mem local v.v_id)
						&& not (Hashtbl.mem inner_bound v.v_id) then begin
						if not (List.exists (fun v2 -> v2.v_id = v.v_id) !free) then
							free := v :: !free
					end
				| TVar (v, eo) ->
					Hashtbl.add inner_bound v.v_id ();
					(match eo with Some e -> scan_inner e | None -> ())
				| TTry (try_e, catches) ->
					(* Handle try/catch in nested functions *)
					scan_inner try_e;
					List.iter (fun (v, catch_e) ->
						Hashtbl.add inner_bound v.v_id ();
						scan_inner catch_e;
						Hashtbl.remove inner_bound v.v_id
					) catches
				| TFunction f2 ->
					(* Recurse into deeper nested functions *)
					let inner2_bound = Hashtbl.create 10 in
					List.iter (fun (v, _) -> Hashtbl.add inner2_bound v.v_id ()) f2.tf_args;
					Type.iter (fun e -> scan_inner e) f2.tf_expr
				| _ ->
					Type.iter scan_inner e
			in
			scan_inner f.tf_expr
		| _ ->
			Type.iter scan e
	in
	scan tf_expr;
	!free

(* Generate function call arguments with type coercion - uses gen_value below *)
let rec gen_call_args ctx args param_types gen_value_fn =
	let rec loop args params =
		match args, params with
		| [], _ -> ()
		| [arg], param :: _ ->
			gen_coerce_with_expr ctx arg.etype param (Some arg) (fun () -> gen_value_fn ctx arg)
		| [arg], [] ->
			gen_value_fn ctx arg
		| arg :: rest, param :: prest ->
			gen_coerce_with_expr ctx arg.etype param (Some arg) (fun () -> gen_value_fn ctx arg);
			spr ctx ", ";
			loop rest prest
		| arg :: rest, [] ->
			gen_value_fn ctx arg;
			spr ctx ", ";
			loop rest []
	in
	loop args param_types

(*
 * ===========================================================================
 * Call Generation - Builtin Calls
 * ===========================================================================
 * Handles special calls: trace, __fiberus__, Std.is, Std.int, Std.string,
 * Fiber.spawn, etc. Returns true if the call was handled.
 *)

(* Helper to generate trace message as FibDynamic *)
and gen_trace_value ctx msg =
	let msg_type = s_type ctx msg.etype in
	if msg_type = "FibString*" then begin
		spr ctx "fib_string_to_dynamic(";
		gen_value ctx msg;
		spr ctx ")"
	end else if msg_type = "int32_t" then begin
		spr ctx "fib_dynamic_int(";
		gen_value ctx msg;
		spr ctx ")"
	end else if msg_type = "double" then begin
		spr ctx "fib_dynamic_float(";
		gen_value ctx msg;
		spr ctx ")"
	end else if msg_type = "bool" then begin
		spr ctx "fib_dynamic_bool(";
		gen_value ctx msg;
		spr ctx ")"
	end else if msg_type = "FibDynamic" then begin
		gen_value ctx msg
	end else begin
		(* Object or unknown type - convert to FibDynamic *)
		spr ctx "fib_dynamic_object((FibObject*)";
		gen_value ctx msg;
		spr ctx ")"
	end

(* Helper for Fiber.spawn closure capture - shared by spawn/spawnOn/spawnAny *)
and gen_fiber_spawn_closure ctx free_vars closure_name =
	List.iteri (fun i v ->
		print ctx "_fc->captures[%d] = " i;
		let vtype = s_type ctx v.v_type in
		if vtype = "int32_t" then
			print ctx "fib_dynamic_int(%s); " (ident v.v_name)
		else if vtype = "double" then
			print ctx "fib_dynamic_float(%s); " (ident v.v_name)
		else if vtype = "bool" then
			print ctx "fib_dynamic_bool(%s); " (ident v.v_name)
		else if vtype = "FibString*" then
			print ctx "fib_dynamic_string(%s); " (ident v.v_name)
		else
			print ctx "(FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=%s}; " (ident v.v_name)
	) free_vars

(* Extract closure info for Fiber.spawn patterns *)
and extract_closure_for_spawn ctx arg =
	match arg.eexpr with
	| TFunction f ->
		let free_vars = collect_free_vars f.tf_args f.tf_expr in
		let closure_name = Printf.sprintf "_closure_%d" ctx.closure_counter in
		ctx.closure_counter <- ctx.closure_counter + 1;
		if not ctx.in_closure_impl then
			ctx.closures <- (closure_name, f, free_vars) :: ctx.closures;
		Some (free_vars, closure_name)
	| _ -> None

(* Generate builtin calls - returns true if handled *)
and gen_builtin_call ctx e args =
	match e.eexpr, args with
	(* trace() -> haxe_Log_trace with position info *)
	| TIdent "__trace__", [msg; infos] ->
		spr ctx "haxe_Log_trace(";
		gen_trace_value ctx msg;
		spr ctx ", ";
		gen_value ctx infos;
		spr ctx ")";
		true
	| TField (_, FStatic ({ cl_path = (["haxe"], "Log") }, { cf_name = "trace" })), [msg; infos] ->
		spr ctx "haxe_Log_trace(";
		gen_trace_value ctx msg;
		spr ctx ", ";
		gen_value ctx infos;
		spr ctx ")";
		true
	(* __fiberus__("code") -> raw code emission *)
	| TIdent "__fiberus__", code_args ->
		List.iter (fun arg ->
			match arg.eexpr with
			| TConst (TString s) -> spr ctx s
			| _ -> gen_value ctx arg
		) code_args;
		true
	(* __fiberus_get_exception_stack() -> native stack array for CallStack *)
	| TIdent "__fiberus_get_exception_stack", [] ->
		spr ctx "fib_get_exception_stack_array()";
		true
	(* __fiberus_get_call_stack() -> native stack array for CallStack *)
	| TIdent "__fiberus_get_call_stack", [] ->
		spr ctx "fib_get_call_stack_array()";
		true
	(* Std.isOfType / Std.is -> instanceof check *)
	| TField (_, FStatic ({ cl_path = ([], "Std") }, { cf_name = ("isOfType" | "is") })), [v; t] ->
		(match t.eexpr with
		| TTypeExpr (TClassDecl c) ->
			(match c.cl_path with
			| ([], "String") ->
				spr ctx "fib_dynamic_is_string(";
				gen_value ctx v;
				spr ctx ")"
			| ([], "Array") ->
				spr ctx "fib_dynamic_is_array(";
				gen_value ctx v;
				spr ctx ")"
			| ([], "Int") | ([], "Float") | ([], "Bool") ->
				spr ctx "false"
			| _ when not (has_class_flag c CExtern) ->
				let target_class = flat_path c.cl_path in
				spr ctx "fib_object_instanceof((FibObject*)";
				gen_value ctx v;
				print ctx ", &%s_class)" target_class
			| _ ->
				spr ctx "false /* extern type check not supported */")
		| _ ->
			spr ctx "false /* dynamic type check not supported */");
		true
	(* Std.int -> cast to int *)
	| TField (_, FStatic ({ cl_path = ([], "Std") }, { cf_name = "int" })), [arg] ->
		spr ctx "((int32_t)(";
		gen_value ctx arg;
		spr ctx "))";
		true
	(* Std.string -> convert to string based on actual type *)
	| TField (_, FStatic ({ cl_path = ([], "Std") }, { cf_name = "string" })), [arg] ->
		let arg_type = match get_actual_c_type ctx arg with
			| Some t -> t
			| None -> s_type ctx arg.etype
		in
		if arg_type = "FibString*" || is_string_type arg.etype then
			gen_value ctx arg
		else if arg_type = "int32_t" then begin
			spr ctx "fib_string_from_int(";
			gen_value ctx arg;
			spr ctx ")"
		end else if arg_type = "double" || arg_type = "float" then begin
			spr ctx "fib_string_from_float(";
			gen_value ctx arg;
			spr ctx ")"
		end else if arg_type = "int64_t" then begin
			spr ctx "fib_string_from_int64(";
			gen_value ctx arg;
			spr ctx ")"
		end else if arg_type = "bool" then begin
			spr ctx "(";
			gen_value ctx arg;
			spr ctx " ? fib_string_new(\"true\") : fib_string_new(\"false\"))"
		end else begin
			spr ctx "fib_dynamic_to_string(";
			gen_value ctx arg;
			spr ctx ")"
		end;
		true
	(* Fiber.spawn with closure *)
	| TField (_, FStatic ({ cl_path = ([], "Fiber") }, { cf_name = "spawn" })), [arg] ->
		(match extract_closure_for_spawn ctx arg with
		| Some (free_vars, closure_name) ->
			(* Fiber spawn closures are never called dynamically, so pass impl for both fn and fn_dynamic *)
			let impl_name = closure_name ^ "_impl" in
			spr ctx "({ gc_mature_alloc_begin(); FibClosure* _fc = fib_closure_create_for_fiber((void*)";
			spr ctx impl_name;
			spr ctx ", (void*)";
			spr ctx closure_name;
			print ctx ", %d, 0); gc_push_temp_root((void**)&_fc); " (List.length free_vars);
			gen_fiber_spawn_closure ctx free_vars closure_name;
			spr ctx "Fiber* _fib = scheduler_spawn(_fib_spawn_closure_trampoline, (void*)_fc); ";
			spr ctx "gc_mature_alloc_end(); gc_pop_temp_roots(1); _fib; })"
		| None ->
			spr ctx "Fiber_spawn(";
			gen_value ctx arg;
			spr ctx ")");
		true
	(* Fiber.spawnOn with closure *)
	| TField (_, FStatic ({ cl_path = ([], "Fiber") }, { cf_name = "spawnOn" })), [thread_id; arg] ->
		(match extract_closure_for_spawn ctx arg with
		| Some (free_vars, closure_name) ->
			let impl_name = closure_name ^ "_impl" in
			spr ctx "({ int _tid = ";
			gen_value ctx thread_id;
			spr ctx "; gc_mature_alloc_begin(); FibClosure* _fc = fib_closure_create_for_fiber((void*)";
			spr ctx impl_name;
			spr ctx ", (void*)";
			spr ctx closure_name;
			print ctx ", %d, 0); gc_push_temp_root((void**)&_fc); " (List.length free_vars);
			gen_fiber_spawn_closure ctx free_vars closure_name;
			spr ctx "Fiber* _fib = scheduler_spawn_on(_tid, _fib_spawn_on_closure_trampoline, (void*)_fc); ";
			spr ctx "gc_mature_alloc_end(); gc_pop_temp_roots(1); _fib; })"
		| None ->
			spr ctx "Fiber_spawnOn(";
			gen_value ctx thread_id;
			spr ctx ", ";
			gen_value ctx arg;
			spr ctx ")");
		true
	(* Fiber.spawnAny with closure *)
	| TField (_, FStatic ({ cl_path = ([], "Fiber") }, { cf_name = "spawnAny" })), [arg] ->
		(match extract_closure_for_spawn ctx arg with
		| Some (free_vars, closure_name) ->
			let impl_name = closure_name ^ "_impl" in
			spr ctx "({ gc_mature_alloc_begin(); FibClosure* _fc = fib_closure_create_for_fiber((void*)";
			spr ctx impl_name;
			spr ctx ", (void*)";
			spr ctx closure_name;
			print ctx ", %d, 0); gc_push_temp_root((void**)&_fc); " (List.length free_vars);
			gen_fiber_spawn_closure ctx free_vars closure_name;
			spr ctx "Fiber* _fib = scheduler_spawn_any(_fib_spawn_on_closure_trampoline, (void*)_fc); ";
			spr ctx "gc_mature_alloc_end(); gc_pop_temp_roots(1); _fib; })"
		| None ->
			spr ctx "Fiber_spawnAny(";
			gen_value ctx arg;
			spr ctx ")");
		true
	(* Static method call: Class.method(args) -> Class_method(args) *)
	| TField (_, FStatic (c, cf)), _ ->
		print ctx "%s_%s(" (flat_path c.cl_path) (ident cf.cf_name);
		gen_call_args ctx args (get_param_types cf.cf_type) gen_value;
		spr ctx ")";
		true
	| _ -> false

(*
 * ===========================================================================
 * Call Generation - Array Method Calls
 * ===========================================================================
 * Handles Array<T> instance method calls. Returns true if handled.
 *)
and gen_array_call ctx arr cf args =
	(* Helper to generate array with coercion if needed *)
	let gen_array_value () =
		match get_actual_c_type ctx arr with
		| Some "FibDynamic" ->
			spr ctx "fib_dynamic_to_array(";
			gen_value ctx arr;
			spr ctx ")"
		| _ -> gen_value ctx arr
	in
	(* Get the specialized array prefix if applicable *)
	let arr_type = s_type ctx arr.etype in
	let is_int_arr = arr_type = "FibIntArray*" in
	let is_float_arr = arr_type = "FibFloatArray*" in
	let is_bool_arr = arr_type = "FibBoolArray*" in
	let is_uint8_arr = arr_type = "FibUInt8Array*" in
	let is_int64_arr = arr_type = "FibInt64Array*" in
	let is_uint64_arr = arr_type = "FibUInt64Array*" in
	let is_float32_arr = arr_type = "FibFloat32Array*" in
	let is_specialized = is_int_arr || is_float_arr || is_bool_arr ||
		is_uint8_arr || is_int64_arr || is_uint64_arr || is_float32_arr in
	let arr_prefix =
		if is_int_arr then "fib_int_array_"
		else if is_float_arr then "fib_float_array_"
		else if is_bool_arr then "fib_bool_array_"
		else if is_uint8_arr then "fib_uint8_array_"
		else if is_int64_arr then "fib_int64_array_"
		else if is_uint64_arr then "fib_uint64_array_"
		else if is_float32_arr then "fib_float32_array_"
		else "fib_array_"
	in
	match cf.cf_name with
	| "push" ->
		print ctx "%spush(" arr_prefix;
		gen_array_value ();
		spr ctx ", ";
		(match args with
		| [arg] ->
			if is_specialized then
				gen_value ctx arg
			else begin
				let arg_type = s_type ctx arg.etype in
				gen_box_to_fib_dynamic ctx arg_type (fun () -> gen_value ctx arg)
			end
		| _ -> ());
		spr ctx ")";
		true
	| "pop" ->
		print ctx "%spop(" arr_prefix;
		gen_array_value ();
		spr ctx ")";
		if not is_specialized then begin
			let elem_type = get_array_elem_type ctx arr.etype in
			spr ctx (fib_dynamic_unbox_suffix elem_type)
		end;
		true
	| "shift" ->
		print ctx "%sshift(" arr_prefix;
		gen_array_value ();
		spr ctx ")";
		if not is_specialized then begin
			let elem_type = get_array_elem_type ctx arr.etype in
			spr ctx (fib_dynamic_unbox_suffix elem_type)
		end;
		true
	| "unshift" ->
		print ctx "%sunshift(" arr_prefix;
		gen_array_value ();
		spr ctx ", ";
		(match args with [arg] -> gen_value ctx arg | _ -> ());
		spr ctx ")";
		true
	| "insert" ->
		print ctx "%sinsert(" arr_prefix;
		gen_array_value ();
		(match args with
		| [idx; val_] ->
			spr ctx ", ";
			gen_value ctx idx;
			spr ctx ", ";
			gen_value ctx val_
		| _ -> ());
		spr ctx ")";
		true
	| "remove" ->
		print ctx "%sremove(" arr_prefix;
		gen_array_value ();
		(match args with [idx] -> spr ctx ", "; gen_value ctx idx | _ -> ());
		spr ctx ")";
		true
	| "indexOf" ->
		print ctx "%sindex_of(" arr_prefix;
		gen_array_value ();
		spr ctx ", ";
		(match args with
		| [val_] -> gen_value ctx val_; spr ctx ", 0"
		| [val_; start] -> gen_value ctx val_; spr ctx ", "; gen_value ctx start
		| _ -> ());
		spr ctx ")";
		true
	| "contains" ->
		print ctx "%scontains(" arr_prefix;
		gen_array_value ();
		spr ctx ", ";
		(match args with [val_] -> gen_value ctx val_ | _ -> ());
		spr ctx ")";
		true
	| "reverse" ->
		print ctx "%sreverse(" arr_prefix;
		gen_array_value ();
		spr ctx ")";
		true
	| "slice" ->
		print ctx "%sslice(" arr_prefix;
		gen_array_value ();
		(match args with
		| [start] -> spr ctx ", "; gen_value ctx start; spr ctx ", -1"
		| [start; end_] -> spr ctx ", "; gen_value ctx start; spr ctx ", "; gen_value ctx end_
		| _ -> spr ctx ", 0, -1");
		spr ctx ")";
		true
	| "concat" ->
		print ctx "%sconcat(" arr_prefix;
		gen_array_value ();
		spr ctx ", ";
		(match args with [other] -> gen_value ctx other | _ -> ());
		spr ctx ")";
		true
	| "join" ->
		spr ctx "fib_array_join(";
		gen_array_value ();
		spr ctx ", ";
		(match args with
		| [sep] -> gen_value ctx sep
		| _ -> spr ctx "fib_string_new(\",\")");
		spr ctx ")";
		true
	| "iterator" ->
		spr ctx "fib_array_iterator(";
		gen_array_value ();
		spr ctx ")";
		true
	| _ ->
		(* Fallback to generic method call *)
		print ctx "Array_%s(" (ident cf.cf_name);
		gen_array_value ();
		if args <> [] then spr ctx ", ";
		gen_call_args ctx args (get_param_types cf.cf_type) gen_value;
		spr ctx ")";
		true

(*
 * ===========================================================================
 * Call Generation - String Method Calls
 * ===========================================================================
 * Handles String instance method calls. Returns true if handled.
 *)
and gen_string_call ctx str cf args =
	match cf.cf_name with
	| "charAt" ->
		spr ctx "fib_string_char_at_str(";
		gen_value ctx str;
		spr ctx ", ";
		(match args with [idx] -> gen_value ctx idx | _ -> spr ctx "0");
		spr ctx ")";
		true
	| "charCodeAt" ->
		spr ctx "fib_string_char_code_at(";
		gen_value ctx str;
		spr ctx ", ";
		(match args with [idx] -> gen_value ctx idx | _ -> spr ctx "0");
		spr ctx ")";
		true
	| "substring" | "substr" ->
		spr ctx "fib_string_substr(";
		gen_value ctx str;
		spr ctx ", ";
		(match args with
		| [start] -> gen_value ctx start; spr ctx ", -1"
		| [start; len] -> gen_value ctx start; spr ctx ", "; gen_value ctx len
		| _ -> spr ctx "0, -1");
		spr ctx ")";
		true
	| "indexOf" ->
		spr ctx "fib_string_index_of(";
		gen_value ctx str;
		spr ctx ", ";
		(match args with
		| [needle] -> gen_value ctx needle; spr ctx ", 0"
		| [needle; start] -> gen_value ctx needle; spr ctx ", "; gen_value ctx start
		| _ -> spr ctx "fib_string_new(\"\"), 0");
		spr ctx ")";
		true
	| "lastIndexOf" ->
		spr ctx "fib_string_last_index_of(";
		gen_value ctx str;
		spr ctx ", ";
		(match args with
		| [needle] -> gen_value ctx needle; spr ctx ", -1"
		| [needle; start] -> gen_value ctx needle; spr ctx ", "; gen_value ctx start
		| _ -> spr ctx "fib_string_new(\"\"), -1");
		spr ctx ")";
		true
	| "split" ->
		spr ctx "fib_string_split(";
		gen_value ctx str;
		spr ctx ", ";
		(match args with [delim] -> gen_value ctx delim | _ -> spr ctx "fib_string_new(\"\")");
		spr ctx ")";
		true
	| "toUpperCase" ->
		spr ctx "fib_string_to_upper(";
		gen_value ctx str;
		spr ctx ")";
		true
	| "toLowerCase" ->
		spr ctx "fib_string_to_lower(";
		gen_value ctx str;
		spr ctx ")";
		true
	| "trim" ->
		spr ctx "fib_string_trim(";
		gen_value ctx str;
		spr ctx ")";
		true
	| "length" ->
		spr ctx "fib_string_length(";
		gen_value ctx str;
		spr ctx ")";
		true
	| _ ->
		(* Fallback to generic method call *)
		print ctx "String_%s(" (ident cf.cf_name);
		gen_value ctx str;
		if args <> [] then spr ctx ", ";
		gen_call_args ctx args (get_param_types cf.cf_type) gen_value;
		spr ctx ")";
		true

(*
 * ===========================================================================
 * Call Generation - Map Method Calls (IntMap, StringMap, Int64Map, ObjectMap)
 * ===========================================================================
 * Handles Map instance method calls. Returns true if handled.
 *)

(* Helper to get value type suffix for map operations *)
and get_map_value_suffix ctx arg_expr =
	match follow arg_expr.etype with
	| TAbstract ({ a_path = ([], "Int") }, []) -> "_int"
	| TAbstract ({ a_path = ([], "Float") }, []) -> "_float"
	| TInst ({ cl_path = ([], "String") }, []) -> "_string"
	| TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "_int64"
	| _ -> "_dynamic"

(* Generate IntMap method call *)
and gen_int_map_call ctx map_expr cf args =
	let get_map_value_type () =
		match follow map_expr.etype with
		| TInst (_, [t]) -> follow t
		| _ -> t_dynamic
	in
	match cf.cf_name with
	| "set" ->
		(match args with
		| [key; value] ->
			let suffix = get_map_value_suffix ctx value in
			print ctx "fib_int_map_set%s(" suffix;
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ", ";
			gen_value ctx value;
			spr ctx ")"
		| _ -> spr ctx "/* IntMap.set: wrong args */");
		true
	| "get" ->
		(match args with
		| [key] ->
			let value_type = get_map_value_type () in
			let fn_name = match value_type with
				| TAbstract ({ a_path = ([], "Int") }, []) -> "fib_int_map_get_int"
				| TAbstract ({ a_path = ([], "Float") }, []) -> "fib_int_map_get_float"
				| TInst ({ cl_path = ([], "String") }, []) -> "fib_int_map_get_string"
				| _ -> "fib_int_map_get_dynamic"
			in
			print ctx "%s(" fn_name;
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* IntMap.get: wrong args */");
		true
	| "exists" ->
		(match args with
		| [key] ->
			spr ctx "fib_int_map_exists(";
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* IntMap.exists: wrong args */");
		true
	| "remove" ->
		(match args with
		| [key] ->
			spr ctx "fib_int_map_remove(";
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* IntMap.remove: wrong args */");
		true
	| "keys" -> spr ctx "fib_int_map_keys("; gen_value ctx map_expr; spr ctx ")"; true
	| "iterator" -> spr ctx "fib_int_map_iterator("; gen_value ctx map_expr; spr ctx ")"; true
	| "copy" -> spr ctx "fib_int_map_copy("; gen_value ctx map_expr; spr ctx ")"; true
	| "toString" -> spr ctx "fib_int_map_to_string("; gen_value ctx map_expr; spr ctx ")"; true
	| "clear" -> spr ctx "fib_int_map_clear("; gen_value ctx map_expr; spr ctx ")"; true
	| "size" -> spr ctx "fib_int_map_size("; gen_value ctx map_expr; spr ctx ")"; true
	| _ -> print ctx "/* IntMap.%s not implemented */" cf.cf_name; true

(* Generate StringMap method call *)
and gen_string_map_call ctx map_expr cf args =
	let get_map_value_type () =
		match follow map_expr.etype with
		| TInst (_, [t]) -> follow t
		| _ -> t_dynamic
	in
	match cf.cf_name with
	| "set" ->
		(match args with
		| [key; value] ->
			let suffix = get_map_value_suffix ctx value in
			print ctx "fib_string_map_set%s(" suffix;
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ", ";
			gen_value ctx value;
			spr ctx ")"
		| _ -> spr ctx "/* StringMap.set: wrong args */");
		true
	| "get" ->
		(match args with
		| [key] ->
			let value_type = get_map_value_type () in
			let fn_name = match value_type with
				| TAbstract ({ a_path = ([], "Int") }, []) -> "fib_string_map_get_int"
				| TAbstract ({ a_path = ([], "Float") }, []) -> "fib_string_map_get_float"
				| TInst ({ cl_path = ([], "String") }, []) -> "fib_string_map_get_string"
				| _ -> "fib_string_map_get_dynamic"
			in
			print ctx "%s(" fn_name;
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* StringMap.get: wrong args */");
		true
	| "exists" ->
		(match args with
		| [key] ->
			spr ctx "fib_string_map_exists(";
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* StringMap.exists: wrong args */");
		true
	| "remove" ->
		(match args with
		| [key] ->
			spr ctx "fib_string_map_remove(";
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* StringMap.remove: wrong args */");
		true
	| "keys" -> spr ctx "fib_string_map_keys("; gen_value ctx map_expr; spr ctx ")"; true
	| "iterator" -> spr ctx "fib_string_map_iterator("; gen_value ctx map_expr; spr ctx ")"; true
	| "copy" -> spr ctx "fib_string_map_copy("; gen_value ctx map_expr; spr ctx ")"; true
	| "toString" -> spr ctx "fib_string_map_to_string("; gen_value ctx map_expr; spr ctx ")"; true
	| "clear" -> spr ctx "fib_string_map_clear("; gen_value ctx map_expr; spr ctx ")"; true
	| "size" -> spr ctx "fib_string_map_size("; gen_value ctx map_expr; spr ctx ")"; true
	| _ -> print ctx "/* StringMap.%s not implemented */" cf.cf_name; true

(* Generate Int64Map method call *)
and gen_int64_map_call ctx map_expr cf args =
	let get_map_value_type () =
		match follow map_expr.etype with
		| TInst (_, [t]) -> follow t
		| _ -> t_dynamic
	in
	match cf.cf_name with
	| "set" ->
		(match args with
		| [key; value] ->
			let suffix = get_map_value_suffix ctx value in
			print ctx "fib_int64_map_set%s(" suffix;
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ", ";
			gen_value ctx value;
			spr ctx ")"
		| _ -> spr ctx "/* Int64Map.set: wrong args */");
		true
	| "get" ->
		(match args with
		| [key] ->
			let value_type = get_map_value_type () in
			let fn_name = match value_type with
				| TAbstract ({ a_path = ([], "Int") }, []) -> "fib_int64_map_get_int"
				| TAbstract ({ a_path = ([], "Float") }, []) -> "fib_int64_map_get_float"
				| TInst ({ cl_path = ([], "String") }, []) -> "fib_int64_map_get_string"
				| TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "fib_int64_map_get_int64"
				| _ -> "fib_int64_map_get_dynamic"
			in
			print ctx "%s(" fn_name;
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* Int64Map.get: wrong args */");
		true
	| "exists" ->
		(match args with
		| [key] ->
			spr ctx "fib_int64_map_exists(";
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* Int64Map.exists: wrong args */");
		true
	| "remove" ->
		(match args with
		| [key] ->
			spr ctx "fib_int64_map_remove(";
			gen_value ctx map_expr;
			spr ctx ", ";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* Int64Map.remove: wrong args */");
		true
	| "keys" -> spr ctx "fib_int64_map_keys("; gen_value ctx map_expr; spr ctx ")"; true
	| "iterator" -> spr ctx "fib_int64_map_iterator("; gen_value ctx map_expr; spr ctx ")"; true
	| "copy" -> spr ctx "fib_int64_map_copy("; gen_value ctx map_expr; spr ctx ")"; true
	| "toString" -> spr ctx "fib_int64_map_to_string("; gen_value ctx map_expr; spr ctx ")"; true
	| "clear" -> spr ctx "fib_int64_map_clear("; gen_value ctx map_expr; spr ctx ")"; true
	| "size" -> spr ctx "fib_int64_map_size("; gen_value ctx map_expr; spr ctx ")"; true
	| _ -> print ctx "/* Int64Map.%s not implemented */" cf.cf_name; true

(* Generate ObjectMap method call *)
and gen_object_map_call ctx map_expr cf args =
	let get_map_value_type () =
		match follow map_expr.etype with
		| TInst (_, [_; t]) -> follow t  (* Second type param is value type *)
		| _ -> t_dynamic
	in
	match cf.cf_name with
	| "set" ->
		(match args with
		| [key; value] ->
			let suffix = get_map_value_suffix ctx value in
			print ctx "fib_object_map_set%s(" suffix;
			gen_value ctx map_expr;
			spr ctx ", (FibObject*)";
			gen_value ctx key;
			spr ctx ", ";
			gen_value ctx value;
			spr ctx ")"
		| _ -> spr ctx "/* ObjectMap.set: wrong args */");
		true
	| "get" ->
		(match args with
		| [key] ->
			let value_type = get_map_value_type () in
			let fn_name = match value_type with
				| TAbstract ({ a_path = ([], "Int") }, []) -> "fib_object_map_get_int"
				| TAbstract ({ a_path = ([], "Float") }, []) -> "fib_object_map_get_float"
				| TInst ({ cl_path = ([], "String") }, []) -> "fib_object_map_get_string"
				| TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "fib_object_map_get_int64"
				| _ -> "fib_object_map_get_dynamic"
			in
			print ctx "%s(" fn_name;
			gen_value ctx map_expr;
			spr ctx ", (FibObject*)";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* ObjectMap.get: wrong args */");
		true
	| "exists" ->
		(match args with
		| [key] ->
			spr ctx "fib_object_map_exists(";
			gen_value ctx map_expr;
			spr ctx ", (FibObject*)";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* ObjectMap.exists: wrong args */");
		true
	| "remove" ->
		(match args with
		| [key] ->
			spr ctx "fib_object_map_remove(";
			gen_value ctx map_expr;
			spr ctx ", (FibObject*)";
			gen_value ctx key;
			spr ctx ")"
		| _ -> spr ctx "/* ObjectMap.remove: wrong args */");
		true
	| "keys" -> spr ctx "fib_object_map_keys("; gen_value ctx map_expr; spr ctx ")"; true
	| "iterator" -> spr ctx "fib_object_map_iterator("; gen_value ctx map_expr; spr ctx ")"; true
	| "copy" -> spr ctx "fib_object_map_copy("; gen_value ctx map_expr; spr ctx ")"; true
	| "toString" -> spr ctx "fib_object_map_to_string("; gen_value ctx map_expr; spr ctx ")"; true
	| "clear" -> spr ctx "fib_object_map_clear("; gen_value ctx map_expr; spr ctx ")"; true
	| "size" -> spr ctx "fib_object_map_size("; gen_value ctx map_expr; spr ctx ")"; true
	| _ -> print ctx "/* ObjectMap.%s not implemented */" cf.cf_name; true

(*
 * ===========================================================================
 * Call Generation - Instance Method Calls
 * ===========================================================================
 * Handles instance method calls on objects.
 * Uses virtual dispatch via vtable when:
 * - The receiver type is different from the declaring class (polymorphism)
 * - The method is declared in a base class or interface
 * - The declaring class IS an interface (interfaces have no implementation)
 *)
and gen_instance_call ctx obj c cf args =
	let class_name = flat_path c.cl_path in
	let obj_type = s_type ctx obj.etype in
	(* Check if the declaring class is an interface *)
	let is_interface_call = GenfiberusVtable.is_interface c in
	(* Determine if we need virtual dispatch *)
	let needs_vtable = match ctx.vtable_ctx with
		| Some vctx ->
			if is_interface_call then
				(* Interface calls ALWAYS need vtable dispatch *)
				true
			else begin
				(* Check if this is a virtual method and receiver type differs *)
				let receiver_class = match follow obj.etype with
					| TInst (rc, _) -> Some rc
					| _ -> None
				in
				match receiver_class with
				| Some rc when rc.cl_path <> c.cl_path ->
					(* Receiver type differs - need virtual dispatch if method is virtual *)
					GenfiberusVtable.needs_virtual_dispatch c cf &&
					(match GenfiberusVtable.get_vtable_slot vctx c cf with
					| Some _ -> true
					| None -> false)
				| _ -> false  (* Same type or non-class receiver - static dispatch *)
			end
		| None -> false
	in
	if needs_vtable then begin
		(* Virtual dispatch via vtable *)
		(* For interfaces, use interface slot; for classes, use class vtable slot *)
		let slot_index = match ctx.vtable_ctx with
			| Some vctx ->
				if is_interface_call then
					GenfiberusVtable.get_interface_slot vctx c cf
				else
					(match GenfiberusVtable.get_vtable_slot vctx c cf with
					| Some info -> Some info.slot_index
					| None -> None)
			| None -> None
		in
		(* Get method signature for type cast *)
		let (arg_types, ret_type) = GenfiberusVtable.get_method_types cf in
		match slot_index with
		| Some slot ->
			(* Generate vtable call with function pointer cast *)
			let ret_str = s_type ctx ret_type in
			(* For interface calls, use FibObject* as this type since we don't know the concrete class *)
			let this_type = if is_interface_call then "FibObject*" else Printf.sprintf "%s*" class_name in
			let arg_strs = List.map (fun t -> s_type ctx t) arg_types in
			let all_arg_types = this_type :: arg_strs in
			let args_str = String.concat ", " all_arg_types in
			(* Function pointer cast *)
			print ctx "((%s (*)(%s))" ret_str args_str;
			(* Vtable lookup - cast to FibObject* to access clazz member *)
			spr ctx "((FibObject*)(";
			gen_value ctx obj;
			print ctx "))->clazz->vtable[%d])(" slot;
			(* Object argument - for interface calls, cast to FibObject* *)
			if is_interface_call then begin
				spr ctx "(FibObject*)";
				gen_value ctx obj
			end else if obj_type <> class_name ^ "*" then begin
				print ctx "((%s*)" class_name;
				gen_value ctx obj;
				spr ctx ")"
			end else
				gen_value ctx obj;
			(* Method arguments *)
			if args <> [] then spr ctx ", ";
			gen_call_args ctx args (get_param_types cf.cf_type) gen_value;
			spr ctx ")"
		| None ->
			(* Fallback to static dispatch - should not happen for interfaces *)
			if is_interface_call then
				print ctx "/* ERROR: Interface method %s has no vtable slot */" cf.cf_name
			else begin
				print ctx "%s_%s(" class_name (ident cf.cf_name);
				if obj_type <> class_name ^ "*" then begin
					print ctx "((%s*)" class_name;
					gen_value ctx obj;
					spr ctx ")"
				end else
					gen_value ctx obj;
				if args <> [] then spr ctx ", ";
				gen_call_args ctx args (get_param_types cf.cf_type) gen_value;
				spr ctx ")"
			end
	end else begin
		(* Static dispatch - direct function call *)
		print ctx "%s_%s(" class_name (ident cf.cf_name);
		(* Cast object to the declaring class type if different *)
		if obj_type <> class_name ^ "*" then begin
			print ctx "((%s*)" class_name;
			gen_value ctx obj;
			spr ctx ")"
		end else
			gen_value ctx obj;
		if args <> [] then spr ctx ", ";
		gen_call_args ctx args (get_param_types cf.cf_type) gen_value;
		spr ctx ")"
	end

(*
 * ===========================================================================
 * Call Generation - Main Entry Point
 * ===========================================================================
 *)
and gen_call ctx e args =
	(* First try builtin calls *)
	if gen_builtin_call ctx e args then ()
	else match e.eexpr, args with
	(* Array method calls -> fib_array_* functions *)
	| TField (arr, FInstance (_, _, cf)), _ when is_array_type arr.etype ->
		ignore (gen_array_call ctx arr cf args)
	(* String method calls -> fib_string_* functions *)
	| TField (str, FInstance (_, _, cf)), _ when is_string_type str.etype ->
		ignore (gen_string_call ctx str cf args)
	(* IntMap method calls *)
	| TField (map_expr, FInstance (c, _, cf)), _ when c.cl_path = (["haxe"; "ds"], "IntMap") ->
		ignore (gen_int_map_call ctx map_expr cf args)
	(* StringMap method calls *)
	| TField (map_expr, FInstance (c, _, cf)), _ when c.cl_path = (["haxe"; "ds"], "StringMap") ->
		ignore (gen_string_map_call ctx map_expr cf args)
	(* Int64Map method calls *)
	| TField (map_expr, FInstance (c, _, cf)), _ when c.cl_path = (["haxe"; "ds"], "Int64Map") ->
		ignore (gen_int64_map_call ctx map_expr cf args)
	(* ObjectMap method calls *)
	| TField (map_expr, FInstance (c, _, cf)), _ when c.cl_path = (["haxe"; "ds"], "ObjectMap") ->
		ignore (gen_object_map_call ctx map_expr cf args)
	(* Enum constructor call: Color.Rgb(r, g, b) -> Enum_Constructor(r, g, b) *)
	| TField (_, FEnum (en, ef)), _ ->
		print ctx "%s_%s(" (flat_path en.e_path) ef.ef_name;
		let param_types = match ef.ef_type with
			| TFun (args, _) -> List.map (fun (_, _, t) -> t) args
			| _ -> []
		in
		gen_call_args ctx args param_types gen_value;
		spr ctx ")"
	(* Instance method call: obj.method(args) -> Class_method(obj, args) *)
	| TField (obj, FInstance (c, _, cf)), _ ->
		gen_instance_call ctx obj c cf args
	(* Closure call *)
	| TField (obj, FClosure (Some (c, _), cf)), _ ->
		gen_instance_call ctx obj c cf args
	(* Super constructor call: super(args) calls ParentClass_init on this *)
	| TConst TSuper, _ ->
		(match ctx.current_class with
		| Some c ->
			(match c.cl_super with
			| Some (parent_c, _) ->
				print ctx "%s_init((%s*)this" (flat_path parent_c.cl_path) (flat_path parent_c.cl_path);
				if args <> [] then spr ctx ", ";
				let param_types = match parent_c.cl_constructor with
					| Some cf -> get_param_types cf.cf_type
					| None -> []
				in
				gen_call_args ctx args param_types gen_value;
				spr ctx ")"
			| None ->
				spr ctx "/* super() with no parent class */")
		| None ->
			spr ctx "/* super() outside of class context */")
	(* Dynamic method call: obj.method() where obj is Dynamic *)
	| TField (obj, FAnon cf), _ ->
		(match cf.cf_name with
		| "toString" ->
			spr ctx "fib_dynamic_to_string(";
			gen_value ctx obj;
			spr ctx ")"
		| "push" | "pop" | "shift" | "unshift" | "slice" | "concat" | "join" | "indexOf" | "contains" | "reverse" ->
			spr ctx "fib_array_";
			spr ctx cf.cf_name;
			spr ctx "(fib_dynamic_to_array(";
			gen_value ctx obj;
			spr ctx ")";
			if args <> [] then begin
				spr ctx ", ";
				List.iter (fun arg -> gen_value ctx arg) args
			end;
			spr ctx ")"
		| _ ->
			spr ctx "fib_call_method(";
			gen_value ctx obj;
			print ctx ", \"%s\"" cf.cf_name;
			if args <> [] then begin
				spr ctx ", ";
				print ctx "%d" (List.length args);
				List.iter (fun arg -> spr ctx ", "; gen_value ctx arg) args
			end else
				spr ctx ", 0";
			spr ctx ")")
	| TField (obj, FDynamic name), _ ->
		(match name with
		| "toString" ->
			spr ctx "fib_dynamic_to_string(";
			gen_value ctx obj;
			spr ctx ")"
		| _ ->
			spr ctx "fib_call_method(";
			gen_value ctx obj;
			print ctx ", \"%s\"" name;
			if args <> [] then begin
				spr ctx ", ";
				print ctx "%d" (List.length args);
				List.iter (fun arg -> spr ctx ", "; gen_value ctx arg) args
			end else
				spr ctx ", 0";
			spr ctx ")")
	(* Local variable call - could be a closure *)
	| TLocal v, _ ->
		(match follow v.v_type with
		| TFun (fun_args, ret) ->
			let arg_types = List.map (fun (_, _, t) -> s_type ctx t) fun_args in
			let args_str = if arg_types = [] then "" else String.concat ", " arg_types in
			let cast_str = s_func_ptr_cast ctx ret args_str in
			print ctx "(%s%s->fn)(%s" cast_str (ident v.v_name) (ident v.v_name);
			if args <> [] then spr ctx ", ";
			gen_call_args ctx args (get_param_types v.v_type) gen_value;
			spr ctx ")"
		| TDynamic _ ->
			(* Dynamic local variable call: use fib_closure_call_dynamic to handle optional params *)
			let num_args = List.length args in
			spr ctx "({ FibClosure* _dc = (FibClosure*)fib_dynamic_to_object(";
			spr ctx (ident v.v_name);
			spr ctx "); FibDynamic _args[";
			print ctx "%d" (max 1 num_args);
			spr ctx "] = {";
			let first = ref true in
			List.iter (fun arg ->
				if not !first then spr ctx ", " else first := false;
				match arg.eexpr with
				| TConst TNull -> spr ctx "fib_dynamic_null()"
				| _ ->
					let arg_type = s_type ctx arg.etype in
					if arg_type = "FibDynamic" then
						gen_value ctx arg
					else
						gen_box_to_fib_dynamic ctx arg_type (fun () -> gen_value ctx arg)
			) args;
			if num_args = 0 then spr ctx "fib_dynamic_null()";  (* Empty initializer not allowed *)
			print ctx "}; fib_closure_call_dynamic(_dc, _args, %d); })" num_args
		| _ ->
			gen_value ctx e;
			spr ctx "(";
			gen_call_args ctx args (get_param_types e.etype) gen_value;
			spr ctx ")")
	| _ ->
		(* Check if callee is a function type (TFun) - treat as closure call *)
		(match follow e.etype with
		| TFun (fun_args, ret) ->
			(* Closure call: ((cast)closure->fn)(closure, args) *)
			let arg_types = List.map (fun (_, _, t) -> s_type ctx t) fun_args in
			let args_str = if arg_types = [] then "" else String.concat ", " arg_types in
			let cast_str = s_func_ptr_cast ctx ret args_str in
			spr ctx "(";
			print ctx "%s" cast_str;
			gen_value ctx e;
			spr ctx "->fn)(";
			gen_value ctx e;  (* Pass closure as first arg *)
			if args <> [] then spr ctx ", ";
			gen_call_args ctx args (get_param_types e.etype) gen_value;
			spr ctx ")"
		| TDynamic _ ->
			(* Dynamic call: use fib_closure_call_dynamic to handle optional params *)
			let num_args = List.length args in
			spr ctx "({ FibClosure* _dc = (FibClosure*)fib_dynamic_to_object(";
			gen_value ctx e;
			spr ctx "); FibDynamic _args[";
			print ctx "%d" (max 1 num_args);
			spr ctx "] = {";
			let first = ref true in
			List.iter (fun arg ->
				if not !first then spr ctx ", " else first := false;
				match arg.eexpr with
				| TConst TNull -> spr ctx "fib_dynamic_null()"
				| _ ->
					let arg_type = s_type ctx arg.etype in
					if arg_type = "FibDynamic" then
						gen_value ctx arg
					else
						gen_box_to_fib_dynamic ctx arg_type (fun () -> gen_value ctx arg)
			) args;
			if num_args = 0 then spr ctx "fib_dynamic_null()";
			print ctx "}; fib_closure_call_dynamic(_dc, _args, %d); })" num_args
		| _ ->
			(* Regular call (unlikely to hit this case for well-typed code) *)
			gen_value ctx e;
			spr ctx "(";
			gen_call_args ctx args (get_param_types e.etype) gen_value;
			spr ctx ")")

and gen_value ctx e =
	match e.eexpr with
	| TConst c ->
		gen_constant ctx c
	| TLocal v ->
		spr ctx (ident v.v_name)
	| TArray (e1, e2) ->
		(* Unbox array element based on expected type *)
		let elem_type = s_type ctx e.etype in
		(* Check if array expr is Dynamic/FibDynamic and needs conversion *)
		let arr_type = match get_actual_c_type ctx e1 with
			| Some t -> t
			| None -> s_type ctx e1.etype
		in
		let gen_arr () =
			if arr_type = "FibDynamic" then begin
				spr ctx "fib_dynamic_to_array(";
				gen_value ctx e1;
				spr ctx ")"
			end else
				gen_value ctx e1
		in
		(* Check for specialized array types *)
		if arr_type = "FibIntArray*" then begin
			(* Specialized int array - direct access *)
			spr ctx "fib_int_array_get(";
			gen_value ctx e1;
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ")"
		end else if arr_type = "FibFloatArray*" then begin
			(* Specialized float array - direct access *)
			spr ctx "fib_float_array_get(";
			gen_value ctx e1;
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ")"
		end else if arr_type = "FibBoolArray*" then begin
			(* Specialized bool array - direct access *)
			spr ctx "fib_bool_array_get(";
			gen_value ctx e1;
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ")"
		end else if arr_type = "FibUInt8Array*" then begin
			(* Specialized uint8 array - direct access *)
			spr ctx "fib_uint8_array_get(";
			gen_value ctx e1;
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ")"
		end else if arr_type = "FibInt64Array*" then begin
			(* Specialized int64 array - direct access *)
			spr ctx "fib_int64_array_get(";
			gen_value ctx e1;
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ")"
		end else if arr_type = "FibUInt64Array*" then begin
			(* Specialized uint64 array - direct access *)
			spr ctx "fib_uint64_array_get(";
			gen_value ctx e1;
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ")"
		end else if arr_type = "FibFloat32Array*" then begin
			(* Specialized float32 array - direct access *)
			spr ctx "fib_float32_array_get(";
			gen_value ctx e1;
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ")"
		end else if is_class_pointer_type elem_type then begin
			(* Object types - unwrap and cast to expected type *)
			(* Extra parens ensure cast binds correctly for subsequent field access *)
			spr ctx "((";
			spr ctx elem_type;
			spr ctx ")fib_array_get(";
			gen_arr ();
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ").data.objectVal)"
		end else begin
			(* Generic array access - unbox based on element type *)
			spr ctx "fib_array_get(";
			gen_arr ();
			spr ctx ", ";
			gen_value ctx e2;
			spr ctx ")";
			spr ctx (fib_dynamic_unbox_suffix elem_type)
		end
	| TBinop (op, e1, e2) ->
		(* Handle string concatenation specially *)
		let is_str = is_string_type e.etype || is_string_type e1.etype || is_string_type e2.etype in
		(* Handle null comparisons for FibDynamic (which is a struct) *)
		let is_null_compare = match e1.eexpr, e2.eexpr with
			| TConst TNull, _ | _, TConst TNull -> true
			| _ -> false
		in
		let is_fib_dynamic_expr e =
			let t = e.etype in
			match follow t with
			| TDynamic _ | TAnon _ -> true
			| TMono { tm_type = None } -> true
			| TEnum _ -> true  (* Enum types use sentinel for null *)
			| TAbstract (a, tl) ->
				(* Check underlying type for abstracts like Any or Null<primitive> *)
				(match a.a_path with
				| ([], "Null") ->
					(* Null<primitive> is FibDynamic *)
					(match tl with
					| [inner] ->
						(match follow inner with
						| TAbstract ({ a_path = ([], ("Int" | "Float" | "Bool")) }, []) -> true
						| _ -> false)
					| _ -> false)
				| _ ->
					(match Abstract.get_underlying_type a tl with
					| TDynamic _ -> true
					| _ -> false))
			| _ -> match e.eexpr with
				| TField (_, FAnon _) | TField (_, FDynamic _) -> true
				| TEnumParameter _ -> true
				| _ -> false
		in
		(* Check if expression is an enum struct type that's NOT from dynamic access *)
		let rec is_dynamic_field_access e = match e.eexpr with
			| TField (_, FAnon _) | TField (_, FDynamic _) -> true
			| TCast (inner, _) | TMeta (_, inner) | TParenthesis inner -> is_dynamic_field_access inner
			| _ -> false
		in
		let is_enum_struct_expr e =
			(* Don't consider null constant as enum struct *)
			match e.eexpr with
			| TConst TNull -> false
			| _ ->
				match follow e.etype with
				| TEnum _ -> not (is_dynamic_field_access e)  (* Only use sentinel if not from dynamic access *)
				| _ -> false
		in
		let enum_null_check = is_null_compare && (is_enum_struct_expr e1 || is_enum_struct_expr e2) in
		(* Enum struct vs enum struct comparison (not null) - compare by .index *)
		let enum_struct_compare = (not is_null_compare) && is_enum_struct_expr e1 && is_enum_struct_expr e2 in
		let needs_null_func = is_null_compare && (is_fib_dynamic_expr e1 || is_fib_dynamic_expr e2) && not enum_null_check in
		(* Generate raw FibDynamic for enum parameters (without unboxing) *)
		let rec gen_raw_fib_dynamic e = match e.eexpr with
			| TEnumParameter (enum_e, _, i) ->
				gen_value ctx enum_e;
				print ctx ".params[%d]" i
			| TCast (inner, _) | TMeta (_, inner) | TParenthesis inner ->
				gen_raw_fib_dynamic inner
			| _ -> gen_value ctx e
		in
		(match op, is_str, enum_null_check, needs_null_func, enum_struct_compare with
		| OpEq, _, true, _, _ ->
			(* Enum struct == null -> check .index == -1 (sentinel) *)
			spr ctx "(";
			(match e1.eexpr with TConst TNull -> gen_value ctx e2 | _ -> gen_value ctx e1);
			spr ctx ".index == -1)"
		| OpNotEq, _, true, _, _ ->
			(* Enum struct != null -> check .index != -1 *)
			spr ctx "(";
			(match e1.eexpr with TConst TNull -> gen_value ctx e2 | _ -> gen_value ctx e1);
			spr ctx ".index != -1)"
		| OpEq, _, _, _, true ->
			(* Enum struct == enum struct -> compare by .index *)
			spr ctx "(";
			gen_value ctx e1;
			spr ctx ".index == ";
			gen_value ctx e2;
			spr ctx ".index)"
		| OpNotEq, _, _, _, true ->
			(* Enum struct != enum struct -> compare by .index *)
			spr ctx "(";
			gen_value ctx e1;
			spr ctx ".index != ";
			gen_value ctx e2;
			spr ctx ".index)"
		| OpEq, _, _, true, _ ->
			(* FibDynamic == null -> fib_dynamic_is_null() *)
			spr ctx "fib_dynamic_is_null(";
			(match e1.eexpr with TConst TNull -> gen_raw_fib_dynamic e2 | _ -> gen_raw_fib_dynamic e1);
			spr ctx ")"
		| OpNotEq, _, _, true, _ ->
			(* FibDynamic != null -> !fib_dynamic_is_null() *)
			spr ctx "!fib_dynamic_is_null(";
			(match e1.eexpr with TConst TNull -> gen_raw_fib_dynamic e2 | _ -> gen_raw_fib_dynamic e1);
			spr ctx ")"
		| OpAdd, true, _, _, _ ->
			(* String concat - coerce operands to FibString* if needed *)
			let gen_str_arg e =
				(* First check actual C type from function call return types *)
				let actual_type = get_actual_c_type ctx e in
				let c_type = s_type ctx e.etype in
				(* Check for dynamic field access which returns FibDynamic *)
				let is_dynamic = match e.eexpr with
					| TField (_, FAnon _) | TField (_, FDynamic _) -> true
					| _ -> false
				in
				(* Check if expression is a call that returns String *)
				let rec is_string_returning_call e = match e.eexpr with
					| TCall ({ eexpr = TField (_, FStatic (_, cf)) }, _) ->
						is_string_type cf.cf_type || (match follow cf.cf_type with TFun (_, ret) -> is_string_type ret | _ -> false)
					| TCall ({ eexpr = TField (_, FInstance (_, _, cf)) }, _) ->
						is_string_type cf.cf_type || (match follow cf.cf_type with TFun (_, ret) -> is_string_type ret | _ -> false)
					| TCall (callee, _) ->
						(* Fallback: check callee's type for function returning String *)
						(match follow callee.etype with TFun (_, ret) -> is_string_type ret | _ -> false)
					| TParenthesis inner | TCast (inner, _) | TMeta (_, inner) ->
						is_string_returning_call inner
					| TBlock exprs when exprs <> [] ->
						(* Check last expression in block *)
						is_string_returning_call (List.hd (List.rev exprs))
					| _ -> false
				in
				let is_string_call = is_string_returning_call e in
				(* Also check if the Haxe type is String - covers generic params and inlined calls *)
				let is_haxe_string = is_string_type e.etype in
				(* Use actual type if available, otherwise use declared type *)
				let effective_type = match actual_type with
					| Some t -> t
					| None -> c_type
				in
				(* Check if the expression looks like an array element access that produces a primitive *)
				let check_array_elem_type () =
					match e.eexpr with
					| TArray (arr, _) -> get_array_elem_type ctx arr.etype
					| _ -> effective_type
				in
				let resolved_type = check_array_elem_type () in
				(* Dynamic field access always returns FibDynamic in C, must convert first *)
				if is_dynamic then begin
					spr ctx "fib_dynamic_to_string("; gen_value ctx e; spr ctx ")"
				end else if is_string_call || is_haxe_string || effective_type = "FibString*" then
					gen_value ctx e
				else if resolved_type = "int32_t" then begin
					spr ctx "fib_string_from_int("; gen_value ctx e; spr ctx ")"
				end else if resolved_type = "double" || resolved_type = "float" then begin
					(* Handle both double and float (Float32) *)
					spr ctx "fib_string_from_float("; gen_value ctx e; spr ctx ")"
				end else if resolved_type = "int64_t" then begin
					spr ctx "fib_string_from_int64("; gen_value ctx e; spr ctx ")"
				end else if resolved_type = "bool" then begin
					spr ctx "("; gen_value ctx e; spr ctx " ? fib_string_new(\"true\") : fib_string_new(\"false\"))"
				end else if effective_type = "FibDynamic" || resolved_type = "FibDynamic" then begin
					spr ctx "fib_dynamic_to_string("; gen_value ctx e; spr ctx ")"
				end else
					(* Unknown type - just gen_value, will error if wrong *)
					gen_value ctx e
			in
			spr ctx "fib_string_concat(";
			gen_str_arg e1;
			spr ctx ", ";
			gen_str_arg e2;
			spr ctx ")"
		| OpAssignOp OpAdd, true, _, _, _ ->
			let gen_str_arg e =
				(* First check actual C type from function call return types *)
				let actual_type = get_actual_c_type ctx e in
				let c_type = s_type ctx e.etype in
				(* Check for dynamic field access which returns FibDynamic *)
				let is_dynamic = match e.eexpr with
					| TField (_, FAnon _) | TField (_, FDynamic _) -> true
					| _ -> false
				in
				(* Check if expression is a call that returns String *)
				let rec is_string_returning_call e = match e.eexpr with
					| TCall ({ eexpr = TField (_, FStatic (_, cf)) }, _) ->
						is_string_type cf.cf_type || (match follow cf.cf_type with TFun (_, ret) -> is_string_type ret | _ -> false)
					| TCall ({ eexpr = TField (_, FInstance (_, _, cf)) }, _) ->
						is_string_type cf.cf_type || (match follow cf.cf_type with TFun (_, ret) -> is_string_type ret | _ -> false)
					| TCall (callee, _) ->
						(* Fallback: check callee's type for function returning String *)
						(match follow callee.etype with TFun (_, ret) -> is_string_type ret | _ -> false)
					| TParenthesis inner | TCast (inner, _) | TMeta (_, inner) ->
						is_string_returning_call inner
					| TBlock exprs when exprs <> [] ->
						(* Check last expression in block *)
						is_string_returning_call (List.hd (List.rev exprs))
					| _ -> false
				in
				let is_string_call = is_string_returning_call e in
				(* Also check if the Haxe type is String *)
				let is_haxe_string = is_string_type e.etype in
				(* Use actual type if available, otherwise use declared type *)
				let effective_type = match actual_type with
					| Some t -> t
					| None -> c_type
				in
				(* Dynamic field access always returns FibDynamic in C, must convert first *)
				if is_dynamic then begin
					spr ctx "fib_dynamic_to_string("; gen_value ctx e; spr ctx ")"
				end else if is_string_call || is_haxe_string || effective_type = "FibString*" then
					gen_value ctx e
				else if effective_type = "FibDynamic" then begin
					spr ctx "fib_dynamic_to_string("; gen_value ctx e; spr ctx ")"
				end else if effective_type = "int32_t" then begin
					spr ctx "fib_string_from_int("; gen_value ctx e; spr ctx ")"
				end else if effective_type = "double" || effective_type = "float" then begin
					(* Handle both double and float (Float32) *)
					spr ctx "fib_string_from_float("; gen_value ctx e; spr ctx ")"
				end else if effective_type = "int64_t" then begin
					spr ctx "fib_string_from_int64("; gen_value ctx e; spr ctx ")"
				end else if effective_type = "bool" then begin
					spr ctx "("; gen_value ctx e; spr ctx " ? fib_string_new(\"true\") : fib_string_new(\"false\"))"
				end else
					gen_value ctx e
			in
			spr ctx "(";
			gen_value ctx e1;
			spr ctx " = fib_string_concat(";
			gen_str_arg e1;
			spr ctx ", ";
			gen_str_arg e2;
			spr ctx "))"
		| OpEq, true, _, _, _ ->
			(* Convert FibDynamic to FibString* for string comparison *)
			let gen_str_cmp_arg e =
				let needs_convert = match e.eexpr with
					| TField (_, FAnon _) | TField (_, FDynamic _) -> true
					| _ -> s_type ctx e.etype = "FibDynamic"
				in
				if needs_convert then begin
					spr ctx "fib_dynamic_to_string("; gen_value ctx e; spr ctx ")"
				end else
					gen_value ctx e
			in
			spr ctx "fib_string_eq(";
			gen_str_cmp_arg e1;
			spr ctx ", ";
			gen_str_cmp_arg e2;
			spr ctx ")"
		| OpNotEq, true, _, _, _ ->
			let gen_str_cmp_arg e =
				let needs_convert = match e.eexpr with
					| TField (_, FAnon _) | TField (_, FDynamic _) -> true
					| _ -> s_type ctx e.etype = "FibDynamic"
				in
				if needs_convert then begin
					spr ctx "fib_dynamic_to_string("; gen_value ctx e; spr ctx ")"
				end else
					gen_value ctx e
			in
			spr ctx "!fib_string_eq(";
			gen_str_cmp_arg e1;
			spr ctx ", ";
			gen_str_cmp_arg e2;
			spr ctx ")"
		| OpAssign, _, _, _, _ ->
			(* Check for array element assignment: arr[i] = value *)
			(match e1.eexpr with
			| TArray (arr, idx) ->
				(* Check for specialized array types *)
				let arr_type = s_type ctx arr.etype in
				if arr_type = "FibIntArray*" then begin
					(* Specialized int array set *)
					spr ctx "fib_int_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", ";
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibFloatArray*" then begin
					(* Specialized float array set *)
					spr ctx "fib_float_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", ";
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibBoolArray*" then begin
					(* Specialized bool array set *)
					spr ctx "fib_bool_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", ";
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibUInt8Array*" then begin
					(* Specialized uint8 array set *)
					spr ctx "fib_uint8_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", ";
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibInt64Array*" then begin
					(* Specialized int64 array set *)
					spr ctx "fib_int64_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", ";
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibUInt64Array*" then begin
					(* Specialized uint64 array set *)
					spr ctx "fib_uint64_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", ";
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibFloat32Array*" then begin
					(* Specialized float32 array set *)
					spr ctx "fib_float32_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", ";
					gen_value ctx e2;
					spr ctx ")"
				end else begin
					(* Generic array - box the value for FibDynamic storage *)
					spr ctx "fib_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", ";
					(* Check for null literal first *)
					(match e2.eexpr with
					| TConst TNull ->
						spr ctx "fib_dynamic_null()"
					| _ ->
						let val_type = s_type ctx e2.etype in
						if val_type = "int32_t" then begin
							spr ctx "fib_dynamic_int("; gen_value ctx e2; spr ctx ")"
						end else if val_type = "double" then begin
							spr ctx "fib_dynamic_float("; gen_value ctx e2; spr ctx ")"
						end else if val_type = "FibString*" then begin
							spr ctx "fib_dynamic_string("; gen_value ctx e2; spr ctx ")"
						end else if val_type = "bool" then begin
							spr ctx "fib_dynamic_bool("; gen_value ctx e2; spr ctx ")"
						end else if val_type = "FibDynamic" then begin
							(* Already FibDynamic, no wrapping needed *)
							gen_value ctx e2
						end else begin
							(* Object pointer - wrap with fib_dynamic_object *)
							spr ctx "fib_dynamic_object((FibObject*)";
							gen_value ctx e2;
							spr ctx ")"
						end);
					spr ctx ")"
				end
			| TLocal v when Hashtbl.mem ctx.stack_alloc_vars v.v_id ->
				(* Reassignment to stack-allocated variable *)
				(match e2.eexpr with
				| TNew (c, _, args) ->
					(* Reinitialize the stack struct in place *)
					let class_name = flat_path c.cl_path in
					spr ctx "(";
					(* Reinitialize the struct fields *)
					print ctx "_stack_%s = (%s){ ._obj.clazz = &%s_class" (ident v.v_name) class_name class_name;
					(match c.cl_constructor with
					| Some cf ->
						(match cf.cf_expr with
						| Some { eexpr = TFunction f } ->
							let filtered_args = filter_void_args f.tf_args in
							let param_field_map = extract_param_field_mapping f in
							List.iter2 (fun (param_v, _) arg ->
								(* Look up the field name for this parameter *)
								let field_name = try List.assoc param_v.v_id param_field_map 
								                 with Not_found -> param_v.v_name in
								spr ctx ", .";
								spr ctx (ident field_name);
								spr ctx " = ";
								gen_value ctx arg
							) filtered_args args
						| _ -> ())
					| None -> ());
					print ctx " }, %s)" (ident v.v_name)
				| _ ->
					(* Not a TNew - shouldn't happen for stack-allocated vars but fall back *)
					spr ctx "(";
					gen_value ctx e1;
					gen_binop ctx op;
					gen_value ctx e2;
					spr ctx ")")
			| TField (obj_expr, field_access) ->
				(* Field assignment - may need write barrier for generational GC *)
				let lhs_type = s_type ctx e1.etype in
				let rhs_type = match get_actual_c_type ctx e2 with
					| Some t -> t
					| None -> s_type ctx e2.etype
				in
				(* Check if this is an instance field (has an object to barrier) *)
				let is_instance_field = match field_access with
					| FInstance (_, _, _) | FAnon _ | FDynamic _ -> true
					| FClosure (Some _, _) -> true
					| FStatic _ | FEnum _ | FClosure (None, _) -> false
				in
				(* Check if RHS is an object pointer (not primitive) - needs write barrier *)
				let needs_write_barrier = 
					is_instance_field &&
					(is_class_pointer_type rhs_type || 
					rhs_type = "FibArray*" || 
					rhs_type = "FibString*" ||
					rhs_type = "FibObject*" ||
					(String.length rhs_type > 0 && rhs_type.[String.length rhs_type - 1] = '*' &&
					 rhs_type <> "char*" && rhs_type <> "void*" && rhs_type <> "int*"))
				in
				if needs_write_barrier then begin
					(* Emit: (FIBRIX_WRITE_BARRIER(obj, value), obj->field = value) *)
					spr ctx "(FIBRIX_WRITE_BARRIER(";
					(* Generate the object expression for write barrier *)
					gen_value ctx obj_expr;
					spr ctx ", ";
					(* Generate the value expression for write barrier check *)
					if lhs_type = "FibDynamic" && rhs_type = "FibArray*" then begin
						spr ctx "fib_dynamic_array(";
						gen_value ctx e2;
						spr ctx ")"
					end else if lhs_type = "FibDynamic" && rhs_type = "FibString*" then begin
						spr ctx "fib_string_to_dynamic(";
						gen_value ctx e2;
						spr ctx ")"
					end else if lhs_type = "FibDynamic" && is_class_pointer_type rhs_type then begin
						spr ctx "fib_dynamic_object((FibObject*)";
						gen_value ctx e2;
						spr ctx ")"
					end else
						gen_value ctx e2;
					spr ctx "), ";
					(* Now emit the actual assignment *)
					gen_value ctx e1;
					gen_binop ctx op;
					if lhs_type = "FibDynamic" && rhs_type = "FibArray*" then begin
						spr ctx "fib_dynamic_array(";
						gen_value ctx e2;
						spr ctx ")"
					end else if lhs_type = "FibDynamic" && rhs_type = "FibString*" then begin
						spr ctx "fib_string_to_dynamic(";
						gen_value ctx e2;
						spr ctx ")"
					end else if lhs_type = "FibDynamic" && is_class_pointer_type rhs_type then begin
						spr ctx "fib_dynamic_object((FibObject*)";
						gen_value ctx e2;
						spr ctx ")"
					end else
						gen_value ctx e2;
					spr ctx ")"
				end else begin
					(* No write barrier needed for primitives *)
					spr ctx "(";
					gen_value ctx e1;
					gen_binop ctx op;
					if lhs_type = "FibDynamic" && rhs_type = "int32_t" then begin
						spr ctx "fib_dynamic_int(";
						gen_value ctx e2;
						spr ctx ")"
					end else if lhs_type = "FibDynamic" && rhs_type = "double" then begin
						spr ctx "fib_dynamic_float(";
						gen_value ctx e2;
						spr ctx ")"
					end else if lhs_type = "FibDynamic" && rhs_type = "bool" then begin
						spr ctx "fib_dynamic_bool(";
						gen_value ctx e2;
						spr ctx ")"
					end else
						gen_value ctx e2;
					spr ctx ")"
				end
			| _ ->
				(* Regular assignment (local variable, etc.) - no write barrier needed *)
				let lhs_type = s_type ctx e1.etype in
				let rhs_type = match get_actual_c_type ctx e2 with
					| Some t -> t
					| None -> s_type ctx e2.etype
				in
				spr ctx "(";
				gen_value ctx e1;
				gen_binop ctx op;
				if lhs_type = "FibDynamic" && rhs_type = "FibArray*" then begin
					spr ctx "fib_dynamic_array(";
					gen_value ctx e2;
					spr ctx ")"
				end else if lhs_type = "FibDynamic" && rhs_type = "FibString*" then begin
					spr ctx "fib_string_to_dynamic(";
					gen_value ctx e2;
					spr ctx ")"
				end else if lhs_type = "FibDynamic" && rhs_type = "int32_t" then begin
					spr ctx "fib_dynamic_int(";
					gen_value ctx e2;
					spr ctx ")"
				end else if lhs_type = "FibDynamic" && rhs_type = "double" then begin
					spr ctx "fib_dynamic_float(";
					gen_value ctx e2;
					spr ctx ")"
				end else if lhs_type = "FibDynamic" && rhs_type = "bool" then begin
					spr ctx "fib_dynamic_bool(";
					gen_value ctx e2;
					spr ctx ")"
				end else if lhs_type = "FibDynamic" && is_class_pointer_type rhs_type then begin
					spr ctx "fib_dynamic_object((FibObject*)";
					gen_value ctx e2;
					spr ctx ")"
				end else
					gen_value ctx e2;
				spr ctx ")")
		| OpUShr, _, _, _, _ ->
			(* Unsigned right shift: cast to uint32_t, shift, cast back to int32_t *)
			let e1_type = match get_actual_c_type ctx e1 with Some t -> t | None -> s_type ctx e1.etype in
			let e2_type = match get_actual_c_type ctx e2 with Some t -> t | None -> s_type ctx e2.etype in
			spr ctx "((int32_t)((uint32_t)(";
			if e1_type = "FibDynamic" then begin spr ctx "fib_dynamic_to_int("; gen_value ctx e1; spr ctx ")" end
			else gen_value ctx e1;
			spr ctx ") >> (";
			if e2_type = "FibDynamic" then begin spr ctx "fib_dynamic_to_int("; gen_value ctx e2; spr ctx ")" end
			else gen_value ctx e2;
			spr ctx ")))"
		| OpAssignOp OpUShr, _, _, _, _ ->
			(* Unsigned right shift assignment: e1 = (int32_t)((uint32_t)e1 >> e2) *)
			let e1_type = match get_actual_c_type ctx e1 with Some t -> t | None -> s_type ctx e1.etype in
			let e2_type = match get_actual_c_type ctx e2 with Some t -> t | None -> s_type ctx e2.etype in
			spr ctx "(";
			gen_value ctx e1;
			if e1_type = "FibDynamic" then begin
				spr ctx " = fib_dynamic_int((int32_t)((uint32_t)fib_dynamic_to_int(";
				gen_value ctx e1;
				spr ctx ") >> (";
				if e2_type = "FibDynamic" then begin spr ctx "fib_dynamic_to_int("; gen_value ctx e2; spr ctx ")" end
				else gen_value ctx e2;
				spr ctx ")))"
			end else begin
				spr ctx " = (int32_t)((uint32_t)(";
				gen_value ctx e1;
				spr ctx ") >> (";
				if e2_type = "FibDynamic" then begin spr ctx "fib_dynamic_to_int("; gen_value ctx e2; spr ctx ")" end
				else gen_value ctx e2;
				spr ctx ")))"
			end
		| OpAssignOp inner_op, _, _, _, _ when (match e1.eexpr with TArray _ -> true | _ -> false) ->
			(* Array compound assignment: arr[i] op= value  ->  arr_set(arr, i, arr_get(arr, i) op value) *)
			(match e1.eexpr with
			| TArray (arr, idx) ->
				let arr_type = s_type ctx arr.etype in
				if arr_type = "FibIntArray*" then begin
					spr ctx "fib_int_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", fib_int_array_get(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ")";
					gen_binop ctx inner_op;
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibFloatArray*" then begin
					spr ctx "fib_float_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", fib_float_array_get(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ")";
					gen_binop ctx inner_op;
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibUInt8Array*" then begin
					spr ctx "fib_uint8_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", fib_uint8_array_get(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ")";
					gen_binop ctx inner_op;
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibInt64Array*" then begin
					spr ctx "fib_int64_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", fib_int64_array_get(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ")";
					gen_binop ctx inner_op;
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibUInt64Array*" then begin
					spr ctx "fib_uint64_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", fib_uint64_array_get(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ")";
					gen_binop ctx inner_op;
					gen_value ctx e2;
					spr ctx ")"
				end else if arr_type = "FibFloat32Array*" then begin
					spr ctx "fib_float32_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", fib_float32_array_get(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ")";
					gen_binop ctx inner_op;
					gen_value ctx e2;
					spr ctx ")"
				end else begin
					(* Generic array with FibDynamic *)
					spr ctx "fib_array_set(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx ", fib_dynamic_int(fib_dynamic_to_int(fib_array_get(";
					gen_value ctx arr;
					spr ctx ", ";
					gen_value ctx idx;
					spr ctx "))";
					gen_binop ctx inner_op;
					gen_value ctx e2;
					spr ctx "))"
				end
			| _ -> assert false)
		| OpAssignOp inner_op, _, _, _, _ ->
			(* Compound assignment on FibDynamic: a op= b -> a = fib_dynamic_XXX(fib_dynamic_to_XXX(a) op b) *)
			let lhs_type = match get_actual_c_type ctx e1 with Some t -> t | None -> s_type ctx e1.etype in
			let rhs_type = match get_actual_c_type ctx e2 with Some t -> t | None -> s_type ctx e2.etype in
			if lhs_type = "FibDynamic" then begin
				(* LHS is FibDynamic - need to extract, operate, and re-box *)
				spr ctx "(";
				gen_value ctx e1;
				spr ctx " = fib_dynamic_int(fib_dynamic_to_int(";
				gen_value ctx e1;
				spr ctx ")";
				gen_binop ctx inner_op;
				if rhs_type = "FibDynamic" then begin
					spr ctx "fib_dynamic_to_int(";
					gen_value ctx e2;
					spr ctx ")"
				end else
					gen_value ctx e2;
				spr ctx "))"
			end else begin
				(* LHS is not FibDynamic - regular compound assignment *)
				spr ctx "(";
				gen_value ctx e1;
				gen_binop ctx (OpAssignOp inner_op);
				if rhs_type = "FibDynamic" then begin
					(* RHS is FibDynamic - extract it *)
					if lhs_type = "double" then begin
						spr ctx "fib_dynamic_to_float(";
						gen_value ctx e2;
						spr ctx ")"
					end else begin
						spr ctx "fib_dynamic_to_int(";
						gen_value ctx e2;
						spr ctx ")"
					end
				end else
					gen_value ctx e2;
				spr ctx ")"
			end
		| _, _, _, _, _ ->
			(* Check if either operand needs FibDynamic extraction for comparisons/arithmetic *)
			(* Use get_actual_c_type to detect dynamic field access that returns FibDynamic at runtime *)
			let get_c_type exp =
				match get_actual_c_type ctx exp with
				| Some t -> t
				| None -> s_type ctx exp.etype
			in
			let my_type = get_c_type e1 in
			let other_type = get_c_type e2 in
			(* Determine the extraction target type based on Haxe result type *)
			let result_type = s_type ctx e.etype in
			(* For arithmetic, comparison, bitwise, and boolean ops, we need to extract FibDynamic to primitives *)
			let is_numeric_op = match op with
				| OpAdd | OpSub | OpMult | OpDiv | OpMod -> true
				| OpLt | OpLte | OpGt | OpGte -> true  (* comparison ops need extraction *)
				| OpAnd | OpOr | OpXor | OpShl | OpShr | OpUShr -> true  (* bitwise ops need extraction *)
				| _ -> false
			in
			let is_bool_op = match op with
				| OpBoolAnd | OpBoolOr -> true
				| _ -> false
			in
			let is_arithmetic = is_numeric_op || is_bool_op in
			(* For equality ops between FibDynamic and primitive, extract the FibDynamic side *)
			let is_equality = match op with
				| OpEq | OpNotEq -> true
				| _ -> false
			in
			let is_primitive_type t = 
				t = "int32_t" || t = "double" || t = "bool" || t = "int64_t"
			in
			(* If operand's C type is FibDynamic, we need to extract for arithmetic/equality *)
			let e1_needs_extract = my_type = "FibDynamic" && (is_arithmetic || (is_equality && is_primitive_type other_type)) in
			let e2_needs_extract = other_type = "FibDynamic" && (is_arithmetic || (is_equality && is_primitive_type my_type)) in
			(* Determine target type for extraction - use the non-FibDynamic operand's type for equality/comparison *)
			let is_comparison = match op with OpLt | OpLte | OpGt | OpGte -> true | _ -> false in
			let target_type_for_extract = 
				if is_equality || is_comparison then
					(* For equality/comparison, extract FibDynamic to match the other operand's type *)
					if my_type = "FibDynamic" then other_type else my_type
				else if is_bool_op then
					"bool"  (* Boolean ops always need bool extraction *)
				else 
					result_type
			in
			let gen_with_extraction exp needs_extract =
				if needs_extract then begin
					(* Extract based on the target type *)
					if target_type_for_extract = "double" then begin
						spr ctx "fib_dynamic_to_float("; gen_value ctx exp; spr ctx ")"
					end else if target_type_for_extract = "int32_t" then begin
						spr ctx "fib_dynamic_to_int("; gen_value ctx exp; spr ctx ")"
					end else if target_type_for_extract = "bool" then begin
						spr ctx "fib_dynamic_to_bool("; gen_value ctx exp; spr ctx ")"
					end else if target_type_for_extract = "int64_t" then begin
						spr ctx "fib_dynamic_to_int64("; gen_value ctx exp; spr ctx ")"
					end else begin
						(* Fallback: try int for unknown types (safer than double for bitwise ops) *)
						spr ctx "fib_dynamic_to_int("; gen_value ctx exp; spr ctx ")"
					end
				end else
					gen_value ctx exp
			in
			spr ctx "(";
			gen_with_extraction e1 e1_needs_extract;
			gen_binop ctx op;
			gen_with_extraction e2 e2_needs_extract;
			spr ctx ")")
	| TField (e, fa) ->
		gen_field_access ctx e fa
	| TTypeExpr mt ->
		spr ctx (flat_path (t_path mt))
	| TParenthesis e ->
		spr ctx "(";
		gen_value ctx e;
		spr ctx ")"
	| TObjectDecl fl ->
		(* Generate anonymous object with fields using GCC statement expression *)
		if fl = [] then
			spr ctx "fib_anon_new()"
		else begin
			spr ctx "({ FibDynamic _anon = fib_anon_new(); ";
			List.iter (fun ((name, _, _), e) ->
				spr ctx "fib_anon_set(&_anon, \"";
				spr ctx name;
				spr ctx "\", ";
				(* Wrap value appropriately based on type *)
				let t = follow e.etype in
				(match t with
				| TAbstract ({ a_path = ([], "Int") }, []) ->
					spr ctx "fib_dynamic_int(";
					gen_value ctx e;
					spr ctx ")"
				| TAbstract ({ a_path = ([], "Float") }, []) ->
					spr ctx "fib_dynamic_float(";
					gen_value ctx e;
					spr ctx ")"
				| TAbstract ({ a_path = ([], "Bool") }, []) ->
					spr ctx "fib_dynamic_bool(";
					gen_value ctx e;
					spr ctx ")"
				| TInst ({ cl_path = ([], "String") }, []) ->
					spr ctx "fib_string_to_dynamic(";
					gen_value ctx e;
					spr ctx ")"
				| _ ->
					gen_value ctx e);
				spr ctx "); "
			) fl;
			spr ctx "_anon; })"
		end
	| TArrayDecl el ->
		(* Check if this is a specialized array type based on the expression's type *)
		let arr_type = s_type ctx e.etype in
		if arr_type = "FibIntArray*" then begin
			(* Specialized int array literal *)
			spr ctx "fib_int_array_from_values((int32_t[]){";
			let rec loop = function
				| [] -> ()
				| [e] -> gen_value ctx e
				| e :: rest -> gen_value ctx e; spr ctx ", "; loop rest
			in
			loop el;
			print ctx "}, %d)" (List.length el)
		end else if arr_type = "FibFloatArray*" then begin
			(* Specialized float array literal *)
			spr ctx "fib_float_array_from_values((double[]){";
			let rec loop = function
				| [] -> ()
				| [e] -> gen_value ctx e
				| e :: rest -> gen_value ctx e; spr ctx ", "; loop rest
			in
			loop el;
			print ctx "}, %d)" (List.length el)
		end else if arr_type = "FibBoolArray*" then begin
			(* Specialized bool array literal *)
			spr ctx "fib_bool_array_from_values((uint8_t[]){";
			let rec loop = function
				| [] -> ()
				| [e] -> gen_value ctx e
				| e :: rest -> gen_value ctx e; spr ctx ", "; loop rest
			in
			loop el;
			print ctx "}, %d)" (List.length el)
		end else if arr_type = "FibUInt8Array*" then begin
			(* Specialized uint8 array literal *)
			spr ctx "fib_uint8_array_from_values((uint8_t[]){";
			let rec loop = function
				| [] -> ()
				| [e] -> gen_value ctx e
				| e :: rest -> gen_value ctx e; spr ctx ", "; loop rest
			in
			loop el;
			print ctx "}, %d)" (List.length el)
		end else if arr_type = "FibInt64Array*" then begin
			(* Specialized int64 array literal *)
			spr ctx "fib_int64_array_from_values((int64_t[]){";
			let rec loop = function
				| [] -> ()
				| [e] -> gen_value ctx e
				| e :: rest -> gen_value ctx e; spr ctx ", "; loop rest
			in
			loop el;
			print ctx "}, %d)" (List.length el)
		end else if arr_type = "FibUInt64Array*" then begin
			(* Specialized uint64 array literal *)
			spr ctx "fib_uint64_array_from_values((uint64_t[]){";
			let rec loop = function
				| [] -> ()
				| [e] -> gen_value ctx e
				| e :: rest -> gen_value ctx e; spr ctx ", "; loop rest
			in
			loop el;
			print ctx "}, %d)" (List.length el)
		end else if arr_type = "FibFloat32Array*" then begin
			(* Specialized float32 array literal *)
			spr ctx "fib_float32_array_from_values((float[]){";
			let rec loop = function
				| [] -> ()
				| [e] -> gen_value ctx e
				| e :: rest -> gen_value ctx e; spr ctx ", "; loop rest
			in
			loop el;
			print ctx "}, %d)" (List.length el)
		end else begin
			(* Generic array - use FibDynamic boxing *)
			spr ctx "fib_array_from_values((FibDynamic[]){";
			(* Generate FibDynamic initializers for each element *)
			let gen_fib_dynamic_init e =
				(* For constants, use direct struct initialization *)
				match e.eexpr with
				| TConst c ->
					gen_fib_dynamic_constant ctx c
				| _ ->
					(* For other expressions, determine type and wrap appropriately *)
					let t = follow e.etype in
					(match t with
					| TAbstract ({ a_path = ([], "Int") }, []) ->
						spr ctx "{.type=FIB_TYPE_INT, .data.intVal=";
						gen_value ctx e;
						spr ctx "}"
					| TAbstract ({ a_path = ([], "Float") }, []) ->
						spr ctx "{.type=FIB_TYPE_FLOAT, .data.floatVal=";
						gen_value ctx e;
						spr ctx "}"
					| TAbstract ({ a_path = ([], "Bool") }, []) ->
						spr ctx "{.type=FIB_TYPE_BOOL, .data.boolVal=";
						gen_value ctx e;
						spr ctx "}"
					| TInst ({ cl_path = ([], "String") }, []) ->
						spr ctx "{.type=FIB_TYPE_STRING, .data.stringVal=";
						gen_value ctx e;
						spr ctx "}"
					| TInst ({ cl_path = ([], "Array") }, _) ->
						spr ctx "{.type=FIB_TYPE_ARRAY, .data.arrayVal=";
						gen_value ctx e;
						spr ctx "}"
					| TInst (_, _) ->
						spr ctx "{.type=FIB_TYPE_OBJECT, .data.objectVal=(FibObject*)";
						gen_value ctx e;
						spr ctx "}"
					| TDynamic _ | TAnon _ ->
						(* Dynamic or anonymous - generate value and use as FibDynamic directly *)
						gen_value ctx e
					| _ ->
						(* Fallback: try to generate as raw value wrapped in FibDynamic *)
						spr ctx "{.type=FIB_TYPE_NULL, .data.ptrVal=(void*)";
						gen_value ctx e;
						spr ctx "}")
			in
			let rec loop = function
				| [] -> ()
				| [e] -> gen_fib_dynamic_init e
				| e :: rest -> gen_fib_dynamic_init e; spr ctx ", "; loop rest
			in
			loop el;
			print ctx "}, %d)" (List.length el)
		end
	| TCall (e, args) ->
		gen_call ctx e args
	| TNew (c, tl, args) ->
		(* Special handling for Array<T> -> fib_*_array_new() *)
		if c.cl_path = ([], "Array") then begin
			(* Check for specialized array types based on type parameter *)
			let arr_func = match tl with
				| [elem_t] ->
					(match follow elem_t with
					| TAbstract ({ a_path = ([], "Int") }, []) -> "fib_int_array_new"
					| TAbstract ({ a_path = ([], "Float") }, []) -> "fib_float_array_new"
					| TAbstract ({ a_path = ([], "Bool") }, []) -> "fib_bool_array_new"
					(* Fiberus native array types *)
					| TAbstract ({ a_path = (["fiberus"], "UInt8") }, []) -> "fib_uint8_array_new"
					| TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "fib_int64_array_new"
					| TAbstract ({ a_path = (["fiberus"], "UInt64") }, []) -> "fib_uint64_array_new"
					| TAbstract ({ a_path = (["fiberus"], "Float32") }, []) -> "fib_float32_array_new"
					| _ -> "fib_array_new")
				| _ -> "fib_array_new"
			in
			print ctx "%s()" arr_func
		(* Hash map types *)
		end else if c.cl_path = (["haxe"; "ds"], "IntMap") then begin
			spr ctx "fib_int_map_new()"
		end else if c.cl_path = (["haxe"; "ds"], "StringMap") then begin
			spr ctx "fib_string_map_new()"
		end else if c.cl_path = (["haxe"; "ds"], "Int64Map") then begin
			spr ctx "fib_int64_map_new()"
		end else if c.cl_path = (["haxe"; "ds"], "ObjectMap") then begin
			spr ctx "fib_object_map_new()"
		end else begin
			print ctx "%s_new(" (flat_path c.cl_path);
			let rec loop = function
				| [] -> ()
				| [arg] -> gen_value ctx arg
				| arg :: rest -> gen_value ctx arg; spr ctx ", "; loop rest
			in
			loop args;
			spr ctx ")"
		end
	| TUnop (op, flag, e) ->
		(* Special handling for increment/decrement on array elements *)
		(match op, e.eexpr with
		| (Increment | Decrement), TArray (arr, idx) ->
			(* Array element increment/decrement needs special handling *)
			(* Generate: fib_xxx_array_set(arr, idx, fib_xxx_array_get(arr, idx) +/- 1) *)
			let arr_type = match get_actual_c_type ctx arr with
				| Some t -> t
				| None -> s_type ctx arr.etype
			in
			let op_str = match op with Increment -> " + 1" | Decrement -> " - 1" | _ -> "" in
			if arr_type = "FibIntArray*" then begin
				spr ctx "fib_int_array_set(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ", fib_int_array_get(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ")";
				spr ctx op_str;
				spr ctx ")"
			end else if arr_type = "FibFloatArray*" then begin
				spr ctx "fib_float_array_set(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ", fib_float_array_get(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ")";
				spr ctx op_str;
				spr ctx ")"
			end else if arr_type = "FibUInt8Array*" then begin
				spr ctx "fib_uint8_array_set(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ", fib_uint8_array_get(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ")";
				spr ctx op_str;
				spr ctx ")"
			end else if arr_type = "FibInt64Array*" then begin
				spr ctx "fib_int64_array_set(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ", fib_int64_array_get(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ")";
				spr ctx op_str;
				spr ctx ")"
			end else if arr_type = "FibUInt64Array*" then begin
				spr ctx "fib_uint64_array_set(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ", fib_uint64_array_get(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ")";
				spr ctx op_str;
				spr ctx ")"
			end else if arr_type = "FibFloat32Array*" then begin
				spr ctx "fib_float32_array_set(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ", fib_float32_array_get(";
				gen_value ctx arr;
				spr ctx ", ";
				gen_value ctx idx;
				spr ctx ")";
				spr ctx op_str;
				spr ctx ")"
			end else begin
				(* Generic array - use standard ++ *)
				if flag = Prefix then gen_unop ctx op flag;
				gen_value ctx e;
				if flag = Postfix then gen_unop ctx op flag
			end
		| (Increment | Decrement), _ ->
			(* Check if operand is FibDynamic - need special handling *)
			let operand_type = match get_actual_c_type ctx e with Some t -> t | None -> s_type ctx e.etype in
			if operand_type = "FibDynamic" then begin
				(* FibDynamic increment/decrement:
				 * Pre:  ({ e = fib_dynamic_int(fib_dynamic_to_int(e) +/- 1); fib_dynamic_to_int(e); })
				 * Post: ({ int32_t _old = fib_dynamic_to_int(e); e = fib_dynamic_int(_old +/- 1); _old; })
				 * Following hxcpp, the result is int32_t (or double), not FibDynamic *)
				let delta = match op with Increment -> "+ 1" | Decrement -> "- 1" | _ -> "" in
				if flag = Prefix then begin
					spr ctx "({ ";
					gen_value ctx e;
					spr ctx " = fib_dynamic_int(fib_dynamic_to_int(";
					gen_value ctx e;
					spr ctx ") ";
					spr ctx delta;
					spr ctx "); fib_dynamic_to_int(";
					gen_value ctx e;
					spr ctx "); })"
				end else begin
					spr ctx "({ int32_t _old = fib_dynamic_to_int(";
					gen_value ctx e;
					spr ctx "); ";
					gen_value ctx e;
					spr ctx " = fib_dynamic_int(_old ";
					spr ctx delta;
					spr ctx "); _old; })"
				end
			end else begin
				(* Standard unary operation *)
				if flag = Prefix then gen_unop ctx op flag;
				gen_value ctx e;
				if flag = Postfix then gen_unop ctx op flag
			end
		| _ ->
			(* Other unary operations (Not, Neg, NegBits) *)
			let operand_type = match get_actual_c_type ctx e with Some t -> t | None -> s_type ctx e.etype in
			if operand_type = "FibDynamic" then begin
				(* FibDynamic unary ops need extraction *)
				(match op with
				| Not ->
					spr ctx "!fib_dynamic_to_bool(";
					gen_value ctx e;
					spr ctx ")"
				| Neg ->
					spr ctx "-fib_dynamic_to_int(";
					gen_value ctx e;
					spr ctx ")"
				| NegBits ->
					spr ctx "~fib_dynamic_to_int(";
					gen_value ctx e;
					spr ctx ")"
				| _ ->
					if flag = Prefix then gen_unop ctx op flag;
					gen_value ctx e;
					if flag = Postfix then gen_unop ctx op flag)
			end else begin
				if flag = Prefix then gen_unop ctx op flag;
				gen_value ctx e;
				if flag = Postfix then gen_unop ctx op flag
			end)
	| TFunction f ->
		(* Collect free variables to detect capturing closures *)
		let free_vars = collect_free_vars f.tf_args f.tf_expr in
		let closure_name = Printf.sprintf "_closure_%d" ctx.closure_counter in
		ctx.closure_counter <- ctx.closure_counter + 1;
		(* Only add to closures list if we're NOT in implementation phase *)
		(* During implementation, closures were already collected by pre-scan *)
		if not ctx.in_closure_impl then
			ctx.closures <- (closure_name, f, free_vars) :: ctx.closures;
		(* Always generate FibClosure* for uniformity *)
		(* Generate: ({ FibClosure* c = fib_closure_create[_for_fiber](fn, n); c->captures[i] = ...; c; }) *)
		(* NOTE: For fiber spawns (in_fiber_spawn=true), the Fiber.spawn/spawnOn/spawnAny
		 * handlers above generate the closure inline to ensure proper temp root protection.
		 * This branch should NOT be reached for fiber spawns, but we keep the mature alloc
		 * logic as a safety measure. *)
		let arg_count = List.length f.tf_args in
		let impl_name = closure_name ^ "_impl" in
		if ctx.in_fiber_spawn then
			spr ctx "({ FibClosure* _c = fib_closure_create_for_fiber((void*)"
		else
			spr ctx "({ FibClosure* _c = fib_closure_create((void*)";
		spr ctx impl_name;
		spr ctx ", (void*)";
		spr ctx closure_name;
		print ctx ", %d, %d); " (List.length free_vars) arg_count;
		List.iteri (fun i v ->
			print ctx "_c->captures[%d] = " i;
			(* Box the captured value appropriately *)
			let vtype = s_type ctx v.v_type in
			if vtype = "int32_t" then
				print ctx "fib_dynamic_int(%s); " (ident v.v_name)
			else if vtype = "double" then
				print ctx "fib_dynamic_float(%s); " (ident v.v_name)
			else if vtype = "bool" then
				print ctx "fib_dynamic_bool(%s); " (ident v.v_name)
			else if vtype = "FibString*" then
				print ctx "fib_dynamic_string(%s); " (ident v.v_name)
			else
				print ctx "(FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=%s}; " (ident v.v_name)
		) free_vars;
		spr ctx "_c; })"
	| TVar (v, eo) ->
		(* Check if this variable can be stack-allocated *)
		let is_stack_alloc = Hashtbl.mem ctx.stack_alloc_vars v.v_id in
		if is_stack_alloc then begin
			(* Stack allocation: declare struct on stack, then take address *)
			let c = Hashtbl.find ctx.stack_alloc_vars v.v_id in
			let class_name = flat_path c.cl_path in
			(* Declare the struct on the stack with just the class pointer *)
			print ctx "%s _stack_%s = { ._obj.clazz = &%s_class };" class_name (ident v.v_name) class_name;
			newline ctx;
			(* Declare the pointer variable pointing to the stack struct *)
			print ctx "%s* %s = &_stack_%s;" class_name (ident v.v_name) (ident v.v_name);
			newline ctx;
			(* Call init function with constructor arguments *)
			print ctx "%s_init(%s" class_name (ident v.v_name);
			(match eo with
			| Some { eexpr = TNew (tc, _, args) } when List.length args > 0 ->
				spr ctx ", ";
				let param_types = match tc.cl_constructor with
					| Some cf -> get_param_types cf.cf_type
					| None -> []
				in
				gen_call_args ctx args param_types gen_value
			| _ -> ());
			spr ctx ")"
		end else begin
			(* Normal heap allocation path *)
			(* Special handling for function types - use FibClosure* *)
			(match follow v.v_type with
			| TFun _ ->
				(* All closures use FibClosure* for uniformity - volatile for GC safety *)
				print ctx "FibClosure* volatile %s" (ident v.v_name)
			| _ ->
				(* Use volatile for GC pointer types to prevent register optimization *)
				let type_str = s_type ctx v.v_type in
				if String.length type_str > 0 && type_str.[String.length type_str - 1] = '*' then
					print ctx "%s volatile %s" type_str (ident v.v_name)
				else
					print ctx "%s %s" type_str (ident v.v_name));
			(match eo with
			| None -> ()
			| Some e ->
				spr ctx " = ";
				gen_coerce_with_expr ctx e.etype v.v_type (Some e) (fun () -> gen_value ctx e))
		end
	| TBlock el ->
		(* Block used as value - use GCC statement expression syntax ({...}) *)
		let old_tabs = ctx.tabs in
		let saved_gc_count = ctx.gc_local_count in
		ctx.tabs <- ctx.tabs ^ "\t";
		spr ctx "({";
		newline ctx;
		(* Generate all but last expression as statements, last as value *)
		let rec gen_block_exprs = function
			| [] -> ()
			| [last] ->
				(* Last expression - generate as value for the block to evaluate to *)
				gen_value ctx last;
				spr ctx ";";
				newline ctx
			| e :: rest ->
				gen_expr ctx e;
				spr ctx ";";
				newline ctx;
				gen_block_exprs rest
		in
		gen_block_exprs el;
		(* Pop GC roots if needed *)
		let to_pop = ctx.gc_local_count - saved_gc_count in
		let block_returns = match el with
			| [] -> false
			| _ -> ends_with_return (List.hd (List.rev el))
		in
		if to_pop > 0 && not block_returns then begin
			print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" to_pop;
			newline ctx
		end;
		ctx.gc_local_count <- saved_gc_count;
		ctx.tabs <- old_tabs;
		newline ctx;
		spr ctx "})"
	| TIf (cond, e1, e2) ->
		ctx.in_value <- true;
		(* Check for type mismatch in ternary - need to coerce branches to same type *)
		let t1 = match get_actual_c_type ctx e1 with Some t -> t | None -> s_type ctx e1.etype in
		let t2 = match e2 with
			| Some e -> (match get_actual_c_type ctx e with Some t -> t | None -> s_type ctx e.etype)
			| None -> "FibDynamic"
		in
		spr ctx "((";
		(* Condition might be FibDynamic - extract to bool if needed *)
		let cond_type = match get_actual_c_type ctx cond with Some t -> t | None -> s_type ctx cond.etype in
		if cond_type = "FibDynamic" then begin
			spr ctx "fib_dynamic_to_bool(";
			gen_value ctx cond;
			spr ctx ")"
		end else
			gen_value ctx cond;
		spr ctx ") ? (";
		(* If one side is FibDynamic and other is primitive, box the primitive *)
		if t2 = "FibDynamic" && t1 <> "FibDynamic" then
			gen_box_to_fib_dynamic ctx t1 (fun () -> gen_value ctx e1)
		else
			gen_value ctx e1;
		spr ctx ") : (";
		(match e2 with
		| None -> spr ctx "fib_dynamic_null()"
		| Some e ->
			if t1 = "FibDynamic" && t2 <> "FibDynamic" then
				gen_box_to_fib_dynamic ctx t2 (fun () -> gen_value ctx e)
			else
				gen_value ctx e);
		spr ctx "))"
	| TWhile _ | TSwitch _ | TTry _ ->
		spr ctx "/* complex expr */"
	| TReturn eo ->
		(match eo with
		| None -> spr ctx "return"
		| Some e ->
			spr ctx "return ";
			(match ctx.current_ret_type with
			| Some ret_type ->
				gen_coerce_with_expr ctx e.etype ret_type (Some e) (fun () -> gen_value ctx e)
			| None ->
				gen_value ctx e))
	| TBreak -> spr ctx "break"
	| TContinue -> spr ctx "continue"
	| TThrow e ->
		(* Begin exception unwinding - captures stack frames as we unwind *)
		spr ctx "fib_exception_begin(); fib_throw(";
		(* Box the value into FibDynamic based on its type *)
		let throw_type = s_type ctx e.etype in
		if throw_type = "FibDynamic" then
			gen_value ctx e
		else if throw_type = "FibString*" then begin
			spr ctx "fib_string_to_dynamic(";
			gen_value ctx e;
			spr ctx ")"
		end else if throw_type = "int32_t" then begin
			spr ctx "fib_dynamic_int(";
			gen_value ctx e;
			spr ctx ")"
		end else if throw_type = "double" then begin
			spr ctx "fib_dynamic_float(";
			gen_value ctx e;
			spr ctx ")"
		end else if throw_type = "bool" then begin
			spr ctx "fib_dynamic_bool(";
			gen_value ctx e;
			spr ctx ")"
		end else if is_enum_struct_type throw_type then begin
			(* For enum values (value types), box with fib_dynamic_enum.
			   Need to use statement expression with temp var since we can't take address of function return. *)
			print ctx "({ %s _enum_tmp = " throw_type;
			gen_value ctx e;
			print ctx "; fib_dynamic_enum(&_enum_tmp, sizeof(%s)); })" throw_type
		end else begin
			(* For objects/exceptions, wrap in FibDynamic *)
			spr ctx "fib_dynamic_object((FibObject*)";
			gen_value ctx e;
			spr ctx ")"
		end;
		spr ctx ")"
	| TCast (inner, _) ->
		(* Generate type conversion if needed *)
		let from_c = match get_actual_c_type ctx inner with
			| Some t -> t
			| None -> s_type ctx inner.etype
		in
		let to_c = s_type ctx e.etype in
		if from_c = to_c then
			gen_value ctx inner
		else if from_c = "FibDynamic" && to_c = "int32_t" then begin
			spr ctx "fib_dynamic_to_int(";
			gen_value ctx inner;
			spr ctx ")"
		end else if from_c = "FibDynamic" && to_c = "double" then begin
			spr ctx "fib_dynamic_to_float(";
			gen_value ctx inner;
			spr ctx ")"
		end else if from_c = "FibDynamic" && to_c = "bool" then begin
			spr ctx "fib_dynamic_to_bool(";
			gen_value ctx inner;
			spr ctx ")"
		end else if from_c = "FibDynamic" && to_c = "FibString*" then begin
			spr ctx "fib_dynamic_to_string(";
			gen_value ctx inner;
			spr ctx ")"
		end else if from_c = "FibDynamic" && is_class_pointer_type to_c then begin
			print ctx "((%s)fib_dynamic_to_object(" to_c;
			gen_value ctx inner;
			spr ctx "))"
		end else
			gen_value ctx inner
	| TMeta (_, e) ->
		gen_value ctx e
	| TEnumParameter (enum_expr, _, i) ->
		(* Enum params are stored as FibDynamic, need to unbox based on target type *)
		let param_type = s_type ctx e.etype in
		if param_type = "FibString*" then begin
			spr ctx "fib_dynamic_to_string(";
			gen_value ctx enum_expr;
			print ctx ".params[%d])" i
		end else if param_type = "FibArray*" then begin
			spr ctx "fib_dynamic_to_array(";
			gen_value ctx enum_expr;
			print ctx ".params[%d])" i
		end else if param_type = "int32_t" then begin
			spr ctx "fib_dynamic_to_int(";
			gen_value ctx enum_expr;
			print ctx ".params[%d])" i
		end else if param_type = "double" then begin
			spr ctx "fib_dynamic_to_float(";
			gen_value ctx enum_expr;
			print ctx ".params[%d])" i
		end else if param_type = "bool" then begin
			spr ctx "fib_dynamic_to_bool(";
			gen_value ctx enum_expr;
			print ctx ".params[%d])" i
		end else if is_class_pointer_type param_type then begin
			(* Unbox to object and cast to class type *)
			print ctx "((%s)fib_dynamic_to_object(" param_type;
			gen_value ctx enum_expr;
			print ctx ".params[%d]))" i
		end else if is_enum_struct_type param_type then begin
			(* Unbox enum with null check - use index=-1 for null *)
			print ctx "(fib_dynamic_is_null(";
			gen_value ctx enum_expr;
			print ctx ".params[%d]) ? (%s){ .index = -1 } : (*(%s*)fib_dynamic_to_ptr(" i param_type param_type;
			gen_value ctx enum_expr;
			print ctx ".params[%d])))" i
		end else begin
			(* FibDynamic or unknown - access directly *)
			gen_value ctx enum_expr;
			print ctx ".params[%d]" i
		end
	| TEnumIndex enum_e ->
		(* Check if expression returns FibDynamic (dynamic field access) *)
		let is_dyn = match enum_e.eexpr with
			| TField (_, FAnon _) | TField (_, FDynamic _) -> true
			| _ -> false
		in
		if is_dyn then begin
			(* FibDynamic enum - use helper to get index *)
			spr ctx "fib_dynamic_enum_index(";
			gen_value ctx enum_e;
			spr ctx ")"
		end else begin
			gen_value ctx enum_e;
			spr ctx ".index"
		end
	| TIdent s ->
		spr ctx (ident s)

and gen_field_access ctx e fa =
	match fa with
	| FStatic (c, cf) ->
		(* Static field access: Class_field *)
		print ctx "%s_%s" (flat_path c.cl_path) (ident cf.cf_name)
	| FInstance (c, _, cf) ->
		(* Array.length -> fib_*_array_length() *)
		if is_array_type e.etype && cf.cf_name = "length" then begin
			(* Use specialized length function for specialized arrays *)
			let arr_type = s_type ctx e.etype in
			let length_func =
				if arr_type = "FibIntArray*" then "fib_int_array_length"
				else if arr_type = "FibFloatArray*" then "fib_float_array_length"
				else if arr_type = "FibBoolArray*" then "fib_bool_array_length"
				else if arr_type = "FibUInt8Array*" then "fib_uint8_array_length"
				else if arr_type = "FibInt64Array*" then "fib_int64_array_length"
				else if arr_type = "FibUInt64Array*" then "fib_uint64_array_length"
				else if arr_type = "FibFloat32Array*" then "fib_float32_array_length"
				else "fib_array_length"
			in
			print ctx "%s(" length_func;
			(* Check if expression returns FibDynamic (dynamic field access) *)
			let needs_convert = match e.eexpr with
				| TField (_, FAnon _) | TField (_, FDynamic _) -> true
				| _ -> false
			in
			if needs_convert then spr ctx "fib_dynamic_to_array(";
			gen_value ctx e;
			if needs_convert then spr ctx ")";
			spr ctx ")"
		(* String.length -> fib_string_length() *)
		end else if is_string_type e.etype && cf.cf_name = "length" then begin
			spr ctx "fib_string_length(";
			(* Check if expression returns FibDynamic *)
			let needs_convert = match e.eexpr with
				| TField (_, FAnon _) | TField (_, FDynamic _) -> true
				| _ -> false
			in
			if needs_convert then spr ctx "fib_dynamic_to_string(";
			gen_value ctx e;
			if needs_convert then spr ctx ")";
			spr ctx ")"
		end else begin
			(* Field belongs to class c - cast if accessing inherited field *)
			let needs_cast = match e.etype with
				| TInst (obj_class, _) -> obj_class.cl_path <> c.cl_path
				| _ -> false
			in
			if needs_cast then begin
				print ctx "((%s*)" (flat_path c.cl_path);
				gen_value ctx e;
				print ctx ")->%s" (ident cf.cf_name)
			end else begin
				gen_value ctx e;
				print ctx "->%s" (ident cf.cf_name)
			end
		end
	| FClosure (Some (c, _), cf) ->
		(* Method reference - wrap in FibClosure with thunk
		 * We need to create a closure that wraps the static/instance method.
		 * The thunk adapts the method to closure calling convention.
		 *
		 * For static methods: thunk ignores closure arg, calls method directly
		 * For instance methods: thunk uses closure context as the bound 'this' *)
		let class_name = flat_path c.cl_path in
		let method_name = ident cf.cf_name in
		let thunk_name = Printf.sprintf "__%s_%s_thunk" class_name method_name in
		(* Determine if this is a static method by checking cl_statics *)
		let is_static = List.exists (fun scf -> scf.cf_name = cf.cf_name) c.cl_ordered_statics in
		(* Get argument types and return type *)
		let arg_types, ret_type = match follow cf.cf_type with
			| TFun (args, ret) -> (List.map (fun (n, _, t) -> (n, t)) args, ret)
			| _ -> ([], t_dynamic)
		in
		(* Register the thunk for generation: (is_static, class_path, method_name, arg_types, ret_type) *)
		Hashtbl.replace ctx.method_thunks thunk_name (is_static, c.cl_path, cf.cf_name, arg_types, ret_type);
		let method_arg_count = List.length arg_types in
		let dyn_thunk_name = thunk_name ^ "_dyn" in
		(* Generate closure creation using GCC statement expression *)
		if is_static then begin
			(* Static method - no captures needed *)
			spr ctx "({ FibClosure* _c = fib_closure_create((void*)";
			spr ctx thunk_name;
			spr ctx ", (void*)";
			spr ctx dyn_thunk_name;
			print ctx ", 0, %d); _c; })" method_arg_count
		end else begin
			(* Instance method - store 'this' in captures[0] *)
			spr ctx "({ FibClosure* _c = fib_closure_create((void*)";
			spr ctx thunk_name;
			spr ctx ", (void*)";
			spr ctx dyn_thunk_name;
			print ctx ", 1, %d); _c->captures[0] = fib_dynamic_object((FibObject*)" method_arg_count;
			gen_value ctx e;
			spr ctx "); _c; })"
		end
	| FClosure (None, cf) ->
		(* Instance method reference on dynamic object - complex case *)
		(* For now, just access the field - may need more work for full support *)
		gen_value ctx e;
		print ctx "->%s" (ident cf.cf_name)
	| FAnon cf ->
		spr ctx "fib_field_get(";
		gen_value ctx e;
		print ctx ", \"%s\")" cf.cf_name
	| FDynamic s ->
		spr ctx "fib_field_get(";
		gen_value ctx e;
		print ctx ", \"%s\")" s
	| FEnum (en, ef) ->
		print ctx "%s_%s" (flat_path en.e_path) ef.ef_name

and gen_expr ctx e =
	match e.eexpr with
	| TConst _ | TLocal _ | TArray _ | TBinop _ | TField _
	| TTypeExpr _ | TParenthesis _ | TObjectDecl _ | TArrayDecl _
	| TCall _ | TNew _ | TUnop _ | TCast _ | TMeta _
	| TEnumParameter _ | TEnumIndex _ | TIdent _ ->
		gen_value ctx e
	| TFunction _ ->
		()  (* Function expressions handled elsewhere *)
	| TVar (v, eo) ->
		(* Check if this variable can be stack-allocated *)
		let is_stack_alloc = Hashtbl.mem ctx.stack_alloc_vars v.v_id in
		if is_stack_alloc then begin
			(* Stack allocation: declare struct on stack, then take address *)
			let c = Hashtbl.find ctx.stack_alloc_vars v.v_id in
			let class_name = flat_path c.cl_path in
			(* Declare the struct on the stack with just the class pointer *)
			print ctx "%s _stack_%s = { ._obj.clazz = &%s_class };" class_name (ident v.v_name) class_name;
			newline ctx;
			(* Declare the pointer variable pointing to the stack struct *)
			print ctx "%s* %s = &_stack_%s;" class_name (ident v.v_name) (ident v.v_name);
			newline ctx;
			(* Call init function with constructor arguments *)
			print ctx "%s_init(%s" class_name (ident v.v_name);
			(match eo with
			| Some { eexpr = TNew (tc, _, args) } when List.length args > 0 ->
				spr ctx ", ";
				let param_types = match tc.cl_constructor with
					| Some cf -> get_param_types cf.cf_type
					| None -> []
				in
				gen_call_args ctx args param_types gen_value
			| _ -> ());
			spr ctx ")"
			(* Stack-allocated objects don't need gc_push_temp_root - they're on the stack *)
		end else begin
			(* Normal heap allocation path *)
			(* Get type string to check if it's a GC pointer *)
			let type_str = match follow v.v_type with
				| TFun _ -> "FibClosure*"
				| _ -> s_type ctx v.v_type
			in
			let is_gc_ptr = String.length type_str > 0 && type_str.[String.length type_str - 1] = '*' in
			(* Generate variable declaration (no more volatile - we use gc_push_temp_root instead) *)
			print ctx "%s %s" type_str (ident v.v_name);
			(match eo with
			| None -> ()
			| Some e ->
				spr ctx " = ";
				gen_coerce_with_expr ctx e.etype v.v_type (Some e) (fun () -> gen_value ctx e));
			(* For GC pointer types, push as temp root to ensure GC can find it *)
			if is_gc_ptr then begin
				spr ctx "; gc_push_temp_root_ctx(FIB_CTX, (void**)&";
				spr ctx (ident v.v_name);
				spr ctx ")";
				ctx.gc_local_count <- ctx.gc_local_count + 1
			end
		end
	| TBlock el ->
		let b = open_block_for_exprs ctx el in
		List.iter (fun e ->
			gen_expr ctx e;
			spr ctx ";";
			newline ctx
		) el;
		b ()
	| TIf (cond, e1, e2) ->
		spr ctx "if (";
		gen_value ctx cond;
		spr ctx ") { ";
		let saved_gc1 = ctx.gc_local_count in
		gen_expr ctx e1;
		(match e1.eexpr with TBlock _ -> () | _ -> spr ctx ";");
		(* Pop GC roots from then-branch, but only if branch doesn't end with return
		 * (return statements handle their own cleanup) *)
		let to_pop1 = ctx.gc_local_count - saved_gc1 in
		if to_pop1 > 0 && not (ends_with_return e1) then begin
			spr ctx " gc_pop_temp_roots_ctx(FIB_CTX, ";
			print ctx "%d);" to_pop1
		end;
		ctx.gc_local_count <- saved_gc1;
		spr ctx " }";
		(match e2 with
		| None -> ()
		| Some e ->
			spr ctx " else { ";
			let saved_gc2 = ctx.gc_local_count in
			gen_expr ctx e;
			(match e.eexpr with TBlock _ -> () | _ -> spr ctx ";");
			(* Pop GC roots from else-branch, but only if branch doesn't end with return *)
			let to_pop2 = ctx.gc_local_count - saved_gc2 in
			if to_pop2 > 0 && not (ends_with_return e) then begin
				spr ctx " gc_pop_temp_roots_ctx(FIB_CTX, ";
				print ctx "%d);" to_pop2
			end;
			ctx.gc_local_count <- saved_gc2;
			spr ctx " }")
	| TWhile (cond, e, NormalWhile) ->
		spr ctx "while (";
		gen_value ctx cond;
		spr ctx ") {";
		newline ctx;
		ctx.tabs <- ctx.tabs ^ "\t";
		ctx.loop_depth <- ctx.loop_depth + 1;
		(* Save GC count at loop body start - will pop at end of each iteration *)
		let saved_gc_count = ctx.gc_local_count in
		(* Yield point only for outer loops (depth <= 1) - inner loops are short-lived *)
		if ctx.loop_depth <= 1 then begin
			spr ctx "FIBER_YIELD_POINT();";
			newline ctx
		end;
		(match e.eexpr with
		| TBlock el ->
			List.iter (fun e ->
				gen_expr ctx e;
				spr ctx ";";
				newline ctx
			) el
		| _ ->
			gen_expr ctx e;
			spr ctx ";";
			newline ctx);
		(* Pop GC roots pushed in this iteration before next iteration *)
		let to_pop = ctx.gc_local_count - saved_gc_count in
		if to_pop > 0 then begin
			print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" to_pop;
			newline ctx;
			ctx.gc_local_count <- saved_gc_count
		end;
		ctx.loop_depth <- ctx.loop_depth - 1;
		ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
		spr ctx "}"
	| TWhile (cond, e, DoWhile) ->
		spr ctx "do {";
		newline ctx;
		ctx.tabs <- ctx.tabs ^ "\t";
		ctx.loop_depth <- ctx.loop_depth + 1;
		(* Save GC count at loop body start - will pop at end of each iteration *)
		let saved_gc_count = ctx.gc_local_count in
		(* Yield point only for outer loops (depth <= 1) - inner loops are short-lived *)
		if ctx.loop_depth <= 1 then begin
			spr ctx "FIBER_YIELD_POINT();";
			newline ctx
		end;
		(match e.eexpr with
		| TBlock el ->
			List.iter (fun e ->
				gen_expr ctx e;
				spr ctx ";";
				newline ctx
			) el
		| _ ->
			gen_expr ctx e;
			spr ctx ";";
			newline ctx);
		(* Pop GC roots pushed in this iteration before next iteration *)
		let to_pop = ctx.gc_local_count - saved_gc_count in
		if to_pop > 0 then begin
			print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" to_pop;
			newline ctx;
			ctx.gc_local_count <- saved_gc_count
		end;
		ctx.loop_depth <- ctx.loop_depth - 1;
		ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
		spr ctx "} while (";
		gen_value ctx cond;
		spr ctx ")"
	| TSwitch sw ->
		(* Check if switch subject is a string - C can't switch on strings *)
		if is_string_type sw.switch_subject.etype then begin
			(* Generate if-else chain for string switches *)
			let tmp = temp ctx in
			print ctx "FibString* %s = " tmp;
			gen_value ctx sw.switch_subject;
			spr ctx ";";
			newline ctx;
			let first_case = ref true in
			List.iter (fun case ->
				if !first_case then begin
					spr ctx "if (";
					first_case := false
				end else begin
					newline ctx;
					spr ctx "else if ("
				end;
				(* Join multiple patterns with || *)
				let first_pat = ref true in
				List.iter (fun pat ->
					if !first_pat then
						first_pat := false
					else
						spr ctx " || ";
					print ctx "fib_string_eq(%s, " tmp;
					gen_value ctx pat;
					spr ctx ")"
				) case.case_patterns;
				spr ctx ") {";
				newline ctx;
				ctx.tabs <- ctx.tabs ^ "\t";
				gen_expr ctx case.case_expr;
				spr ctx ";";
				ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
				newline ctx;
				spr ctx "}"
			) sw.switch_cases;
			(match sw.switch_default with
			| None -> ()
			| Some e ->
				if not !first_case then begin
					spr ctx " else {";
					newline ctx;
					ctx.tabs <- ctx.tabs ^ "\t"
				end;
				gen_expr ctx e;
				spr ctx ";";
				if not !first_case then begin
					ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
					newline ctx;
					spr ctx "}"
				end)
		end else begin
			(* Integer switch - use C switch *)
			spr ctx "switch (";
			gen_value ctx sw.switch_subject;
			spr ctx ") ";
			let b = open_block ctx in
			List.iter (fun case ->
				List.iter (fun pat ->
					spr ctx "case ";
					gen_value ctx pat;
					spr ctx ":";
					newline ctx
				) case.case_patterns;
				gen_expr ctx case.case_expr;
				spr ctx ";";
				newline ctx;
				spr ctx "break;";
				newline ctx
			) sw.switch_cases;
			(match sw.switch_default with
			| None -> ()
			| Some e ->
				spr ctx "default:";
				newline ctx;
				gen_expr ctx e;
				spr ctx ";";
				newline ctx);
			b ()
		end
	| TTry (e, catches) ->
		(* Generate try-catch using setjmp/longjmp *)
		let jmp = temp ctx in
		let exc = temp ctx in
		let gc_save = temp ctx in
		let stack_save = temp ctx in
		spr ctx "{";
		newline ctx;
		ctx.tabs <- ctx.tabs ^ "\t";
		print ctx "jmp_buf %s;" jmp;
		newline ctx;
		(* Save GC root count before try - will restore on exception *)
		print ctx "size_t %s = FIB_CTX ? FIB_CTX->mTempRootCount : 0;" gc_save;
		newline ctx;
		(* Save stack frame count - longjmp bypasses cleanup handlers *)
		print ctx "int %s = fib_current_fiber() ? fib_current_fiber()->stackFrameCount : 0;" stack_save;
		newline ctx;
		print ctx "fib_exc_push(&%s);" jmp;
		newline ctx;
		print ctx "if (setjmp(%s) == 0) {" jmp;
		newline ctx;
		ctx.tabs <- ctx.tabs ^ "\t";
		gen_expr ctx e;
		newline ctx;
		spr ctx "fib_exc_pop();";
		ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
		newline ctx;
		spr ctx "} else {";
		newline ctx;
		ctx.tabs <- ctx.tabs ^ "\t";
		(* Restore GC roots to pre-try level - longjmp skipped cleanup code *)
		print ctx "if (FIB_CTX && FIB_CTX->mTempRootCount > %s) FIB_CTX->mTempRootCount = %s;" gc_save gc_save;
		newline ctx;
		(* Restore stack frame count - longjmp bypassed cleanup handlers *)
		print ctx "if (fib_current_fiber()) fib_current_fiber()->stackFrameCount = %s;" stack_save;
		newline ctx;
		print ctx "FibDynamic %s = fib_current_exception();" exc;
		newline ctx;
		(* Stop exception unwinding - exception stack is now complete *)
		spr ctx "fib_exception_catch();";
		newline ctx;
		(* Generate catch clauses with proper type checking *)
		let first = ref true in
		List.iter (fun (v, catch_e) ->
			let catch_type = s_type ctx v.v_type in
			(* Generate type check condition *)
			let gen_type_check () =
				if catch_type = "FibDynamic" then
					(* Dynamic catches everything - no condition needed *)
					spr ctx "1"
				else if catch_type = "int32_t" then
					print ctx "%s.type == FIB_TYPE_INT" exc
				else if catch_type = "double" then
					print ctx "%s.type == FIB_TYPE_FLOAT" exc
				else if catch_type = "bool" then
					print ctx "%s.type == FIB_TYPE_BOOL" exc
				else if catch_type = "FibString*" then
					print ctx "%s.type == FIB_TYPE_STRING" exc
				else begin
					(* Object type - check FIB_TYPE_OBJECT and instanceof *)
					let class_name = String.sub catch_type 0 (String.length catch_type - 1) in (* Remove * *)
					print ctx "(%s.type == FIB_TYPE_OBJECT && fib_object_instanceof(%s.data.objectVal, &%s_class))"
						exc exc class_name
				end
			in
			if !first then begin
				first := false;
				print ctx "if (";
				gen_type_check ();
				spr ctx ")"
			end else begin
				spr ctx " else if (";
				gen_type_check ();
				spr ctx ")"
			end;
			newline ctx;
			spr ctx "{";
			newline ctx;
			ctx.tabs <- ctx.tabs ^ "\t";
			(* Assign exception to catch variable with proper extraction *)
			print ctx "%s %s = " catch_type (ident v.v_name);
			if catch_type = "FibDynamic" then
				print ctx "%s" exc
			else if catch_type = "int32_t" then
				print ctx "fib_dynamic_to_int(%s)" exc
			else if catch_type = "double" then
				print ctx "fib_dynamic_to_float(%s)" exc
			else if catch_type = "bool" then
				print ctx "%s.data.boolVal" exc
			else if catch_type = "FibString*" then
				print ctx "fib_dynamic_to_string(%s)" exc
			else
				print ctx "(%s)%s.data.objectVal" catch_type exc;
			spr ctx ";";
			newline ctx;
			gen_expr ctx catch_e;
			ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
			newline ctx;
			spr ctx "}"
		) catches;
		ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
		newline ctx;
		spr ctx "}";
		ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
		newline ctx;
		spr ctx "}"
	| TReturn eo ->
		(* Handle GC roots cleanup before return *)
		if ctx.gc_local_count > 0 then begin
			(match eo with
			| None ->
				(* Simple case: no return value, just pop and return *)
				print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d); return" ctx.gc_local_count
			| Some e ->
				(* Complex case: evaluate return value first, save to temp, pop roots, return temp *)
				let ret_type = match ctx.current_ret_type with
					| Some t -> s_type ctx t
					| None -> s_type ctx e.etype
				in
				(* For simple values like constants/locals, we can return directly after pop *)
				let is_simple = match e.eexpr with
					| TConst _ | TLocal _ -> true
					| _ -> false
				in
				if is_simple then begin
					print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d); return " ctx.gc_local_count;
					(match ctx.current_ret_type with
					| Some ret_type -> gen_coerce_with_expr ctx e.etype ret_type (Some e) (fun () -> gen_value ctx e)
					| None -> gen_value ctx e)
				end else begin
					(* Evaluate into temp, then pop, then return *)
					spr ctx "{ ";
					print ctx "%s __ret = " ret_type;
					(match ctx.current_ret_type with
					| Some ret_type -> gen_coerce_with_expr ctx e.etype ret_type (Some e) (fun () -> gen_value ctx e)
					| None -> gen_value ctx e);
					print ctx "; gc_pop_temp_roots_ctx(FIB_CTX, %d); return __ret; }" ctx.gc_local_count
				end)
			(* NOTE: We do NOT reset gc_local_count here because:
			 * 1. The TIf handler properly saves/restores gc_local_count for each branch
			 * 2. Setting it to 0 would corrupt tracking for later code paths
			 * 3. The duplicate gc_pop issue needs a different fix *)
		end else begin
			(* No GC locals to pop - original code *)
			match eo with
			| None -> spr ctx "return"
			| Some e ->
				spr ctx "return ";
				(match ctx.current_ret_type with
				| Some ret_type ->
					gen_coerce_with_expr ctx e.etype ret_type (Some e) (fun () -> gen_value ctx e)
				| None ->
					gen_value ctx e)
		end
	| TBreak -> spr ctx "break"
	| TContinue -> spr ctx "continue"
	| TThrow e ->
		(* Begin exception unwinding - captures stack frames as we unwind *)
		spr ctx "fib_exception_begin(); fib_throw(";
		(* Box the value into FibDynamic based on its type *)
		let throw_type = s_type ctx e.etype in
		if throw_type = "FibDynamic" then
			gen_value ctx e
		else if throw_type = "FibString*" then begin
			spr ctx "fib_string_to_dynamic(";
			gen_value ctx e;
			spr ctx ")"
		end else if throw_type = "int32_t" then begin
			spr ctx "fib_dynamic_int(";
			gen_value ctx e;
			spr ctx ")"
		end else if throw_type = "double" then begin
			spr ctx "fib_dynamic_float(";
			gen_value ctx e;
			spr ctx ")"
		end else if throw_type = "bool" then begin
			spr ctx "fib_dynamic_bool(";
			gen_value ctx e;
			spr ctx ")"
		end else if is_enum_struct_type throw_type then begin
			(* For enum values (value types), box with fib_dynamic_enum.
			   Need to use statement expression with temp var since we can't take address of function return. *)
			print ctx "({ %s _enum_tmp = " throw_type;
			gen_value ctx e;
			print ctx "; fib_dynamic_enum(&_enum_tmp, sizeof(%s)); })" throw_type
		end else begin
			(* For objects/exceptions, wrap in FibDynamic *)
			spr ctx "fib_dynamic_object((FibObject*)";
			gen_value ctx e;
			spr ctx ")"
		end;
		spr ctx ")"

let gen_function ctx name f c is_static =
	let class_name = flat_path c.cl_path in
	(* Filter out void-typed parameters *)
	let filtered_args = filter_void_args f.tf_args in
	let args = List.map (fun (v, _) ->
		s_type_with_name ctx v.v_type (ident v.v_name)
	) filtered_args in
	let func_name = Printf.sprintf "%s_%s" class_name name in
	let args_str =
		if is_static then
			if args = [] then "void" else String.concat ", " args
		else
			let this_arg = Printf.sprintf "%s* this" class_name in
			if args = [] then this_arg else this_arg ^ ", " ^ String.concat ", " args
	in
	spr ctx (s_func_decl ctx f.tf_type func_name args_str);
	spr ctx " {";
	newline ctx;
	ctx.tabs <- ctx.tabs ^ "\t";
	(* Cache GC context at function entry - avoids TLS reads in hot path *)
	spr ctx "FIB_GC_CTX;";
	newline ctx;
	(* Inject GC safe point at function entry - stack is clean here *)
	spr ctx "GC_SAFE_POINT();";
	newline ctx;
	(* Reset GC local count and context flag for this function *)
	let old_gc_count = ctx.gc_local_count in
	let old_has_gc_ctx = ctx.has_gc_ctx in
	let old_stack_alloc_vars = ctx.stack_alloc_vars in
	ctx.gc_local_count <- 0;
	ctx.has_gc_ctx <- true;
	(* Run escape analysis to find stack-allocatable variables *)
	ctx.stack_alloc_vars <- analyze_escapes f;
	(* Stack frame for source mapping *)
	gen_stack_push ctx class_name name f.tf_expr.epos;
	(* Set return type for coercion in return statements *)
	let old_ret_type = ctx.current_ret_type in
	ctx.current_ret_type <- Some f.tf_type;
	(* Generate function body - unwrap TBlock to avoid double braces *)
	(match f.tf_expr.eexpr with
	| TBlock el ->
		List.iter (fun e ->
			gen_line ctx e.epos;
			gen_expr ctx e;
			spr ctx ";";
			newline ctx
		) el
	| _ ->
		gen_line ctx f.tf_expr.epos;
		gen_expr ctx f.tf_expr;
		spr ctx ";";
		newline ctx);
	(* Pop all GC roots pushed in this function (for fall-through case) *)
	(* Skip if the function body ends with a return (return already does gc_pop) *)
	if ctx.gc_local_count > 0 && not (ends_with_return f.tf_expr) then begin
		print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" ctx.gc_local_count;
		newline ctx
	end;
	ctx.current_ret_type <- old_ret_type;
	ctx.gc_local_count <- old_gc_count;
	ctx.has_gc_ctx <- old_has_gc_ctx;
	ctx.stack_alloc_vars <- old_stack_alloc_vars;
	ctx.tabs <- String.sub ctx.tabs 0 (String.length ctx.tabs - 1);
	spr ctx "}";
	newline ctx;
	newline ctx

(* Generate a static variable declaration *)
(* Check if an expression is a compile-time constant (can be used in static initializer) *)
let rec is_const_expr e =
	match e.eexpr with
	| TConst _ -> true
	| TField (_, FEnum _) -> true  (* Enum constants *)
	| TParenthesis e -> is_const_expr e
	| TCast (e, _) -> is_const_expr e
	| TMeta (_, e) -> is_const_expr e
	| _ -> false

(* Check if a static field needs runtime initialization (non-constant initializer) *)
let needs_runtime_init cf =
	match cf.cf_kind, cf.cf_expr with
	| Var _, Some e when not (is_const_expr e) ->
		(match e.eexpr with
		| TFunction _ -> false  (* Functions don't need runtime init *)
		| _ -> true)
	| _ -> false

(* Get list of static fields that need runtime initialization *)
let get_runtime_init_fields c =
	List.filter needs_runtime_init c.cl_ordered_statics

let gen_static_var ctx c cf =
	let class_name = flat_path c.cl_path in
	let var_type = s_type ctx cf.cf_type in
	(* Use C 'static' only for promoted local statics (marked with CfNoLookup) *)
	(* Regular class static fields are global and need extern in header *)
	let is_local_static = has_class_field_flag cf CfNoLookup in
	if is_local_static then
		print ctx "static %s %s_%s" var_type class_name (ident cf.cf_name)
	else
		print ctx "%s %s_%s" var_type class_name (ident cf.cf_name);
	(* Only use initializer if it's a compile-time constant *)
	(match cf.cf_expr with
	| Some e when is_const_expr e ->
		spr ctx " = ";
		gen_value ctx e
	| _ ->
		(* Default initialization - non-constant init needs runtime init *)
		if var_type = "int32_t" then spr ctx " = 0"
		else if var_type = "double" then spr ctx " = 0.0"
		else if var_type = "bool" then spr ctx " = false"
		else spr ctx " = NULL");
	spr ctx ";";
	newline ctx

let gen_class_field ctx c cf is_static =
	match cf.cf_expr with
	| Some { eexpr = TFunction f } ->
		gen_function ctx cf.cf_name f c is_static
	| _ -> ()

(* Generate constructor: ClassName_init(this, args) and ClassName_new(args) *)
(* For simple constructors, these are generated inline in the header, so skip *)
let gen_constructor ctx c =
	let class_name = flat_path c.cl_path in
	match c.cl_constructor with
	| None ->
		(* Empty constructor - generated inline in header, skip here *)
		()
	| Some cf ->
		(match cf.cf_expr with
		| Some { eexpr = TFunction f } ->
			(* Check if this is a simple constructor (already inline in header) *)
			if is_simple_constructor ctx f then
				(* Skip - simple constructors are generated inline in header *)
				()
			else begin
				(* Complex constructor - generate implementation in .c file *)
				let filtered_args = filter_void_args f.tf_args in
				let args = List.map (fun (v, _) ->
					s_type_with_name ctx v.v_type (ident v.v_name)
				) filtered_args in
				let args_str = String.concat ", " args in
				(* Check if constructor body needs GC context (allocations or GC pointers) *)
				let rec needs_gc_context e =
					match e.eexpr with
					| TNew _ -> true
					| TCall ({ eexpr = TField (_, FStatic (_, cf)) }, _) when cf.cf_name = "new" -> true
					| TVar (v, _) when needs_gc_root ctx v.v_type -> true
					| _ -> 
						let found = ref false in
						Type.iter (fun e -> if needs_gc_context e then found := true) e;
						!found
				in
				let init_needs_gc_ctx = needs_gc_context f.tf_expr in
				(* _init function - initializes fields on existing object *)
				print ctx "void %s_init(%s* this%s)" class_name class_name
					(if args = [] then "" else ", " ^ args_str);
				spr ctx " {";
				newline ctx;
				ctx.tabs <- "\t";
				(* Track GC locals in constructor body *)
				let old_gc_count = ctx.gc_local_count in
				let old_has_gc_ctx = ctx.has_gc_ctx in
				let old_stack_alloc_vars = ctx.stack_alloc_vars in
				ctx.gc_local_count <- 0;
				(* Run escape analysis for constructor body *)
				ctx.stack_alloc_vars <- analyze_escapes f;
				(* Only emit FIB_GC_CTX if constructor body needs it *)
				if init_needs_gc_ctx then begin
					spr ctx "FIB_GC_CTX;";
					newline ctx;
					ctx.has_gc_ctx <- true
				end else
					ctx.has_gc_ctx <- false;
				(* Generate constructor body *)
				ctx.current_ret_type <- None;  (* Constructors don't return values *)
				(match f.tf_expr.eexpr with
				| TBlock el ->
					List.iter (fun e ->
						gen_expr ctx e;
						spr ctx ";";
						newline ctx
					) el
				| _ ->
					gen_expr ctx f.tf_expr;
					spr ctx ";";
					newline ctx);
				(* Pop GC roots if any were pushed *)
				if ctx.gc_local_count > 0 then begin
					print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" ctx.gc_local_count;
					newline ctx
				end;
				ctx.gc_local_count <- old_gc_count;
				ctx.has_gc_ctx <- old_has_gc_ctx;
				ctx.stack_alloc_vars <- old_stack_alloc_vars;
				ctx.tabs <- "";
				spr ctx "}";
				newline ctx;
				newline ctx;
				(* _new function - allocates and calls _init *)
				let args_str_for_new = if args = [] then "void" else args_str in
				print ctx "%s* %s_new(%s)" class_name class_name args_str_for_new;
				spr ctx " {";
				newline ctx;
				ctx.tabs <- "\t";
				(* Use inline allocation directly - avoids extra TLS caching when _init doesn't need it *)
				print ctx "%s* this = gc_alloc_object_inline(sizeof(%s));" class_name class_name;
				newline ctx;
				(* Set class pointer *)
				print ctx "((FibObject*)this)->clazz = &%s_class;" class_name;
				newline ctx;
				(* Call _init with args - use filtered args for consistency *)
				let arg_names = List.map (fun (v, _) -> ident v.v_name) filtered_args in
				print ctx "%s_init(this%s);" class_name
					(if arg_names = [] then "" else ", " ^ String.concat ", " arg_names);
				newline ctx;
				spr ctx "return this;";
				newline ctx;
				ctx.tabs <- "";
				spr ctx "}";
				newline ctx;
				newline ctx
			end
		| _ -> ())

(* Generate method thunks - wrapper functions that adapt methods to closure calling convention.
 * A thunk like __Calculator_staticAdd_thunk(FibClosure* _c, int a, int b) calls
 * Calculator_staticAdd(a, b), allowing the method to be used as a FibClosure*.
 *
 * Also generates dynamic thunks (_dyn suffix) that take FibDynamic params for dynamic calls.
 *)
let gen_method_thunks ctx =
	if Hashtbl.length ctx.method_thunks = 0 then () else begin
		newline ctx;
		spr ctx "/* Method thunks for closure wrapping */";
		newline ctx;
		Hashtbl.iter (fun thunk_name (is_static, class_path, method_name, arg_types, ret_type) ->
			let class_name = flat_path class_path in
			(* Generate return type - use FibClosure* for function returns *)
			let ret_str = match follow ret_type with
				| TFun _ -> "FibClosure*"
				| _ -> s_type ctx ret_type
			in
			(* Generate parameter list: FibClosure* _c, then the actual params *)
			let param_strs = List.mapi (fun i (name, t) ->
				let param_name = if name = "" then Printf.sprintf "_arg%d" i else ident name in
				s_type_with_name ctx t param_name
			) arg_types in
			let all_params = "FibClosure* _c" :: param_strs in
			print ctx "static %s %s(%s) {" ret_str thunk_name (String.concat ", " all_params);
			newline ctx;
			ctx.tabs <- "\t";
			(* Generate the call to the actual method *)
			if ret_str <> "void" then spr ctx "return ";
			print ctx "%s_%s(" class_name (ident method_name);
			(* For instance methods, extract 'this' from captures[0] *)
			if not is_static then begin
				(* Instance method - extract 'this' pointer from captures[0] *)
				print ctx "(%s*)fib_dynamic_to_object(_c->captures[0])" class_name;
				if arg_types <> [] then spr ctx ", "
			end;
			let arg_names = List.mapi (fun i (name, _) ->
				if name = "" then Printf.sprintf "_arg%d" i else ident name
			) arg_types in
			spr ctx (String.concat ", " arg_names);
			spr ctx ");";
			newline ctx;
			ctx.tabs <- "";
			spr ctx "}";
			newline ctx;
			
			(* Generate dynamic thunk that takes FibDynamic params *)
			let dyn_thunk_name = thunk_name ^ "_dyn" in
			let dyn_param_strs = List.mapi (fun i _ -> Printf.sprintf "FibDynamic _arg%d" i) arg_types in
			let all_dyn_params = "FibClosure* _c" :: dyn_param_strs in
			print ctx "static FibDynamic %s(%s) {" dyn_thunk_name (String.concat ", " all_dyn_params);
			newline ctx;
			ctx.tabs <- "\t";
			(* Convert FibDynamic args to typed args *)
			List.iteri (fun i (_, t) ->
				let vtype = match follow t with
					| TFun _ -> "FibClosure*"
					| _ -> s_type ctx t
				in
				let conv = 
					if vtype = "int32_t" then Printf.sprintf "fib_dynamic_to_int(_arg%d)" i
					else if vtype = "double" then Printf.sprintf "fib_dynamic_to_float(_arg%d)" i
					else if vtype = "bool" then Printf.sprintf "fib_dynamic_to_bool(_arg%d)" i
					else if vtype = "FibString*" then Printf.sprintf "fib_dynamic_to_string(_arg%d)" i
					else if vtype = "int64_t" then Printf.sprintf "fib_dynamic_to_int64(_arg%d)" i
					else if vtype = "FibClosure*" then Printf.sprintf "(FibClosure*)fib_dynamic_to_object(_arg%d)" i
					else if vtype = "FibDynamic" then Printf.sprintf "_arg%d" i
					else Printf.sprintf "(%s)fib_dynamic_to_object(_arg%d)" vtype i
				in
				print ctx "%s _typed%d = %s;" vtype i conv;
				newline ctx
			) arg_types;
			(* Call the typed thunk *)
			let typed_call_args = List.mapi (fun i _ -> Printf.sprintf "_typed%d" i) arg_types in
			let call_args_str = String.concat ", " ("_c" :: typed_call_args) in
			if ret_str = "void" then begin
				print ctx "%s(%s);" thunk_name call_args_str;
				newline ctx;
				spr ctx "return fib_dynamic_null();";
				newline ctx
			end else begin
				let ret_conv = 
					if ret_str = "int32_t" then Printf.sprintf "fib_dynamic_int(%s(%s))" thunk_name call_args_str
					else if ret_str = "double" then Printf.sprintf "fib_dynamic_float(%s(%s))" thunk_name call_args_str
					else if ret_str = "bool" then Printf.sprintf "fib_dynamic_bool(%s(%s))" thunk_name call_args_str
					else if ret_str = "FibString*" then Printf.sprintf "fib_dynamic_string(%s(%s))" thunk_name call_args_str
					else if ret_str = "int64_t" then Printf.sprintf "fib_dynamic_int64(%s(%s))" thunk_name call_args_str
					else if ret_str = "FibClosure*" then Printf.sprintf "fib_dynamic_object((FibObject*)%s(%s))" thunk_name call_args_str
					else if ret_str = "FibDynamic" then Printf.sprintf "%s(%s)" thunk_name call_args_str
					else Printf.sprintf "fib_dynamic_object((FibObject*)%s(%s))" thunk_name call_args_str
				in
				print ctx "return %s;" ret_conv;
				newline ctx
			end;
			ctx.tabs <- "";
			spr ctx "}";
			newline ctx
		) ctx.method_thunks;
		newline ctx;
		(* Clear the thunks table for the next class *)
		Hashtbl.clear ctx.method_thunks
	end

(* Pre-scan a class to find method references that need thunks *)
let prescan_class_for_thunks ctx c =
	let rec scan_expr e =
		match e.eexpr with
		| TField (e, fa) ->
			scan_expr e;
			(match fa with
			| FClosure (Some (cls, _), cf) ->
				let class_name = flat_path cls.cl_path in
				let method_name = ident cf.cf_name in
				let thunk_name = Printf.sprintf "__%s_%s_thunk" class_name method_name in
				let is_static = List.exists (fun scf -> scf.cf_name = cf.cf_name) cls.cl_ordered_statics in
				let arg_types, ret_type = match follow cf.cf_type with
					| TFun (args, ret) -> (List.map (fun (n, _, t) -> (n, t)) args, ret)
					| _ -> ([], t_dynamic)
				in
				Hashtbl.replace ctx.method_thunks thunk_name (is_static, cls.cl_path, cf.cf_name, arg_types, ret_type)
			| _ -> ())
		| TBlock el -> List.iter scan_expr el
		| TFunction f -> scan_expr f.tf_expr
		| TIf (econd, eif, eelse) ->
			scan_expr econd; scan_expr eif;
			(match eelse with Some e -> scan_expr e | None -> ())
		| TWhile (econd, ebody, _) -> scan_expr econd; scan_expr ebody
		| TSwitch sw ->
			scan_expr sw.switch_subject;
			List.iter (fun case -> List.iter scan_expr case.case_patterns; scan_expr case.case_expr) sw.switch_cases;
			(match sw.switch_default with Some e -> scan_expr e | None -> ())
		| TTry (e, catches) ->
			scan_expr e;
			List.iter (fun (_, e) -> scan_expr e) catches
		| TReturn (Some e) -> scan_expr e
		| TVar (_, Some e) -> scan_expr e
		| TBinop (_, e1, e2) -> scan_expr e1; scan_expr e2
		| TUnop (_, _, e) -> scan_expr e
		| TCall (e, args) -> scan_expr e; List.iter scan_expr args
		| TParenthesis e -> scan_expr e
		| TArray (e1, e2) -> scan_expr e1; scan_expr e2
		| TArrayDecl el -> List.iter scan_expr el
		| TObjectDecl fields -> List.iter (fun ((_, _, _), e) -> scan_expr e) fields
		| TCast (e, _) -> scan_expr e
		| TMeta (_, e) -> scan_expr e
		| TEnumParameter (e, _, _) -> scan_expr e
		| TEnumIndex e -> scan_expr e
		| TNew (_, _, args) -> List.iter scan_expr args
		| TThrow e -> scan_expr e
		| _ -> ()
	in
	(* Scan constructor *)
	(match c.cl_constructor with
	| Some cf ->
		(match cf.cf_expr with
		| Some e -> scan_expr e
		| None -> ())
	| None -> ());
	(* Scan static methods *)
	List.iter (fun cf ->
		match cf.cf_kind, cf.cf_expr with
		| Method _, Some e -> scan_expr e
		| _ -> ()
	) c.cl_ordered_statics;
	(* Scan instance methods *)
	List.iter (fun cf ->
		match cf.cf_kind, cf.cf_expr with
		| Method _, Some e -> scan_expr e
		| _ -> ()
	) c.cl_ordered_fields

(* Generate a single class to its own .c file - returns the class implementation as string *)
let gen_class_impl ctx c =
	if has_class_flag c CExtern then "" else begin
		(* Set current class for super call resolution *)
		ctx.current_class <- Some c;
		let class_name = flat_path c.cl_path in
		let class_id = get_class_id ctx c.cl_path in

		(* Pre-scan to collect method thunks needed *)
		prescan_class_for_thunks ctx c;

		Buffer.clear ctx.buf;
		ctx.tabs <- "";

		(* Generate method thunk forward declarations at the top *)
		if Hashtbl.length ctx.method_thunks > 0 then begin
			spr ctx "/* Method thunk forward declarations */\n";
			Hashtbl.iter (fun thunk_name (_, _, _, arg_types, ret_type) ->
				let ret_str = match follow ret_type with
					| TFun _ -> "FibClosure*"
					| _ -> s_type ctx ret_type
				in
				(* Typed thunk forward declaration *)
				let param_strs = List.mapi (fun i (name, t) ->
					let param_name = if name = "" then Printf.sprintf "_arg%d" i else ident name in
					s_type_with_name ctx t param_name
				) arg_types in
				let all_params = "FibClosure* _c" :: param_strs in
				print ctx "static %s %s(%s);\n" ret_str thunk_name (String.concat ", " all_params);
				(* Dynamic thunk forward declaration *)
				let dyn_thunk_name = thunk_name ^ "_dyn" in
				let dyn_param_strs = List.mapi (fun i _ -> Printf.sprintf "FibDynamic _arg%d" i) arg_types in
				let all_dyn_params = "FibClosure* _c" :: dyn_param_strs in
				print ctx "static FibDynamic %s(%s);\n" dyn_thunk_name (String.concat ", " all_dyn_params)
			) ctx.method_thunks;
			spr ctx "\n"
		end;

		(* Collect instance fields that need GC marking *)
		let gc_fields = List.filter (fun cf ->
			match cf.cf_kind with
			| Var _ when not (has_class_field_flag cf CfStatic) ->
				let type_str = s_type ctx cf.cf_type in
				needs_gc_marking type_str
			| _ -> false
		) c.cl_ordered_fields in

		(* Generate mark function if there are GC pointer fields *)
		let has_mark_func = List.length gc_fields > 0 in
		if has_mark_func then begin
			print ctx "static void %s_mark(FibObject* obj, MarkContext* ctx) {" class_name;
			newline ctx;
			print ctx "\t%s* this = (%s*)obj;" class_name class_name;
			newline ctx;
			List.iter (fun cf ->
				let field_name = ident cf.cf_name in
				print ctx "\tgc_mark_object(ctx, this->%s);" field_name;
				newline ctx
			) gc_fields;
			spr ctx "}";
			newline ctx;
			newline ctx
		end;

		(* Generate vtable array if class has virtual methods *)
		let vtable_methods = match ctx.vtable_ctx with
			| Some vctx -> GenfiberusVtable.get_vtable_methods vctx c
			| None -> []
		in
		(* Vtable size is max_slot + 1, not count of methods *)
		let vtable_size = match vtable_methods with
			| [] -> 0
			| _ -> 
				let max_slot = List.fold_left (fun acc (slot, _, _) -> max acc slot) 0 vtable_methods in
				max_slot + 1
		in
		if vtable_size > 0 then begin
			print ctx "static void* %s_vtable[%d] = {" class_name vtable_size;
			newline ctx;
			(* Create a slot-indexed array for proper placement *)
			let slot_array = Array.make vtable_size None in
			List.iter (fun (slot, method_name, _cf) ->
				(* Find which class actually implements this method *)
				let impl_class = 
					let rec find_impl c =
						if List.exists (fun cf2 -> cf2.cf_name = method_name && GenfiberusVtable.is_instance_method cf2) c.cl_ordered_fields then
							c
						else match c.cl_super with
							| Some (parent, _) -> find_impl parent
							| None -> c (* fallback to current class *)
					in
					find_impl c
				in
				slot_array.(slot) <- Some (impl_class, method_name)
			) vtable_methods;
			(* Generate entries in slot order *)
			for i = 0 to vtable_size - 1 do
				ctx.tabs <- "\t";
				(match slot_array.(i) with
				| Some (impl_class, method_name) ->
					let impl_class_name = flat_path impl_class.cl_path in
					print ctx "(void*)%s_%s" impl_class_name (ident method_name)
				| None ->
					spr ctx "NULL");
				if i < vtable_size - 1 then spr ctx ",";
				print ctx " /* slot %d */" i;
				newline ctx
			done;
			ctx.tabs <- "";
			spr ctx "};";
			newline ctx;
			newline ctx
		end;

		(* FibClass definition *)
		print ctx "FibClass %s_class = {" class_name;
		newline ctx;
		ctx.tabs <- "\t";
		print ctx ".name = \"%s\"," (s_type_path c.cl_path);
		newline ctx;
		print ctx ".classId = %d," class_id;
		newline ctx;
		print ctx ".instanceSize = sizeof(%s)," class_name;
		newline ctx;
		(match c.cl_super with
		| Some (parent_c, _) ->
			print ctx ".super = &%s_class," (flat_path parent_c.cl_path)
		| None ->
			spr ctx ".super = NULL,");
		newline ctx;
		if has_mark_func then
			print ctx ".markFunc = %s_mark," class_name
		else
			spr ctx ".markFunc = NULL,";
		newline ctx;
		spr ctx ".construct = NULL,";
		newline ctx;
		spr ctx ".destruct = NULL,";
		newline ctx;
		spr ctx ".staticFields = NULL,";
		newline ctx;
		spr ctx ".fieldNames = NULL,";
		newline ctx;
		spr ctx ".fieldCount = 0,";
		newline ctx;
		(* Vtable fields *)
		if vtable_size > 0 then
			print ctx ".vtable = %s_vtable," class_name
		else
			spr ctx ".vtable = NULL,";
		newline ctx;
		print ctx ".vtableSize = %d" vtable_size;
		newline ctx;
		ctx.tabs <- "";
		spr ctx "};";
		newline ctx;
		newline ctx;

		(* Static variable declarations - for static locals promoted to class statics *)
		List.iter (fun cf ->
			match cf.cf_kind, cf.cf_expr with
			| Var _, None ->
				(* Static variable with no initializer *)
				gen_static_var ctx c cf
			| Var _, Some { eexpr = TFunction _ } ->
				(* This is a function, skip *)
				()
			| Var _, Some _ ->
				(* Static variable with initializer *)
				gen_static_var ctx c cf
			| _ -> ()
		) c.cl_ordered_statics;

		(* Generate __boot function for runtime static initialization *)
		let runtime_init_fields = get_runtime_init_fields c in
		if runtime_init_fields <> [] then begin
			print ctx "void %s___boot(void) {" class_name;
			newline ctx;
			ctx.tabs <- "\t";
			(* Cache GC context at function entry *)
			spr ctx "FIB_GC_CTX;";
			newline ctx;
			(* Reset GC local count for boot function *)
			let old_gc_count = ctx.gc_local_count in
			let old_has_gc_ctx = ctx.has_gc_ctx in
			ctx.gc_local_count <- 0;
			ctx.has_gc_ctx <- true;
			List.iter (fun cf ->
				match cf.cf_expr with
				| Some e ->
					print ctx "(%s_%s = " class_name (ident cf.cf_name);
					gen_value ctx e;
					spr ctx ");";
					newline ctx
				| None -> ()
			) runtime_init_fields;
			(* Pop GC roots if any were pushed during init *)
			if ctx.gc_local_count > 0 then begin
				print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" ctx.gc_local_count;
				newline ctx
			end;
			ctx.gc_local_count <- old_gc_count;
			ctx.has_gc_ctx <- old_has_gc_ctx;
			ctx.tabs <- "";
			spr ctx "}";
			newline ctx;
			newline ctx
		end;

		(* Constructor *)
		gen_constructor ctx c;

		(* Static methods *)
		List.iter (fun cf -> gen_class_field ctx c cf true) c.cl_ordered_statics;

		(* Instance methods *)
		List.iter (fun cf -> gen_class_field ctx c cf false) c.cl_ordered_fields;

		(* Get the main content we've generated so far *)
		let main_content = Buffer.contents ctx.buf in

		(* Generate closures collected during code generation *)
		if ctx.closures <> [] then begin
			(* Generate forward declarations and implementations in a new buffer *)
			Buffer.clear ctx.buf;

			(* Pre-scan all closures to find nested closures recursively *)
			(* This ensures all forward declarations are emitted before any implementations *)
			let rec scan_expr e =
				match e.eexpr with
				| TFunction f ->
					let free_vars = collect_free_vars f.tf_args f.tf_expr in
					let closure_name = Printf.sprintf "_closure_%d" ctx.closure_counter in
					ctx.closure_counter <- ctx.closure_counter + 1;
					ctx.closures <- (closure_name, f, free_vars) :: ctx.closures;
					scan_expr f.tf_expr
				| TBlock el -> List.iter scan_expr el
				| TIf (econd, eif, eelse) ->
					scan_expr econd; scan_expr eif;
					(match eelse with Some e -> scan_expr e | None -> ())
				| TWhile (econd, ebody, _) -> scan_expr econd; scan_expr ebody
				| TSwitch sw ->
					scan_expr sw.switch_subject;
					List.iter (fun c -> List.iter scan_expr c.case_patterns; scan_expr c.case_expr) sw.switch_cases;
					(match sw.switch_default with Some e -> scan_expr e | None -> ())
				| TTry (e, catches) ->
					scan_expr e;
					List.iter (fun (_, e) -> scan_expr e) catches
				| TReturn (Some e) -> scan_expr e
				| TVar (_, Some e) -> scan_expr e
				| TBinop (_, e1, e2) -> scan_expr e1; scan_expr e2
				| TUnop (_, _, e) -> scan_expr e
				| TCall (e, args) -> scan_expr e; List.iter scan_expr args
				| TParenthesis e -> scan_expr e
				| TField (e, fa) ->
				scan_expr e;
				(* Check for method references that need thunks *)
				(match fa with
				| FClosure (Some (c, _), cf) ->
					let class_name = flat_path c.cl_path in
					let method_name = ident cf.cf_name in
					let thunk_name = Printf.sprintf "__%s_%s_thunk" class_name method_name in
					let is_static = List.exists (fun scf -> scf.cf_name = cf.cf_name) c.cl_ordered_statics in
					let arg_types, ret_type = match follow cf.cf_type with
						| TFun (args, ret) -> (List.map (fun (n, _, t) -> (n, t)) args, ret)
						| _ -> ([], t_dynamic)
					in
					Hashtbl.replace ctx.method_thunks thunk_name (is_static, c.cl_path, cf.cf_name, arg_types, ret_type)
				| _ -> ())
				| TArray (e1, e2) -> scan_expr e1; scan_expr e2
				| TArrayDecl el -> List.iter scan_expr el
				| TObjectDecl fields -> List.iter (fun (_, e) -> scan_expr e) fields
				| TCast (e, _) -> scan_expr e
				| TMeta (_, e) -> scan_expr e
				| TEnumParameter (e, _, _) -> scan_expr e
				| TEnumIndex e -> scan_expr e
				| TNew (_, _, args) -> List.iter scan_expr args
				| TThrow e -> scan_expr e
				| _ -> ()
			in
			(* Save closure counter before pre-scan *)
			let counter_before_prescan = ctx.closure_counter in
			(* Scan all closure bodies to find nested closures *)
			let initial_closures = List.rev ctx.closures in
			ctx.closures <- [];
			List.iter (fun (name, f, captured) ->
				ctx.closures <- (name, f, captured) :: ctx.closures;
				scan_expr f.tf_expr
			) initial_closures;

			(* Forward declarations for ALL closures (including nested ones) *)
			(* Note: The thunks always take FibDynamic params and return FibDynamic *)
			spr ctx "/* Closure forward declarations */\n";
			List.iter (fun (name, f, _captured) ->
				let ret_type = match follow f.tf_type with
					| TFun _ -> "FibClosure*"
					| _ -> s_type ctx f.tf_type
				in
				let filtered_args = filter_void_args f.tf_args in
				(* Forward declaration for typed impl function *)
				let impl_name = name ^ "_impl" in
				let typed_args = List.map (fun (v, _) ->
					s_type_with_name ctx v.v_type (ident v.v_name)
				) filtered_args in
				let all_typed_args = "FibClosure* _closure" :: typed_args in
				let typed_args_str = String.concat ", " all_typed_args in
				print ctx "static %s %s(%s);\n" ret_type impl_name typed_args_str;
				(* Forward declaration for dynamic thunk *)
				let dyn_args = List.mapi (fun i _ -> Printf.sprintf "FibDynamic _arg%d" i) filtered_args in
				let all_dyn_args = "FibClosure* _closure" :: dyn_args in
				let dyn_args_str = String.concat ", " all_dyn_args in
				print ctx "static FibDynamic %s(%s);\n" name dyn_args_str
			) (List.rev ctx.closures);
			spr ctx "\n";

			(* Add main content *)
			spr ctx main_content;

			(* Generate closure implementations *)
			(* Reset closure counter so nested closures get same numbers as pre-scan *)
			ctx.closure_counter <- counter_before_prescan;
			(* Set flag so nested closures don't re-register *)
			ctx.in_closure_impl <- true;
			newline ctx;
			spr ctx "/* Closure implementations */";
			newline ctx;
			List.iter (fun (name, f, captured) ->
				let ret_type = match follow f.tf_type with
					| TFun _ -> "FibClosure*"
					| _ -> s_type ctx f.tf_type
				in
				let filtered_args = filter_void_args f.tf_args in
				let args = List.map (fun (v, _) ->
					s_type_with_name ctx v.v_type (ident v.v_name)
				) filtered_args in
				let all_args = "FibClosure* _closure" :: args in
				let args_str = String.concat ", " all_args in
				(* Generate the typed implementation function as _closure_N_impl *)
				let impl_name = name ^ "_impl" in
				print ctx "static %s %s(%s) {" ret_type impl_name args_str;
				newline ctx;
				ctx.tabs <- "\t";
				(* Cache GC context at closure entry *)
				spr ctx "FIB_GC_CTX;";
				newline ctx;
				(* Add stack frame for Tracy profiling *)
				if ctx.debug_level > 0 then begin
					print ctx "FIB_LOCAL_STACK_FRAME(_fib_pos_%s, \"<closure>\", \"%s\", \"<closure>.%s\", \"generated\", 0);" impl_name name name;
					newline ctx;
					print ctx "FIB_STACKFRAME(&_fib_pos_%s);" impl_name;
					newline ctx
				end;
				ctx.current_ret_type <- Some f.tf_type;
				let old_gc_count = ctx.gc_local_count in
				let old_has_gc_ctx = ctx.has_gc_ctx in
				ctx.gc_local_count <- 0;
				ctx.has_gc_ctx <- true;
				if captured = [] then begin
					spr ctx "(void)_closure;";
					newline ctx
				end;
				List.iteri (fun i v ->
					(* For TFun types, use FibClosure* since all closures are FibClosure in Fiberus *)
					let vtype = match follow v.v_type with
						| TFun _ -> "FibClosure*"
						| _ -> s_type ctx v.v_type
					in
					print ctx "%s %s = " vtype (ident v.v_name);
					if vtype = "int32_t" then
						print ctx "_closure->captures[%d].data.intVal;" i
					else if vtype = "double" then
						print ctx "_closure->captures[%d].data.floatVal;" i
					else if vtype = "bool" then
						print ctx "_closure->captures[%d].data.boolVal;" i
					else if vtype = "FibString*" then
						print ctx "_closure->captures[%d].data.stringVal;" i
					else
						print ctx "(%s)_closure->captures[%d].data.ptrVal;" vtype i;
					newline ctx
				) captured;
				(match f.tf_expr.eexpr with
				| TBlock el ->
					List.iter (fun e ->
						gen_expr ctx e;
						spr ctx ";";
						newline ctx
					) el
				| _ ->
					if ret_type <> "void" then spr ctx "return ";
					gen_expr ctx f.tf_expr;
					spr ctx ";";
					newline ctx);
				if ctx.gc_local_count > 0 then begin
					print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" ctx.gc_local_count;
					newline ctx
				end;
				ctx.gc_local_count <- old_gc_count;
				ctx.has_gc_ctx <- old_has_gc_ctx;
				ctx.tabs <- "";
				spr ctx "}";
				newline ctx;
				newline ctx;
				
				(* Generate the dynamic thunk that takes FibDynamic params and calls the impl *)
				(* This thunk is what gets stored in the FibClosure and called via fib_closure_call_dynamic *)
				let num_args = List.length filtered_args in
				let dyn_args = List.mapi (fun i _ -> Printf.sprintf "FibDynamic _arg%d" i) filtered_args in
				let all_dyn_args = "FibClosure* _closure" :: dyn_args in
				let dyn_args_str = String.concat ", " all_dyn_args in
				let dyn_ret = if ret_type = "void" then "FibDynamic" else "FibDynamic" in
				print ctx "static %s %s(%s) {" dyn_ret name dyn_args_str;
				newline ctx;
				ctx.tabs <- "\t";
				(* Convert each FibDynamic arg to the typed parameter *)
				List.iteri (fun i (v, _) ->
					let vtype = match follow v.v_type with
						| TFun _ -> "FibClosure*"
						| _ -> s_type ctx v.v_type
					in
					let conv = 
						if vtype = "int32_t" then Printf.sprintf "fib_dynamic_to_int(_arg%d)" i
						else if vtype = "double" then Printf.sprintf "fib_dynamic_to_float(_arg%d)" i
						else if vtype = "bool" then Printf.sprintf "fib_dynamic_to_bool(_arg%d)" i
						else if vtype = "FibString*" then Printf.sprintf "fib_dynamic_to_string(_arg%d)" i
						else if vtype = "int64_t" then Printf.sprintf "fib_dynamic_to_int64(_arg%d)" i
						else if vtype = "FibClosure*" then Printf.sprintf "(FibClosure*)fib_dynamic_to_object(_arg%d)" i
						else if vtype = "FibDynamic" then Printf.sprintf "_arg%d" i  (* Pass through unchanged *)
						else Printf.sprintf "(%s)fib_dynamic_to_object(_arg%d)" vtype i
					in
					print ctx "%s _typed%d = %s;" vtype i conv;
					newline ctx
				) filtered_args;
				(* Call the impl function *)
				let typed_call_args = List.mapi (fun i _ -> Printf.sprintf "_typed%d" i) filtered_args in
				let call_args_str = String.concat ", " ("_closure" :: typed_call_args) in
				if ret_type = "void" then begin
					print ctx "%s(%s);" impl_name call_args_str;
					newline ctx;
					spr ctx "return fib_dynamic_null();";
					newline ctx
				end else begin
					(* Convert return value to FibDynamic *)
					let ret_conv = 
						if ret_type = "int32_t" then Printf.sprintf "fib_dynamic_int(%s(%s))" impl_name call_args_str
						else if ret_type = "double" then Printf.sprintf "fib_dynamic_float(%s(%s))" impl_name call_args_str
						else if ret_type = "bool" then Printf.sprintf "fib_dynamic_bool(%s(%s))" impl_name call_args_str
						else if ret_type = "FibString*" then Printf.sprintf "fib_dynamic_string(%s(%s))" impl_name call_args_str
						else if ret_type = "int64_t" then Printf.sprintf "fib_dynamic_int64(%s(%s))" impl_name call_args_str
						else if ret_type = "FibClosure*" then Printf.sprintf "fib_dynamic_object((FibObject*)%s(%s))" impl_name call_args_str
						else if ret_type = "FibDynamic" then Printf.sprintf "%s(%s)" impl_name call_args_str
						else Printf.sprintf "fib_dynamic_object((FibObject*)%s(%s))" impl_name call_args_str
					in
					print ctx "return %s;" ret_conv;
					newline ctx
				end;
				ctx.tabs <- "";
				spr ctx "}";
				newline ctx;
				newline ctx
			) (List.rev ctx.closures);
			ctx.in_closure_impl <- false;
			ctx.closures <- []
		end;

		(* Generate method thunks for any methods used as values *)
		gen_method_thunks ctx;

		(* Clear current class *)
		ctx.current_class <- None;

		Buffer.contents ctx.buf
	end

let gen_enum_impl ctx e =
	if has_enum_flag e EnExtern then "" else begin
		Buffer.clear ctx.buf;
		ctx.tabs <- "";

		print ctx "/* Enum: %s */" (s_type_path e.e_path);
		newline ctx;

		(* Enum constructors *)
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
				spr ctx ") {";
				newline ctx;
				ctx.tabs <- "\t";
				print ctx "%s _e = { .index = %d };" (flat_path e.e_path) ef.ef_index;
				newline ctx;
				let i = ref 0 in
				List.iter (fun (n, _, t) ->
					let arg_type = s_type ctx t in
					print ctx "_e.params[%d] = " !i;
					if is_enum_struct_type arg_type then
						(* Enum struct - box it using fib_dynamic_enum *)
						print ctx "fib_dynamic_enum(&%s, sizeof(%s))" (ident n) arg_type
					else
						gen_box_to_fib_dynamic ctx arg_type (fun () -> spr ctx (ident n));
					spr ctx ";";
					newline ctx;
					incr i
				) filtered_args;
				spr ctx "return _e;";
				newline ctx;
				ctx.tabs <- "";
				spr ctx "}";
				newline ctx
			| _ ->
				print ctx "const %s %s_%s = { .index = %d };"
					(flat_path e.e_path) (flat_path e.e_path) name ef.ef_index;
				newline ctx
		) e.e_constrs;
		newline ctx;

		Buffer.contents ctx.buf
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
	spr ctx "\n";

	(* Fiber yield point macro - uses runtime scheduler_should_yield from scheduler.h *)
	spr ctx "/* Fiber yield point - for loop back-edges (cooperative scheduling only) */\n";
	spr ctx "#define FIBER_YIELD_POINT() do { \\\n";
	spr ctx "\tif (scheduler_should_yield()) fiber_yield(); \\\n";
	spr ctx "} while(0)\n\n";

	(* GC safe point macro - for function entry where stack is clean *)
	spr ctx "/* GC safe point - called at function entry where temporaries are out of scope */\n";
	spr ctx "#define GC_SAFE_POINT() do { \\\n";
	spr ctx "\tgc_maybe_collect(); \\\n";
	spr ctx "\tif (scheduler_should_yield()) fiber_yield(); \\\n";
	spr ctx "} while(0)\n\n";

	(* GC disable scope guard - uses GCC cleanup attribute for RAII-style enable on scope exit *)
	spr ctx "/* GC disable scope guard - auto-enables on ANY scope exit (return, break, etc) */\n";
	spr ctx "static inline void _gc_scope_cleanup(int* p) { (void)p; gc_enable(); }\n";
	spr ctx "#define GC_DISABLE_SCOPE() \\\n";
	spr ctx "\tgc_disable(); \\\n";
	spr ctx "\tint _gc_scope_guard __attribute__((cleanup(_gc_scope_cleanup))) = 0; \\\n";
	spr ctx "\t(void)_gc_scope_guard\n\n";

	(* Helper macros *)
	spr ctx "/* Runtime helpers */\n";
	spr ctx "static inline void fib_trace(FibString* s) {\n";
	spr ctx "\tprintf(\"%s\\n\", fib_string_data(s));\n";
	spr ctx "}\n\n";
	(* fib_dynamic_is_null is now in object.h *)
	spr ctx "static inline bool fib_dynamic_is_string(FibDynamic v) {\n";
	spr ctx "\treturn v.type == FIB_TYPE_STRING;\n";
	spr ctx "}\n\n";
	spr ctx "static inline bool fib_dynamic_is_array(FibDynamic v) {\n";
	spr ctx "\treturn v.type == FIB_TYPE_ARRAY;\n";
	spr ctx "}\n\n";
	spr ctx "/* Memory allocation - GC-tracked objects (inline fast path) */\n";
	spr ctx "static inline void* fib_alloc(size_t size) {\n";
	spr ctx "\treturn gc_alloc_object_inline(size);\n";
	spr ctx "}\n\n";
	spr ctx "/* Context-based allocation (preferred - avoids repeated TLS access) */\n";
	spr ctx "static inline void* fib_alloc_ctx(FibrixLocalAlloc* ctx, size_t size) {\n";
	spr ctx "\treturn gc_alloc_ctx(ctx, size);\n";
	spr ctx "}\n\n";
	spr ctx "/* String comparison */\n";
	spr ctx "static inline bool fib_string_eq(FibString* a, FibString* b) {\n";
	spr ctx "\tif (a == b) return true;\n";
	spr ctx "\tif (a == NULL || b == NULL) return false;\n";
	spr ctx "\treturn strcmp(fib_string_data(a), fib_string_data(b)) == 0;\n";
	spr ctx "}\n\n";
	spr ctx "/* Type coercion helpers - most are now in object.h */\n";
	spr ctx "static inline FibDynamic fib_string_to_dynamic(FibString* s) {\n";
	spr ctx "\treturn fib_dynamic_string(s);\n";
	spr ctx "}\n\n";
	spr ctx "static inline void* fib_dynamic_to_ptr(FibDynamic v) {\n";
	spr ctx "\tif (v.type == FIB_TYPE_ENUM) return v.data.ptrVal;\n";
	spr ctx "\treturn v.data.ptrVal;\n";
	spr ctx "}\n\n";
	spr ctx "/* Type constants for runtime type checking */\n";
	spr ctx "#define FIB_TYPE_STRING_CLASS ((FibDynamic){ .type = FIB_TYPE_CLASS, .data.intVal = FIB_CLASS_ID_STRING })\n\n";
	spr ctx "/* Anonymous object field storage */\n";
	spr ctx "typedef struct FibAnonField {\n";
	spr ctx "\tconst char* name;\n";
	spr ctx "\tFibDynamic value;\n";
	spr ctx "\tstruct FibAnonField* next;\n";
	spr ctx "} FibAnonField;\n\n";
	spr ctx "/* Dynamic field access */\n";
	spr ctx "static inline FibDynamic fib_field_get(FibDynamic obj, const char* name) {\n";
	spr ctx "\tif (obj.type != FIB_TYPE_OBJECT || obj.data.ptrVal == NULL) return fib_dynamic_null();\n";
	spr ctx "\tFibAnonField* field = (FibAnonField*)obj.data.ptrVal;\n";
	spr ctx "\twhile (field != NULL) {\n";
	spr ctx "\t\tif (strcmp(field->name, name) == 0) return field->value;\n";
	spr ctx "\t\tfield = field->next;\n";
	spr ctx "\t}\n";
	spr ctx "\treturn fib_dynamic_null();\n";
	spr ctx "}\n\n";
	spr ctx "/* Fiber API bridge - maps Haxe Fiber class to runtime functions */\n";
	spr ctx "#define Fiber_yield() scheduler_yield()\n";
	spr ctx "static inline bool Fiber_isAlive(Fiber* f) {\n";
	spr ctx "\treturn f != NULL && f->state != FIBER_STATE_DEAD;\n";
	spr ctx "}\n";
	spr ctx "static inline Fiber* Fiber_current(void) {\n";
	spr ctx "\treturn scheduler_current();\n";
	spr ctx "}\n";
	spr ctx "/* Fiber_spawn wrapper - adapts FibDynamic-taking functions to void* */\n";
	spr ctx "typedef void (*FibDynamicFunc)(FibDynamic);\n";
	spr ctx "static void _fib_spawn_trampoline(void* arg) {\n";
	spr ctx "\tFibDynamicFunc fn = (FibDynamicFunc)arg;\n";
	spr ctx "\tif (fn) fn(fib_dynamic_null());\n";
	spr ctx "}\n";
	spr ctx "static inline Fiber* Fiber_spawn(FibDynamicFunc fn) {\n";
	spr ctx "\treturn scheduler_spawn(_fib_spawn_trampoline, (void*)fn);\n";
	spr ctx "}\n";
	spr ctx "/* Fiber_spawn_closure - spawns a fiber with a closure */\n";
	spr ctx "typedef void (*FibClosureFunc)(FibClosure*, FibDynamic);\n";
	spr ctx "/* GDB breakpoint function - called when closure corruption detected */\n";
	spr ctx "__attribute__((noinline)) static void _fib_closure_corruption_trap(\n";
	spr ctx "\tFibClosure* closure, void* arg, void* gc_arg,\n";
	spr ctx "\tvoid* actual_clazz, void* expected_clazz, uint64_t actual_magic) {\n";
	spr ctx "\tfprintf(stderr, \"\\n[FATAL] CLOSURE CORRUPTION DETECTED!\\n\");\n";
	spr ctx "\tfprintf(stderr, \"  closure     = %p\\n\", (void*)closure);\n";
	spr ctx "\tfprintf(stderr, \"  arg         = %p\\n\", arg);\n";
	spr ctx "\tfprintf(stderr, \"  gc_arg      = %p\\n\", gc_arg);\n";
	spr ctx "\tfprintf(stderr, \"  clazz       = %p (expected %p)\\n\", actual_clazz, expected_clazz);\n";
	spr ctx "\tfprintf(stderr, \"  magic       = 0x%016lx (expected 0x%016lx)\\n\",\n";
	spr ctx "\t\t(unsigned long)actual_magic, (unsigned long)FIB_CLOSURE_MAGIC);\n";
	spr ctx "\tuint64_t* p = (uint64_t*)closure;\n";
	spr ctx "\tfor (int i = 0; i < 8; i++) fprintf(stderr, \"  [%d] %p: 0x%016lx\\n\", i, (void*)&p[i], (unsigned long)p[i]);\n";
	spr ctx "\t__builtin_trap();\n";
	spr ctx "}\n";
	spr ctx "static void _fib_spawn_closure_trampoline(void* arg) {\n";
	spr ctx "\t/* Get closure from fiber's gc_arg which is updated by GC if evacuated.\n";
	spr ctx "\t * Fall back to arg if fiber_current() fails (shouldn't happen). */\n";
	spr ctx "\tFiber* self = fiber_current();\n";
	spr ctx "\tFibClosure* closure = (FibClosure*)(self && self->gc_arg ? self->gc_arg : arg);\n";
	spr ctx "\t/* Validate closure before calling - check magic and clazz */\n";
	spr ctx "\tif (closure) {\n";
	spr ctx "\t\tvolatile FibClosure* vclosure = closure;\n";
	spr ctx "\t\tif (vclosure->magic != FIB_CLOSURE_MAGIC || vclosure->clazz != &fib_closure_class) {\n";
	spr ctx "\t\t\t_fib_closure_corruption_trap(closure, arg, self ? self->gc_arg : NULL,\n";
	spr ctx "\t\t\t\t(void*)vclosure->clazz, (void*)&fib_closure_class, vclosure->magic);\n";
	spr ctx "\t\t}\n";
	spr ctx "\t\tFibClosureFunc fn = (FibClosureFunc)vclosure->fn;\n";
	spr ctx "\t\tfn(closure, fib_dynamic_null());\n";
	spr ctx "\t}\n";
	spr ctx "}\n";
	spr ctx "static inline Fiber* Fiber_spawn_closure(FibClosure* closure) {\n";
	spr ctx "\t/* Push temp root to protect closure during fiber creation.\n";
	spr ctx "\t * The closure is in a caller-saved register (rdi) at this point,\n";
	spr ctx "\t * and GC could run during scheduler_spawn before fiber->gc_arg is set. */\n";
	spr ctx "\tgc_push_temp_root((void**)&closure);\n";
	spr ctx "\tFiber* fiber = scheduler_spawn(_fib_spawn_closure_trampoline, (void*)closure);\n";
	spr ctx "\tgc_pop_temp_roots(1);\n";
	spr ctx "\treturn fiber;\n";
	spr ctx "}\n";
	spr ctx "/* Fiber MT API - multithreading support */\n";
	spr ctx "static inline int Fiber_createWorkers(int count) {\n";
	spr ctx "\treturn scheduler_create_workers(count);\n";
	spr ctx "}\n";
	spr ctx "static inline int Fiber_getThreadCount(void) {\n";
	spr ctx "\treturn scheduler_get_thread_count();\n";
	spr ctx "}\n";
	spr ctx "static inline int Fiber_getWorkerCount(void) {\n";
	spr ctx "\treturn scheduler_get_worker_count();\n";
	spr ctx "}\n";
	spr ctx "/* Fiber_spawnOn - spawn fiber on specific thread */\n";
	spr ctx "static void _fib_spawn_on_closure_trampoline(void* arg) {\n";
	spr ctx "\tFiber* self = fiber_current();\n";
	spr ctx "\tFibClosure* closure = (FibClosure*)(self && self->gc_arg ? self->gc_arg : arg);\n";
	spr ctx "\tif (closure) {\n";
	spr ctx "\t\tvolatile FibClosure* vclosure = closure;\n";
	spr ctx "\t\tif (vclosure->clazz != &fib_closure_class) {\n";
	spr ctx "\t\t\tfprintf(stderr, \"[FATAL] Closure wrong class (spawnOn)! closure=%p clazz=%p expected=%p fn=%p arg=%p gc_arg=%p\\n\",\n";
	spr ctx "\t\t\t\t(void*)closure, (void*)vclosure->clazz, (void*)&fib_closure_class, vclosure->fn, arg, self ? self->gc_arg : NULL);\n";
	spr ctx "\t\t\t__builtin_trap();\n";
	spr ctx "\t\t}\n";
	spr ctx "\t\tFibClosureFunc fn = (FibClosureFunc)vclosure->fn;\n";
	spr ctx "\t\tfn(closure, fib_dynamic_null());\n";
	spr ctx "\t}\n";
	spr ctx "}\n";
	spr ctx "static inline Fiber* Fiber_spawnOn(int threadId, FibClosure* closure) {\n";
	spr ctx "\t/* Push temp root to protect closure during fiber creation */\n";
	spr ctx "\tgc_push_temp_root((void**)&closure);\n";
	spr ctx "\tFiber* fiber = scheduler_spawn_on(threadId, _fib_spawn_on_closure_trampoline, (void*)closure);\n";
	spr ctx "\tgc_pop_temp_roots(1);\n";
	spr ctx "\treturn fiber;\n";
	spr ctx "}\n";
	spr ctx "/* Fiber_spawnAny - spawn fiber on least-loaded thread */\n";
	spr ctx "static inline Fiber* Fiber_spawnAny(FibClosure* closure) {\n";
	spr ctx "\t/* Push temp root to protect closure during fiber creation */\n";
	spr ctx "\tgc_push_temp_root((void**)&closure);\n";
	spr ctx "\tFiber* fiber = scheduler_spawn_any(_fib_spawn_on_closure_trampoline, (void*)closure);\n";
	spr ctx "\tgc_pop_temp_roots(1);\n";
	spr ctx "\treturn fiber;\n";
	spr ctx "}\n\n";
	spr ctx "/* Counter API bridge - maps Haxe Counter class to runtime functions */\n";
	spr ctx "static inline Counter* Counter_create(int initialValue) {\n";
	spr ctx "\treturn counter_create(initialValue);\n";
	spr ctx "}\n";
	spr ctx "static inline void Counter_add(Counter* c, int delta) {\n";
	spr ctx "\tcounter_add(c, delta);\n";
	spr ctx "}\n";
	spr ctx "static inline int Counter_decrement(Counter* c) {\n";
	spr ctx "\treturn counter_decrement(c);\n";
	spr ctx "}\n";
	spr ctx "static inline void Counter_wait(Counter* c, int target) {\n";
	spr ctx "\tcounter_wait(c, target);\n";
	spr ctx "}\n";
	spr ctx "static inline void Counter_done(Counter* c) {\n";
	spr ctx "\tcounter_done(c);\n";
	spr ctx "}\n";
	spr ctx "static inline void Counter_waitAndDone(Counter* c, int target) {\n";
	spr ctx "\tcounter_wait_and_done(c, target);\n";
	spr ctx "}\n";
	spr ctx "static inline int Counter_getValue(Counter* c) {\n";
	spr ctx "\treturn counter_get_value(c);\n";
	spr ctx "}\n\n";
	spr ctx "/* Anonymous objects */\n";
	spr ctx "static inline FibDynamic fib_anon_new(void) {\n";
	spr ctx "\t/* Create empty anonymous object (fields added with fib_anon_set) */\n";
	spr ctx "\treturn (FibDynamic){ .type = FIB_TYPE_OBJECT, .data.ptrVal = NULL };\n";
	spr ctx "}\n";
	spr ctx "static inline void fib_anon_set(FibDynamic* obj, const char* name, FibDynamic value) {\n";
	spr ctx "\tif (obj->type != FIB_TYPE_OBJECT) return;\n";
	spr ctx "\t/* Check if field already exists */\n";
	spr ctx "\tFibAnonField* field = (FibAnonField*)obj->data.ptrVal;\n";
	spr ctx "\twhile (field != NULL) {\n";
	spr ctx "\t\tif (strcmp(field->name, name) == 0) { field->value = value; return; }\n";
	spr ctx "\t\tfield = field->next;\n";
	spr ctx "\t}\n";
	spr ctx "\t/* Add new field */\n";
	spr ctx "\tFibAnonField* newField = (FibAnonField*)malloc(sizeof(FibAnonField));\n";
	spr ctx "\tnewField->name = name;\n";
	spr ctx "\tnewField->value = value;\n";
	spr ctx "\tnewField->next = (FibAnonField*)obj->data.ptrVal;\n";
	spr ctx "\tobj->data.ptrVal = newField;\n";
	spr ctx "}\n\n";
	spr ctx "/* GC API bridge - maps Haxe GC class to runtime functions */\n";
	spr ctx "#define GC_collect() gc_collect()\n";
	spr ctx "#define GC_printStats() gc_print_stats()\n";
	spr ctx "static inline void GC_setDebug(bool enabled) {\n";
	spr ctx "\tgc_set_debug(enabled);\n";
	spr ctx "}\n";
	spr ctx "static inline void GC_setThreshold(int bytes) {\n";
	spr ctx "\tgc_set_threshold((size_t)bytes);\n";
	spr ctx "}\n";
	spr ctx "static inline int GC_getThreshold(void) {\n";
	spr ctx "\treturn (int)gc_get_threshold();\n";
	spr ctx "}\n";
	spr ctx "/* GC_stats returns an anonymous object with GC statistics */\n";
	spr ctx "static inline FibDynamic GC_stats(void) {\n";
	spr ctx "\tconst GCStats* s = gc_get_stats();\n";
	spr ctx "\tFibDynamic obj = fib_anon_new();\n";
	spr ctx "\tfib_anon_set(&obj, \"totalAllocations\", fib_dynamic_int((int)s->total_allocations));\n";
	spr ctx "\tfib_anon_set(&obj, \"totalBytesAllocated\", fib_dynamic_int((int)s->total_bytes_allocated));\n";
	spr ctx "\tfib_anon_set(&obj, \"currentHeapSize\", fib_dynamic_int((int)s->current_heap_size));\n";
	spr ctx "\tfib_anon_set(&obj, \"peakHeapSize\", fib_dynamic_int((int)s->peak_heap_size));\n";
	spr ctx "\tfib_anon_set(&obj, \"currentObjectCount\", fib_dynamic_int((int)s->current_object_count));\n";
	spr ctx "\tfib_anon_set(&obj, \"collectionCount\", fib_dynamic_int((int)s->collection_count));\n";
	spr ctx "\tfib_anon_set(&obj, \"objectsMarked\", fib_dynamic_int((int)s->objects_marked));\n";
	spr ctx "\tfib_anon_set(&obj, \"objectsSwept\", fib_dynamic_int((int)s->objects_swept));\n";
	spr ctx "\tfib_anon_set(&obj, \"bytesFreed\", fib_dynamic_int((int)s->bytes_freed));\n";
	spr ctx "\tfib_anon_set(&obj, \"lastMarkTimeMs\", fib_dynamic_float((double)s->last_mark_time_us / 1000.0));\n";
	spr ctx "\tfib_anon_set(&obj, \"lastSweepTimeMs\", fib_dynamic_float((double)s->last_sweep_time_us / 1000.0));\n";
	spr ctx "\tfib_anon_set(&obj, \"totalGcTimeMs\", fib_dynamic_float((double)s->total_gc_time_us / 1000.0));\n";
	spr ctx "\tfib_anon_set(&obj, \"fibersScanned\", fib_dynamic_int((int)s->fibers_scanned));\n";
	spr ctx "\tfib_anon_set(&obj, \"stackBytesScanned\", fib_dynamic_int((int)s->stack_bytes_scanned));\n";
	spr ctx "\t/* Generational GC stats */\n";
	spr ctx "\tfib_anon_set(&obj, \"minorCollections\", fib_dynamic_int((int)s->minor_collections));\n";
	spr ctx "\tfib_anon_set(&obj, \"minorObjectsEvacuated\", fib_dynamic_int((int)s->minor_objects_evacuated));\n";
	spr ctx "\tfib_anon_set(&obj, \"minorBytesEvacuated\", fib_dynamic_int((int)s->minor_bytes_evacuated));\n";
	spr ctx "\tfib_anon_set(&obj, \"lastMinorTimeMs\", fib_dynamic_float((double)s->last_minor_time_us / 1000.0));\n";
	spr ctx "\tfib_anon_set(&obj, \"totalMinorTimeMs\", fib_dynamic_float((double)s->total_minor_time_us / 1000.0));\n";
	spr ctx "\tfib_anon_set(&obj, \"writeBarriersTriggered\", fib_dynamic_int((int)s->write_barriers_triggered));\n";
	spr ctx "\treturn obj;\n";
	spr ctx "}\n\n";
	spr ctx "/* Stub for haxe.Exception base class */\n";
	spr ctx "typedef struct haxe_Exception haxe_Exception;\n";
	spr ctx "struct haxe_Exception {\n";
	spr ctx "\tFibObject _obj;\n";
	spr ctx "\tFibString* message;\n";
	spr ctx "};\n";
	spr ctx "extern FibClass haxe_Exception_class;\n";
	spr ctx "static inline FibString* haxe_Exception_toString(haxe_Exception* this) {\n";
	spr ctx "\treturn this ? this->message : fib_string_new(\"Exception\");\n";
	spr ctx "}\n";
	spr ctx "void haxe_Exception_init(haxe_Exception* this, FibString* message, haxe_Exception* previous, FibDynamic native);\n";
	spr ctx "haxe_Exception* haxe_Exception_new(FibString* message, haxe_Exception* previous, FibDynamic native);\n\n";

	(* Exception handling using setjmp/longjmp - per-fiber exception stack with thread-local fallback *)
	spr ctx "/* Exception handling - per-fiber stacks with thread-local fallback */\n";
	spr ctx "#define FIB_TLS_EXC_STACK_SIZE 64\n";
	spr ctx "extern __thread jmp_buf* _fib_tls_exc_stack[FIB_TLS_EXC_STACK_SIZE];\n";
	spr ctx "extern __thread int _fib_tls_exc_stack_top;\n";
	spr ctx "extern __thread FibDynamic _fib_current_exception;\n\n";
	spr ctx "static inline void fib_exc_push(jmp_buf* buf) {\n";
	spr ctx "\tFiber* f = fiber_current();\n";
	spr ctx "\tif (f) {\n";
	spr ctx "\t\tif (f->exc_stack_top < FIBER_EXC_STACK_SIZE) {\n";
	spr ctx "\t\t\tf->exc_stack[f->exc_stack_top++] = buf;\n";
	spr ctx "\t\t}\n";
	spr ctx "\t} else {\n";
	spr ctx "\t\t/* No fiber context - use thread-local fallback */\n";
	spr ctx "\t\tif (_fib_tls_exc_stack_top < FIB_TLS_EXC_STACK_SIZE) {\n";
	spr ctx "\t\t\t_fib_tls_exc_stack[_fib_tls_exc_stack_top++] = buf;\n";
	spr ctx "\t\t}\n";
	spr ctx "\t}\n";
	spr ctx "}\n\n";
	spr ctx "static inline void fib_exc_pop(void) {\n";
	spr ctx "\tFiber* f = fiber_current();\n";
	spr ctx "\tif (f) {\n";
	spr ctx "\t\tif (f->exc_stack_top > 0) f->exc_stack_top--;\n";
	spr ctx "\t} else {\n";
	spr ctx "\t\tif (_fib_tls_exc_stack_top > 0) _fib_tls_exc_stack_top--;\n";
	spr ctx "\t}\n";
	spr ctx "}\n\n";
	spr ctx "static inline FibDynamic fib_current_exception(void) {\n";
	spr ctx "\treturn _fib_current_exception;\n";
	spr ctx "}\n\n";
	spr ctx "void fib_throw(FibDynamic exc);\n";
	spr ctx "void fiberus_register_gc_roots(void);\n\n";

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
			(match c.cl_constructor with
			| None ->
				(* Simple: generate inline implementations *)
				print ctx "static inline void %s_init(%s* this) { (void)this; }" class_name class_name;
				newline ctx;
				print ctx "static inline %s* %s_new(void) {" class_name class_name;
				newline ctx;
				print ctx "\t%s* this = gc_alloc_object_inline(sizeof(%s));" class_name class_name;
				newline ctx;
				print ctx "\t((FibObject*)this)->clazz = &%s_class;" class_name;
				newline ctx;
				print ctx "\treturn this;";
				newline ctx;
				spr ctx "}";
				newline ctx
			| Some cf ->
				(match cf.cf_expr with
				| Some { eexpr = TFunction f } ->
					let filtered_args = filter_void_args f.tf_args in
					let args = List.map (fun (v, _) ->
						s_type_with_name ctx v.v_type (ident v.v_name)
					) filtered_args in
					let args_str = String.concat ", " args in
					let is_simple = is_simple_constructor ctx f in
					if is_simple then begin
						(* Generate inline _init *)
						print ctx "static inline void %s_init(%s* this%s) {" class_name class_name
							(if args = [] then "" else ", " ^ args_str);
						newline ctx;
						(* Generate field assignments inline *)
						let gen_inline_expr e =
							match e.eexpr with
							| TBlock el ->
								List.iter (fun e ->
									match e.eexpr with
									| TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, value)
									| TParenthesis { eexpr = TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, value) } ->
										print ctx "\tthis->%s = " (ident cf.cf_name);
										gen_value ctx value;
										spr ctx ";";
										newline ctx
									| _ -> ()
								) el
							| TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, value)
							| TParenthesis { eexpr = TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, value) } ->
								print ctx "\tthis->%s = " (ident cf.cf_name);
								gen_value ctx value;
								spr ctx ";";
								newline ctx
							| _ -> ()
						in
						gen_inline_expr f.tf_expr;
						spr ctx "}";
						newline ctx;
						(* Generate inline _new *)
						let args_str_for_new = if args = [] then "void" else args_str in
						let arg_names = List.map (fun (v, _) -> ident v.v_name) filtered_args in
						print ctx "static inline %s* %s_new(%s) {" class_name class_name args_str_for_new;
						newline ctx;
						print ctx "\t%s* this = gc_alloc_object_inline(sizeof(%s));" class_name class_name;
						newline ctx;
						print ctx "\t((FibObject*)this)->clazz = &%s_class;" class_name;
						newline ctx;
						print ctx "\t%s_init(this%s);" class_name
							(if arg_names = [] then "" else ", " ^ String.concat ", " arg_names);
						newline ctx;
						spr ctx "\treturn this;";
						newline ctx;
						spr ctx "}";
						newline ctx
					end else begin
						(* Non-simple: just declarations *)
						print ctx "void %s_init(%s* this%s);" class_name class_name
							(if args = [] then "" else ", " ^ args_str);
						newline ctx;
						let args_str_for_new = if args = [] then "void" else args_str in
						print ctx "%s* %s_new(%s);" class_name class_name args_str_for_new;
						newline ctx
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
	Buffer.add_string buf "\t((FibObject*)this)->clazz = &haxe_Exception_class;\n";
	Buffer.add_string buf "\tthis->message = message ? message : fib_string_new(\"Exception\");\n";
	Buffer.add_string buf "}\n\n";
	Buffer.add_string buf "haxe_Exception* haxe_Exception_new(FibString* message, haxe_Exception* previous, FibDynamic native) {\n";
	Buffer.add_string buf "\thaxe_Exception* this = fib_alloc(sizeof(haxe_Exception));\n";
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
		in_value = false;
		id_counter = 0;
		local_types = Hashtbl.create 0;
		current_ret_type = None;
		current_class = None;
		class_id_counter = 100;  (* Start at 100 to reserve 0-99 for built-in classes *)
		class_ids = Hashtbl.create 0;
		debug_level = debug_level;
		last_line = 0;
		closure_counter = 0;
		closures = [];
		in_closure_impl = false;
		closure_fwd_decls = Buffer.create 256;
		in_fiber_spawn = false;
		gc_local_count = 0;
		loop_depth = 0;
		has_gc_ctx = false;
		stack_alloc_vars = Hashtbl.create 0;
		vtable_ctx = None;
		method_thunks = Hashtbl.create 16;
	} in

	(* Build vtables for all classes - enables virtual method dispatch *)
	ctx.vtable_ctx <- Some (GenfiberusVtable.build_all_vtables com.types);

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
					if needs_gc_root ctx cf.cf_type then begin
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

	(* Generate the main fiber entry function - runs the Haxe main code as a fiber *)
	spr ctx "/* Main fiber entry - runs the Haxe main code as a fiber.\n";
	spr ctx " * This allows the main thread to participate in work-stealing\n";
	spr ctx " * and provides a uniform execution model where all code runs in fibers. */\n";
	spr ctx "static void _fiberus_main_entry(void* arg) {\n";
	spr ctx "\t(void)arg;\n";
	(match com.main.main_expr with
	| Some e ->
		ctx.tabs <- "\t";
		gen_expr ctx e;
		spr ctx ";";
		ctx.tabs <- ""
	| None ->
		spr ctx "\t/* No main expression */");
	spr ctx "\n}\n\n";

	spr ctx "int main(int argc, char** argv) {\n";
	spr ctx "\t(void)argc; (void)argv;\n";
	spr ctx "\tvolatile int _gc_stack_base_marker;\n";
	spr ctx "\tgc_set_stack_base((void*)&_gc_stack_base_marker);\n";
	spr ctx "\tscheduler_init();\n";
	spr ctx "\tfiberus_register_gc_roots();\n\n";
	(* Call boot functions to initialize static fields - must happen before main fiber *)
	if boot_classes <> [] then begin
		spr ctx "\t/* Static field initialization (before main fiber) */\n";
		List.iter (fun class_name ->
			print ctx "\t%s___boot();\n" class_name
		) boot_classes;
		spr ctx "\n"
	end;
	(* Spawn main as a fiber on thread 0 (main thread's queue) *)
	spr ctx "\t/* Spawn main code as fiber on thread 0 (main thread's queue) */\n";
	spr ctx "\tscheduler_spawn(_fiberus_main_entry, NULL);\n\n";
	(* Tracy zone wraps scheduler_run which includes main fiber execution *)
	spr ctx "#ifdef FIBERUS_TRACY\n";
	spr ctx "\tTracyCZoneN(_main_zone, \"main\", 1);\n";
	spr ctx "#endif\n\n";
	spr ctx "\t/* Run fibers until all complete (main thread participates in work-stealing) */\n";
	spr ctx "\tscheduler_run();\n\n";
	spr ctx "#ifdef FIBERUS_TRACY\n";
	spr ctx "\tTracyCZoneEnd(_main_zone);\n";
	spr ctx "#endif\n";
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
	List.iter (fun filename ->
		Buffer.add_string build_xml (Printf.sprintf "  <file name=\"%s\"/>\n" filename)
	) (List.rev !generated_files);
	Buffer.add_string build_xml "</files>\n\n";
	Buffer.add_string build_xml "<!-- Build executable -->\n";
	Buffer.add_string build_xml "<target id=\"default\" output=\"Main\" tool=\"linker\" toolid=\"exe\">\n";
	Buffer.add_string build_xml "  <files id=\"haxe\"/>\n";
	Buffer.add_string build_xml "  <files id=\"runtime\"/>\n";
	Buffer.add_string build_xml "  <files id=\"gc\"/>\n";
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

	(* Write Options.txt for build dependency tracking *)
	let options_file = dir ^ "/Options.txt" in
	let och = open_out_bin options_file in
	PMap.iter (fun name value ->
		match name with
		| "true" | "sys" | "dce" | "fiberus" | "debug" -> ()
		| _ -> output_string och (Printf.sprintf "%s=%s\n" name value)
	) com.defines.Define.values;
	close_out och;

	com.print (Printf.sprintf "Generated %d source files\n" (List.length !generated_files));

	(* Run fiberus build tool unless -D no-compilation *)
	if not (Gctx.defined com Define.NoCompilation) then begin
		let old_dir = Sys.getcwd () in
		Sys.chdir dir;
		let cmd = ref ["run"; "fiberus"; "Build.xml"] in
		if com.debug then cmd := !cmd @ ["-Ddebug"];
		com.print ("haxelib " ^ (String.concat " " !cmd) ^ "\n");
		if com.run_command_args "haxelib" !cmd <> 0 then failwith "Build failed";
		Sys.chdir old_dir
	end
