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
	mutable closures : tc_closure list;  (* Collected closures (C-AST) *)
	mutable in_closure_impl : bool;  (* True when generating closure implementations *)
	mutable in_fiber_spawn : bool;  (* True when generating a closure for Fiber.spawn *)
	mutable spawn_counter : int;  (* Counter for unique Fiber.spawn temp variable names *)
	(* GC root tracking: count of gc_push_temp_root calls in current function *)
	mutable gc_local_count : int;
	(* Loop depth tracking: skip yield points in deeply nested loops *)
	mutable loop_depth : int;
	(* GC context: has FIB_GC_CTX been emitted in this function? *)
	mutable has_gc_ctx : bool;
	(* Escape analysis: set of variable IDs that can be stack-allocated *)
	mutable stack_alloc_vars : (int, tclass) Hashtbl.t;
	(* Vtable context for virtual method dispatch *)
	mutable vtable_ctx : FiberusVtable.vtable_context option;
	(* Method thunks: methods that are used as values and need closure wrappers *)
	(* Maps thunk_name -> (is_static, class_path, method_name, arg_types, ret_type) *)
	mutable method_thunks : (string, bool * path * string * (string * Type.t) list * Type.t) Hashtbl.t;
}

(* Escape analysis functions (can_stack_alloc_class, analyze_escapes, 
   filter_void_args, extract_param_field_mapping) now imported from FiberusEscape *)

(* is_void_type now imported from FiberusGenEnum *)

(* ident, flat_path, s_path, escape_string now imported from FiberusStrings *)

let spr ctx s =
	Buffer.add_string ctx.buf s

let print ctx =
	Printf.kprintf (fun s -> Buffer.add_string ctx.buf s)

let newline ctx =
	print ctx "\n%s" ctx.tabs

let temp ctx =
	ctx.id_counter <- ctx.id_counter + 1;
	"_hx_tmp" ^ string_of_int ctx.id_counter

(* ends_with_return now imported from FiberusEscape *)

(* ===========================================================================
 * C-AST Pipeline Helper
 * ===========================================================================
 * Converts a Haxe expression to C-AST and emits it via FiberusSourceWriter.
 * This is used during the migration from direct string emission to C-AST.
 *)

(* Create a conversion context from the genfiberus context *)
let make_conv_ctx ctx =
  {
    FiberusConvert.current_class = ctx.current_class;
    FiberusConvert.current_class_name = Option.map (fun c -> flat_path c.cl_path) ctx.current_class;
    FiberusConvert.vtable_ctx = ctx.vtable_ctx;
    FiberusConvert.current_ret_type = Option.map tc_type_of ctx.current_ret_type;
    FiberusConvert.gc_local_count = ctx.gc_local_count;
    FiberusConvert.loop_depth = 0;
    FiberusConvert.closure_counter = ctx.closure_counter;
    FiberusConvert.closures = [];
    FiberusConvert.in_fiber_spawn = ctx.in_fiber_spawn;
    FiberusConvert.spawn_counter = ctx.spawn_counter;
    FiberusConvert.debug_level = ctx.debug_level;
  }

(* Sync closure state from conv_ctx back to genfiberus ctx, return collected closures *)
let sync_closures_from_conv ctx conv_ctx =
  ctx.closure_counter <- conv_ctx.FiberusConvert.closure_counter;
  ctx.spawn_counter <- conv_ctx.FiberusConvert.spawn_counter;
  FiberusConvert.get_closures conv_ctx

(* Emit a C-AST expression directly to the buffer.
 * NOTE: pending_stmts are NOT emitted here - they must be emitted by the caller
 * at statement level before this expression is evaluated. Use emit_cexpr_as_stmt
 * if you need pending_stmts to be emitted. *)
let emit_cexpr ctx (cexpr : tc_expr) =
  let w = FiberusSourceWriter.create () in
  FiberusSourceWriter.write_expr w cexpr;
  spr ctx (FiberusSourceWriter.contents w)

(* Emit a C-AST expression and return its gc_roots count for later cleanup.
 * Used when the expression is part of a statement that needs to pop roots.
 * NOTE: pending_stmts are NOT emitted here - they must be emitted by the caller. *)
let emit_cexpr_with_roots ctx (cexpr : tc_expr) : int =
  let w = FiberusSourceWriter.create () in
  FiberusSourceWriter.write_expr w cexpr;
  spr ctx (FiberusSourceWriter.contents w);
  cexpr.gc_roots

(* Emit gc_pop for expression-level roots if needed.
 * Call this after emitting an expression that may have unpaired roots. *)
let emit_expr_gc_pop ctx gc_roots =
  if gc_roots > 0 then begin
    print ctx "; gc_pop_temp_roots_ctx(FIB_CTX, %d)" gc_roots
  end

(* Emit pending_stmts from an expression, then the expression itself.
 * This is for statement-level contexts where pending_stmts can be emitted. *)
let emit_cexpr_with_pending ctx (cexpr : tc_expr) =
  let w = FiberusSourceWriter.create () in
  (* Emit any pending statements first *)
  List.iter (FiberusSourceWriter.write_stmt w) cexpr.pending_stmts;
  (* Emit the expression *)
  FiberusSourceWriter.write_expr w cexpr;
  spr ctx (FiberusSourceWriter.contents w)

(* Emit a C-AST statement directly to the buffer (without trailing newline) *)
let emit_cstmt_inline ctx (cstmt : tc_stmt) =
  let w = FiberusSourceWriter.create () in
  FiberusSourceWriter.write_stmt w cstmt;
  (* Remove trailing newline that write_stmt adds *)
  let s = FiberusSourceWriter.contents w in
  let s = if String.length s > 0 && s.[String.length s - 1] = '\n' 
          then String.sub s 0 (String.length s - 1) else s in
  spr ctx s

(* Emit a C-AST statement without trailing semicolon or newline - for gen_value context *)
let emit_cstmt_no_semi ctx (cstmt : tc_stmt) =
  let w = FiberusSourceWriter.create () in
  FiberusSourceWriter.write_stmt w cstmt;
  let s = FiberusSourceWriter.contents w in
  (* Strip trailing newline and semicolon *)
  let s = String.trim s in
  let s = if String.length s > 0 && s.[String.length s - 1] = ';' 
          then String.sub s 0 (String.length s - 1) else s in
  spr ctx s

(* Convert a Haxe expression to C-AST and emit it *)
let gen_value_via_cast ctx e =
  let conv_ctx = make_conv_ctx ctx in
  let cexpr = FiberusConvert.convert_expr conv_ctx e in
  emit_cexpr ctx cexpr

(* Convert a Haxe expression to C-AST, emit it, and return gc_roots count.
 * Used for initializers where we need to pop expression roots after. *)
let gen_value_with_roots ctx e : int =
  let conv_ctx = make_conv_ctx ctx in
  let cexpr = FiberusConvert.convert_expr conv_ctx e in
  emit_cexpr_with_roots ctx cexpr

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

(* s_path, flat_path, strip_file, escape_string now imported from FiberusStrings *)
(* Note: s_path is available as s_type_path in FiberusStrings *)

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

(* Generate a function pointer CAST expression for closure calls.
 * For normal return types: "(ret_type (*)(fn_args))"
 * For closure return types (TFun): returns FibClosure* since all closures are FibClosure
 *)
let s_func_ptr_cast _ctx ret_type fn_args_str =
	let full_args = if fn_args_str = "" then "FibClosure*" else "FibClosure*, " ^ fn_args_str in
	match follow ret_type with
	| TFun _ ->
		(* Return type is a function - closures return FibClosure* for other closures *)
		Printf.sprintf "(FibClosure* (*)(%s))" full_args
	| _ ->
		(* Normal return type - standard function pointer cast *)
		Printf.sprintf "(%s (*)(%s))" (tc_type_to_string (tc_type_of ret_type)) full_args

(* Check if a type needs GC root registration - delegates to FiberusTypeUtils *)
let needs_gc_root _ctx t =
	haxe_type_needs_gc_root t

(* is_simple_constructor now imported from FiberusGenClass *)

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

(* Type predicates (is_string_type, is_dynamic_type, is_array_type) 
   now imported from FiberusBuiltins *)

(* tc_type-based predicates *)

(* Check if type is a "class pointer" - pointer types excluding FibString*, FibArray*, FibDynamic* *)
let is_class_pointer_tc = function
	| TCFibClass _ -> true
	| TCFibArray TCArrGeneric -> false  (* FibArray* excluded *)
	| TCFibArray _ -> true  (* Specialized arrays included *)
	| TCFibIntMap | TCFibStringMap | TCFibInt64Map | TCFibObjectMap -> true
	| TCFibBytesData -> true
	| _ -> false

(* Check if type is an enum struct *)
let is_enum_struct_tc = function
	| TCFibEnum _ -> true
	| _ -> false

(* Check if type ends with '*' (is a pointer that needs GC marking) *)
let needs_gc_marking_tc = function
	| TCFibString | TCFibArray _ | TCFibClass _ | TCFibClosure 
	| TCFibObject | TCFibIntMap | TCFibStringMap 
	| TCFibInt64Map | TCFibObjectMap | TCFibBytesData -> true
	| TCPointer _ -> true
	(* Note: FibDynamic is NOT a pointer (struct), so excluded *)
	| _ -> false

(* String-based wrappers removed - all callers now use tc_type versions *)

(* Generate boxing wrapper for value to FibDynamic using tc_type *)
let gen_box_to_fib_dynamic_tc ctx tc_type gen_inner =
	match tc_type with
	| TCFibDynamic -> gen_inner ()
	| TCInt32 -> spr ctx "fib_dynamic_int("; gen_inner (); spr ctx ")"
	| TCFloat64 -> spr ctx "fib_dynamic_float("; gen_inner (); spr ctx ")"
	| TCBool -> spr ctx "fib_dynamic_bool("; gen_inner (); spr ctx ")"
	| TCFibString -> spr ctx "fib_dynamic_string("; gen_inner (); spr ctx ")"
	| TCFibArray _ -> spr ctx "fib_dynamic_array("; gen_inner (); spr ctx ")"
	| TCFibClass _ -> spr ctx "fib_dynamic_object((FibObject*)"; gen_inner (); spr ctx ")"
	| TCFibEnum name ->
		(* Enum struct - box with fib_dynamic_enum *)
		print ctx "({ %s _enum_tmp = " name; gen_inner (); print ctx "; fib_dynamic_enum(&_enum_tmp, sizeof(%s)); })" name
	| _ -> gen_inner ()

(* String-based version for compatibility *)
let gen_box_to_fib_dynamic ctx type_str gen_inner =
	gen_box_to_fib_dynamic_tc ctx (tc_type_of_string type_str) gen_inner

(* Get actual tc_type from expression, unwrapping casts/meta.
   Returns the most specific type we can determine for the expression. *)
let rec get_actual_tc_type e =
	match e.eexpr with
	(* TCast explicitly changes the type - return the cast's target type *)
	| TCast (_, _) -> Some (tc_type_of e.etype)
	| TMeta (_, inner) -> get_actual_tc_type inner
	| TParenthesis inner -> get_actual_tc_type inner
	| TBlock exprs when exprs <> [] ->
		(* Block expressions evaluate to the last expression *)
		get_actual_tc_type (List.hd (List.rev exprs))
	(* Local variable - use the variable's type directly *)
	| TLocal v -> Some (tc_type_of v.v_type)
	(* Dynamic/anonymous field access returns FibDynamic *)
	| TField (_, FAnon _) | TField (_, FDynamic _) -> Some TCFibDynamic
	(* Static field: use actual field type *)
	| TField (_, FStatic (_, cf)) -> Some (tc_type_of cf.cf_type)
	(* Instance field: use actual field type *)
	| TField (_, FInstance (_, _, cf)) -> Some (tc_type_of cf.cf_type)
	(* Closure: use actual field type *)
	| TField (_, FClosure (_, cf)) -> Some (tc_type_of cf.cf_type)
	(* Array literals produce specialized type based on expression type *)
	| TArrayDecl _ -> Some (tc_type_of e.etype)
	(* Array element access returns the element type for typed arrays *)
	| TArray (e1, _) -> Some (FiberusTypeUtils.get_array_elem_type e1.etype)
	(* Dynamic method calls - toString returns FibString *)
	| TCall ({ eexpr = TField (_, FAnon cf) }, _) when cf.cf_name = "toString" -> Some TCFibString
	| TCall ({ eexpr = TField (_, FDynamic "toString") }, _) -> Some TCFibString
	(* Static method calls - use the method's return type *)
	| TCall ({ eexpr = TField (_, FStatic (_, cf)) }, _) ->
		(match follow cf.cf_type with
		| TFun (_, ret) -> Some (tc_type_of ret)
		| _ -> None)
	(* Instance method calls - use the method's return type *)
	(* Special case: specialized array methods return primitive types, not Null<T> *)
	| TCall ({ eexpr = TField (obj, FInstance (c, _, cf)) }, _) ->
		(* Check if this is a specialized array method that returns a primitive *)
		let obj_tc = tc_type_of obj.etype in
		let is_int_array = obj_tc = TCFibArray TCArrInt in
		let is_float_array = obj_tc = TCFibArray TCArrFloat in
		let is_bool_array = obj_tc = TCFibArray TCArrBool in
		let is_string = is_string_type obj.etype in
		let map_kind = FiberusBuiltins.map_kind_of_type obj.etype in
		(* Methods that return the element type (not Null<T>) for specialized arrays *)
		(match cf.cf_name with
		(* String methods that return int in C (not FibDynamic) *)
		| "charCodeAt" when is_string -> Some TCInt32
		| "indexOf" | "lastIndexOf" when is_string -> Some TCInt32
		| "pop" | "shift" | "__get" | "__unsafe_get" when is_int_array -> Some TCInt32
		| "pop" | "shift" | "__get" | "__unsafe_get" when is_float_array -> Some TCFloat64
		| "pop" | "shift" | "__get" | "__unsafe_get" when is_bool_array -> Some TCBool
		(* Map get methods return type-specialized values *)
		| "get" when map_kind <> None && c.cl_path <> (["haxe"; "ds"], "ObjectMap") ->
			(* Get the value type parameter from the map type *)
			(match follow obj.etype with
			| TInst (_, [t]) -> Some (tc_type_of t)
			| _ -> Some TCFibDynamic)
		(* ObjectMap.get returns type-specialized values based on second type parameter *)
		| "get" when c.cl_path = (["haxe"; "ds"], "ObjectMap") ->
			(match follow obj.etype with
			| TInst (_, [_; t]) -> Some (tc_type_of t)
			| _ -> Some TCFibDynamic)
		| _ ->
			(match follow cf.cf_type with
			| TFun (_, ret) -> Some (tc_type_of ret)
			| _ -> None))
	(* __fiberus__ calls return the expression's declared type (from inline function) *)
	| TCall ({ eexpr = TIdent "__fiberus__" }, _) ->
		Some (tc_type_of e.etype)
	(* Any function call - try to get return type from callee's type *)
	| TCall (callee, _) ->
		(match follow callee.etype with
		| TFun (_, ret) -> Some (tc_type_of ret)
		| _ -> None)
	| _ -> None

(* Get tc_type from expression, falling back to haxe type *)
let get_expr_tc_type e =
	match get_actual_tc_type e with
	| Some tc -> tc
	| None -> tc_type_of e.etype

(* Check if tc_type is a GC-managed pointer that needs write barrier *)
let needs_write_barrier_tc = function
	| TCFibString | TCFibArray _ | TCFibClass _ | TCFibClosure
	| TCFibObject | TCFibIntMap | TCFibStringMap
	| TCFibInt64Map | TCFibObjectMap | TCFibBytesData -> true
	| TCPointer _ -> true
	| _ -> false

(* is_enum_type now imported from FiberusTypeUtils *)

(* Check if expression is a __fiberus__ call (produces raw C code with correct type) *)
let rec is_fiberus_call expr =
	match expr with
	| Some { eexpr = TCall ({ eexpr = TIdent "__fiberus__" }, _) } -> true
	| Some { eexpr = TCast (inner, _) } -> is_fiberus_call (Some inner)
	| Some { eexpr = TParenthesis inner } -> is_fiberus_call (Some inner)
	| Some { eexpr = TMeta (_, inner) } -> is_fiberus_call (Some inner)
	| _ -> false

(* Generate coercion wrapper if needed *)
(* Generate type coercion using tc_type pattern matching *)
let gen_coerce_with_expr ctx from_type to_type expr gen_inner =
	(* Convert to tc_type for pattern matching *)
	let from_tc = tc_type_of from_type in
	let to_tc = tc_type_of to_type in
	(* Check for null expression *)
	let is_null_expr = match expr with
		| Some { eexpr = TConst TNull } -> true
		| _ -> false
	in
	(* Check for __fiberus__ calls - these produce raw C code with correct type *)
	let is_fiberus = is_fiberus_call expr in
	(* Handle special cases first *)
	if is_fiberus then
		(* __fiberus__ calls produce raw C with correct type, no coercion needed *)
		gen_inner ()
	else if is_null_expr then
		(* Handle null coercions *)
		match to_tc with
		| TCFibEnum name -> print ctx "((%s){ .index = 0 })" name
		| TCFibDynamic -> spr ctx "fib_dynamic_null()"
		| TCInt32 -> spr ctx "0"
		| TCFloat64 -> spr ctx "0.0"
		| TCBool -> spr ctx "false"
		| _ -> gen_inner ()
	else begin
		(* Determine actual C type based on expression kind *)
		let from_tc = match expr with
			| Some e -> (match get_actual_tc_type e with
				| Some t -> t
				| None -> from_tc)
			| None -> from_tc
		in
		(* Generate coercion based on type pair *)
		match from_tc, to_tc with
		| t1, t2 when t1 = t2 -> gen_inner ()
		(* FibDynamic -> other types (unboxing) *)
		| TCFibDynamic, TCFibString ->
			spr ctx "fib_dynamic_to_string("; gen_inner (); spr ctx ")"
		| TCFibDynamic, TCFibArray TCArrGeneric ->
			spr ctx "fib_dynamic_to_array("; gen_inner (); spr ctx ")"
		| TCFibDynamic, TCFibArray kind ->
			(* Specialized arrays need cast from FibArray* *)
			print ctx "((%s)fib_dynamic_to_array(" (tc_type_to_string (TCFibArray kind)); gen_inner (); spr ctx "))"
		| TCFibDynamic, TCFibClass name ->
			print ctx "((%s*)fib_dynamic_to_object(" name; gen_inner (); spr ctx "))"
		| TCFibDynamic, TCFloat64 ->
			spr ctx "fib_dynamic_to_float("; gen_inner (); spr ctx ")"
		| TCFibDynamic, TCInt32 ->
			spr ctx "fib_dynamic_to_int("; gen_inner (); spr ctx ")"
		| TCFibDynamic, TCBool ->
			spr ctx "fib_dynamic_to_bool("; gen_inner (); spr ctx ")"
		(* Other types -> FibDynamic (boxing) *)
		| TCFibString, TCFibDynamic ->
			spr ctx "fib_string_to_dynamic("; gen_inner (); spr ctx ")"
		| TCFibArray TCArrGeneric, TCFibDynamic ->
			spr ctx "fib_dynamic_array("; gen_inner (); spr ctx ")"
		| TCFibArray _, TCFibDynamic ->
			(* Specialized arrays need cast to FibArray* first *)
			spr ctx "fib_dynamic_array((FibArray*)"; gen_inner (); spr ctx ")"
		| TCInt32, TCFibDynamic ->
			spr ctx "fib_dynamic_int("; gen_inner (); spr ctx ")"
		| TCFloat64, TCFibDynamic ->
			spr ctx "fib_dynamic_float("; gen_inner (); spr ctx ")"
		| TCBool, TCFibDynamic ->
			spr ctx "fib_dynamic_bool("; gen_inner (); spr ctx ")"
		| TCFibClass _, TCFibDynamic ->
			spr ctx "fib_dynamic_object((FibObject*)"; gen_inner (); spr ctx ")"
		(* Cast between class pointer types *)
		| TCFibClass _, TCFibClass name ->
			print ctx "((%s*)" name; gen_inner (); spr ctx ")"
		(* Default: no coercion *)
		| _ -> gen_inner ()
	end

let gen_coerce ctx from_type to_type gen_inner =
	gen_coerce_with_expr ctx from_type to_type None gen_inner

(* get_param_types now imported from FiberusTypeUtils *)

(* collect_free_vars now imported as find_free_vars from FiberusClosure *)

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
	match tc_type_of msg.etype with
	| TCFibString ->
		spr ctx "fib_string_to_dynamic("; gen_value ctx msg; spr ctx ")"
	| TCInt32 ->
		spr ctx "fib_dynamic_int("; gen_value ctx msg; spr ctx ")"
	| TCFloat64 ->
		spr ctx "fib_dynamic_float("; gen_value ctx msg; spr ctx ")"
	| TCBool ->
		spr ctx "fib_dynamic_bool("; gen_value ctx msg; spr ctx ")"
	| TCFibDynamic ->
		gen_value ctx msg
	| _ ->
		(* Object or unknown type - convert to FibDynamic *)
		spr ctx "fib_dynamic_object((FibObject*)"; gen_value ctx msg; spr ctx ")"

(* Helper for Fiber.spawn closure capture - shared by spawn/spawnOn/spawnAny *)
and gen_fiber_spawn_closure ctx free_vars _closure_name =
	List.iteri (fun i v ->
		print ctx "_fc->captures[%d] = " i;
		let box_func = FiberusClosure.box_to_dynamic_func v.v_type in
		if box_func = "" then
			(* Already dynamic or needs raw object boxing *)
			print ctx "(FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=%s}; " (ident v.v_name)
		else
			print ctx "%s(%s); " box_func (ident v.v_name)
	) free_vars

(* Extract closure info for Fiber.spawn patterns *)
and extract_closure_for_spawn ctx arg =
	match arg.eexpr with
	| TFunction f ->
		let free_vars = find_free_vars f in
		let closure_name = Printf.sprintf "_closure_%d" ctx.closure_counter in
		let impl_name = closure_name ^ "_impl" in
		ctx.closure_counter <- ctx.closure_counter + 1;
		if not ctx.in_closure_impl then begin
			(* Create a C-AST closure record for the implementations to be generated later *)
			let conv_ctx = make_conv_ctx ctx in
			conv_ctx.FiberusConvert.in_fiber_spawn <- true;
			(* Convert function body to C-AST *)
			let body_ctx = { conv_ctx with FiberusConvert.current_ret_type = Some (tc_type_of f.tf_type) } in
			let body_stmts = FiberusConvert.convert_stmt body_ctx f.tf_expr in
			let ret_type = tc_type_of f.tf_type in
			let args = List.map (fun (v, _) ->
				{ FiberusAst.fa_name = ident v.v_name; FiberusAst.fa_type = tc_type_of v.v_type }
			) f.tf_args in
			let captures = List.mapi (fun i v ->
				{ FiberusAst.cap_var = ident v.v_name; FiberusAst.cap_type = tc_type_of v.v_type; FiberusAst.cap_index = i }
			) free_vars in
			let closure_def = {
				FiberusAst.cl_id = ctx.closure_counter - 1;
				FiberusAst.cl_name = closure_name;
				FiberusAst.cl_impl_name = impl_name;
				FiberusAst.cl_args = args;
				FiberusAst.cl_ret = ret_type;
				FiberusAst.cl_captures = captures;
				FiberusAst.cl_body = body_stmts;
			} in
			ctx.closures <- closure_def :: ctx.closures
		end;
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
	(* Fiber.spawn with closure - matches both ([], "Fiber") and (["fiberus"], "Fiber") *)
	| TField (_, FStatic ({ cl_path = (([] | ["fiberus"]), "Fiber") }, { cf_name = "spawn" })), [arg] ->
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
	| TField (_, FStatic ({ cl_path = (([] | ["fiberus"]), "Fiber") }, { cf_name = "spawnOn" })), [thread_id; arg] ->
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
	| TField (_, FStatic ({ cl_path = (([] | ["fiberus"]), "Fiber") }, { cf_name = "spawnAny" })), [arg] ->
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
	(* Fiber.spawnWithStack with closure - custom stack size *)
	| TField (_, FStatic ({ cl_path = (([] | ["fiberus"]), "Fiber") }, { cf_name = "spawnWithStack" })), [stack_size; arg] ->
		(match extract_closure_for_spawn ctx arg with
		| Some (free_vars, closure_name) ->
			let impl_name = closure_name ^ "_impl" in
			spr ctx "({ size_t _sz = (size_t)";
			gen_value ctx stack_size;
			spr ctx "; gc_mature_alloc_begin(); FibClosure* _fc = fib_closure_create_for_fiber((void*)";
			spr ctx impl_name;
			spr ctx ", (void*)";
			spr ctx closure_name;
			print ctx ", %d, 0); gc_push_temp_root((void**)&_fc); " (List.length free_vars);
			gen_fiber_spawn_closure ctx free_vars closure_name;
			spr ctx "Fiber* _fib = scheduler_spawn_sized(_sz, _fib_spawn_closure_trampoline, (void*)_fc); ";
			spr ctx "gc_mature_alloc_end(); gc_pop_temp_roots(1); _fib; })"
		| None ->
			spr ctx "Fiber_spawnWithStack(";
			gen_value ctx stack_size;
			spr ctx ", ";
			gen_value ctx arg;
			spr ctx ")");
		true
	(* Static method call: Class.method(args) -> Class_method(args) 
	   Needed when called with TFunction arguments *)
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
 * Handles Array<T> instance method calls with TFunction arguments.
 * NOTE: Simple array methods (push, pop, etc.) go through C-AST pipeline.
 * This is only reached when an argument is a TFunction (e.g., filter, map, sort callbacks).
 *)
and gen_array_call ctx arr cf args =
	(* Helper to generate array with coercion if needed *)
	let arr_tc = get_expr_tc_type arr in
	let gen_array_value () =
		if arr_tc = TCFibDynamic then begin
			spr ctx "fib_dynamic_to_array(";
			gen_value ctx arr;
			spr ctx ")"
		end else gen_value ctx arr
	in
	(* Fallback to generic method call for filter, map, sort, etc. *)
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
 * NOTE: String has no methods that take function arguments, so this is only 
 * reached as a fallback. Standard string methods go through C-AST pipeline.
 *)
and gen_string_call ctx str cf args =
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
 * NOTE: Map has no methods that take function arguments, so this is only 
 * reached as a fallback. Standard map methods go through C-AST pipeline.
 *)
and gen_map_call ctx kind map_expr cf args =
	let map_name = match kind with
		| MapInt -> "IntMap" | MapString -> "StringMap"
		| MapInt64 -> "Int64Map" | MapObject -> "ObjectMap"
	in
	(* Fallback to generic method call *)
	print ctx "%s_%s(" map_name (ident cf.cf_name);
	gen_value ctx map_expr;
	if args <> [] then spr ctx ", ";
	gen_call_args ctx args (get_param_types cf.cf_type) gen_value;
	spr ctx ")";
	true

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
	let is_interface_call = FiberusVtable.is_interface c in
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
					FiberusVtable.needs_virtual_dispatch c cf &&
					(match FiberusVtable.get_vtable_slot vctx c cf with
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
					FiberusVtable.get_interface_slot vctx c cf
				else
					(match FiberusVtable.get_vtable_slot vctx c cf with
					| Some info -> Some info.slot_index
					| None -> None)
			| None -> None
		in
		(* Get method signature for type cast *)
		let (arg_types, ret_type) = FiberusVtable.get_method_types cf in
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
	(* Map method calls (IntMap, StringMap, Int64Map, ObjectMap) *)
	| TField (map_expr, FInstance (_, _, cf)), _ when map_kind_of_type map_expr.etype <> None ->
		let kind = match map_kind_of_type map_expr.etype with Some k -> k | None -> MapInt in
		ignore (gen_map_call ctx kind map_expr cf args)
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
		(* Use C-AST pipeline for constants *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TLocal v ->
		(* Use C-AST pipeline for local variables *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TArray _ ->
		(* Use C-AST pipeline for array access *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TBinop (OpAssign, { eexpr = TLocal v }, e2) when Hashtbl.mem ctx.stack_alloc_vars v.v_id ->
		(* Stack-allocated variable reassignment requires special handling *)
		(match e2.eexpr with
		| TNew (c, _, args) ->
			(* Reinitialize the stack struct in place *)
			let class_name = flat_path c.cl_path in
			spr ctx "(";
			print ctx "_stack_%s = (%s){ ._obj.clazz = &%s_class" (ident v.v_name) class_name class_name;
			(match c.cl_constructor with
			| Some cf ->
				(match cf.cf_expr with
				| Some { eexpr = TFunction f } ->
					let filtered_args = filter_void_args f.tf_args in
					let param_field_map = extract_param_field_mapping f in
					List.iter2 (fun (param_v, _) arg ->
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
			gen_value ctx { e with eexpr = TLocal v };
			gen_binop ctx OpAssign;
			gen_value ctx e2;
			spr ctx ")")
	| TBinop _ ->
		(* Use C-AST pipeline for all other binary operations *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TField (obj, fa) ->
		(* FClosure needs gen_field_access for thunk generation, others use C-AST *)
		(match fa with
		| FClosure _ -> gen_field_access ctx obj fa
		| _ ->
			let conv_ctx = make_conv_ctx ctx in
			let cexpr = FiberusConvert.convert_expr conv_ctx e in
			emit_cexpr ctx cexpr)
	| TTypeExpr _ ->
		(* Use C-AST pipeline for type expressions *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TParenthesis e ->
		(* Use C-AST pipeline - just convert inner, parentheses handled by binop emission *)
		gen_value ctx e
	| TObjectDecl _ ->
		(* Use C-AST pipeline for anonymous objects *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TArrayDecl _ ->
		(* Use C-AST pipeline for array literals *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TCall (callee, args) ->
		(* Check for builtins that require gen_call (closure extraction, trace, etc.)
		 * Note: Fiber.spawn/spawnOn/spawnAny/spawnWithStack now use C-AST pipeline *)
		let needs_gen_call = match FiberusBuiltins.get_intrinsic callee with
			| Some FiberusBuiltins.ITrace -> true
			| Some FiberusBuiltins.IFiberus -> true
			| _ -> false
		in
		(* Also check if any argument is a TFunction - needs gen_call for closure handling.
		 * Exception: Fiber.spawn variants handle their own closures in C-AST pipeline. *)
		let is_fiber_spawn = match FiberusBuiltins.get_intrinsic callee with
			| Some (FiberusBuiltins.IFiberSpawn | FiberusBuiltins.IFiberSpawnOn 
			       | FiberusBuiltins.IFiberSpawnAny | FiberusBuiltins.IFiberSpawnWithStack) -> true
			| _ -> false
		in
		let has_func_arg = not is_fiber_spawn && 
			List.exists (fun arg -> match arg.eexpr with TFunction _ -> true | _ -> false) args in
		if needs_gen_call || has_func_arg then
			gen_call ctx callee args
		else begin
			(* Use C-AST pipeline for all other calls including Fiber.spawn variants *)
			let conv_ctx = make_conv_ctx ctx in
			let cexpr = FiberusConvert.convert_expr conv_ctx e in
			(* Sync closures for Fiber.spawn cases *)
			if is_fiber_spawn then begin
				let new_closures = sync_closures_from_conv ctx conv_ctx in
				ctx.closures <- new_closures @ ctx.closures
			end;
			emit_cexpr ctx cexpr
		end
	| TNew _ ->
		(* Use C-AST pipeline for object instantiation *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TUnop _ ->
		(* Use C-AST pipeline for unary operations *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TFunction _ ->
		(* Use C-AST pipeline for closure creation *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		(* Sync closures back to main context *)
		let new_closures = sync_closures_from_conv ctx conv_ctx in
		ctx.closures <- new_closures @ ctx.closures;
		emit_cexpr ctx cexpr
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
		(* Block used as value - use C-AST pipeline with GC tracking *)
		let conv_ctx = make_conv_ctx ctx in
		let result_tc = tc_type_of e.etype in
		let cexpr = FiberusConvert.convert_block_expr conv_ctx el result_tc e.epos in
		(* Sync GC count back from conversion context *)
		ctx.gc_local_count <- conv_ctx.gc_local_count;
		emit_cexpr ctx cexpr
	| TIf _ ->
		(* Use C-AST pipeline for ternary expressions *)
		ctx.in_value <- true;
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TWhile _ | TSwitch _ | TTry _ ->
		spr ctx "/* complex expr */"
	| TReturn eo ->
		(* Use C-AST pipeline for return statements *)
		let conv_ctx = make_conv_ctx ctx in
		let ret_expr = match eo with
			| None -> None
			| Some inner ->
				let inner_expr = FiberusConvert.convert_expr conv_ctx inner in
				(* Coerce to return type if known *)
				match conv_ctx.current_ret_type with
				| Some ret_tc -> Some (FiberusConvert.coerce_to_type inner_expr ret_tc)
				| None -> Some inner_expr
		in
		emit_cstmt_no_semi ctx (TCSReturn ret_expr)
	| TBreak -> emit_cstmt_inline ctx TCSBreak
	| TContinue -> emit_cstmt_inline ctx TCSContinue
	| TThrow exc ->
		(* Use C-AST pipeline for throw statements *)
		let conv_ctx = make_conv_ctx ctx in
		let exc_expr = FiberusConvert.convert_expr conv_ctx exc in
		(* Box to FibDynamic if not already *)
		let boxed_expr = 
			if exc_expr.ctype = TCFibDynamic then exc_expr
			else mk_expr (TCEBox (exc_expr, box_kind_of_type exc_expr.ctype)) TCFibDynamic
		in
		emit_cstmt_no_semi ctx (TCSThrow boxed_expr)
	| TCast _ ->
		(* Use C-AST pipeline for type casts *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TMeta (_, inner) ->
		(* Meta annotations - just unwrap to inner expression *)
		gen_value ctx inner
	| TEnumParameter _ ->
		(* Use C-AST pipeline for enum parameter access *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TEnumIndex _ ->
		(* Use C-AST pipeline for enum index *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr
	| TIdent _ ->
		(* Use C-AST pipeline for identifiers *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr ctx cexpr

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
	| TNew _ | TUnop _ | TCast _ | TMeta _
	| TEnumParameter _ | TEnumIndex _ | TIdent _ ->
		(* For value expressions used as statements, we need to:
		 * 1. Emit any pending_stmts from the expression
		 * 2. Emit the expression
		 * 3. Pop any gc_roots the expression leaves on the stack
		 * Convert to C-AST to check gc_roots and pending_stmts *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		emit_cexpr_with_pending ctx cexpr;
		if cexpr.gc_roots > 0 then
			print ctx "; gc_pop_temp_roots_ctx(FIB_CTX, %d)" cexpr.gc_roots
	| TCall _ ->
		(* Convert call to C-AST to properly handle pending_stmts from complex arguments.
		 * This handles trace(), Fiber.spawn, and all other calls that may have
		 * string concatenation or other GC-allocating expressions as arguments. *)
		let conv_ctx = make_conv_ctx ctx in
		let cexpr = FiberusConvert.convert_expr conv_ctx e in
		(* Sync closures back if any were created *)
		let new_closures = sync_closures_from_conv ctx conv_ctx in
		if new_closures <> [] then ctx.closures <- new_closures @ ctx.closures;
		(* Emit pending statements first, then the expression *)
		emit_cexpr_with_pending ctx cexpr;
		if cexpr.gc_roots > 0 then
			print ctx "; gc_pop_temp_roots_ctx(FIB_CTX, %d)" cexpr.gc_roots
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
			(* Track gc_roots from initializer for proper cleanup order *)
			let init_gc_roots = ref 0 in
			(match eo with
			| None ->
				(* No initializer - just declare the variable *)
				print ctx "%s %s" type_str (ident v.v_name)
			| Some e ->
				(* Convert to C-AST first to get pending_stmts and gc_roots *)
				let conv_ctx = make_conv_ctx ctx in
				let cexpr = FiberusConvert.convert_expr conv_ctx e in
				(* Sync closures back to main context - critical for TFunction initializers! *)
				let new_closures = sync_closures_from_conv ctx conv_ctx in
				if new_closures <> [] then ctx.closures <- new_closures @ ctx.closures;
				init_gc_roots := cexpr.gc_roots;
				(* IMPORTANT: Emit pending_stmts BEFORE the variable declaration.
				 * These contain temp variable declarations needed by the initializer. *)
				if cexpr.pending_stmts <> [] then begin
					let w = FiberusSourceWriter.create () in
					List.iter (FiberusSourceWriter.write_stmt w) cexpr.pending_stmts;
					spr ctx (FiberusSourceWriter.contents w)
				end;
				(* Now emit the variable declaration with initializer *)
				print ctx "%s %s = " type_str (ident v.v_name);
				(* Emit with proper coercion *)
				let from_tc = cexpr.ctype in
				let to_tc = tc_type_of v.v_type in
				if from_tc = to_tc then
					emit_cexpr ctx cexpr
				else
					(* Need coercion - emit via coerce function *)
					gen_coerce_with_expr ctx e.etype v.v_type (Some e) (fun () -> emit_cexpr ctx cexpr));
			(* For GC pointer types:
			 * 1. FIRST push the variable as a root - this protects the value
			 * 2. THEN pop expression-level roots from the initializer
			 * This order is critical: gc_pop may trigger GC, and at that point
			 * the value must already be rooted. If we pop first, the value in
			 * the variable could be relocated without updating the variable. *)
			if is_gc_ptr then begin
				spr ctx "; gc_push_temp_root_ctx(FIB_CTX, (void**)&";
				spr ctx (ident v.v_name);
				spr ctx ")";
				ctx.gc_local_count <- ctx.gc_local_count + 1;
				if !init_gc_roots > 0 then begin
					print ctx "; gc_pop_temp_roots_ctx(FIB_CTX, %d)" !init_gc_roots
				end
			end else if !init_gc_roots > 0 then begin
				(* Non-GC pointer type but init had gc_roots - still need to pop *)
				print ctx "; gc_pop_temp_roots_ctx(FIB_CTX, %d)" !init_gc_roots
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
		(* Convert condition to C-AST to handle pending_stmts from complex expressions *)
		let conv_ctx = make_conv_ctx ctx in
		let cond_expr = FiberusConvert.convert_expr conv_ctx cond in
		(* Emit pending_stmts before the if - these declare temp variables used in condition *)
		if cond_expr.pending_stmts <> [] then begin
			let w = FiberusSourceWriter.create () in
			List.iter (FiberusSourceWriter.write_stmt w) cond_expr.pending_stmts;
			spr ctx (FiberusSourceWriter.contents w)
		end;
		spr ctx "if (";
		emit_cexpr ctx cond_expr;
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
		(* Convert condition to C-AST to handle pending_stmts from complex expressions *)
		let conv_ctx = make_conv_ctx ctx in
		let cond_expr = FiberusConvert.convert_expr conv_ctx cond in
		(* Emit pending_stmts before the while - these declare temp variables used in condition *)
		if cond_expr.pending_stmts <> [] then begin
			let w = FiberusSourceWriter.create () in
			List.iter (FiberusSourceWriter.write_stmt w) cond_expr.pending_stmts;
			spr ctx (FiberusSourceWriter.contents w)
		end;
		spr ctx "while (";
		emit_cexpr ctx cond_expr;
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
		(* FIB_CTX is now FiberGCContext*, so use tempRootCount (not mTempRootCount) *)
		print ctx "size_t %s = FIB_CTX ? FIB_CTX->tempRootCount : 0;" gc_save;
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
		(* FIB_CTX is now FiberGCContext*, so use tempRootCount (not mTempRootCount) *)
		print ctx "if (FIB_CTX && FIB_CTX->tempRootCount > %s) FIB_CTX->tempRootCount = %s;" gc_save gc_save;
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
		(* Handle GC roots cleanup before return.
		 * We need to pop:
		 * 1. Expression-level roots from the return expression (gc_roots)
		 * 2. Function-level local variable roots (ctx.gc_local_count) *)
		(match eo with
		| None ->
			(* No return value, just pop function locals and return *)
			if ctx.gc_local_count > 0 then
				print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d); return" ctx.gc_local_count
			else
				spr ctx "return"
		| Some e ->
			(* Convert return expression to check for gc_roots and pending_stmts *)
			let conv_ctx = make_conv_ctx ctx in
			let cexpr_raw = FiberusConvert.convert_expr conv_ctx e in
			(* Coerce to return type if known *)
			let cexpr = match conv_ctx.FiberusConvert.current_ret_type with
				| Some ret_tc -> FiberusConvert.coerce_to_type cexpr_raw ret_tc
				| None -> cexpr_raw
			in
			let expr_gc_roots = cexpr.gc_roots in
			let has_pending = cexpr.pending_stmts <> [] in
			let total_to_pop = ctx.gc_local_count + expr_gc_roots in
			let ret_type = match ctx.current_ret_type with
				| Some t -> s_type ctx t
				| None -> s_type ctx e.etype
			in
			(* For simple values with no gc_roots, no locals, and no pending_stmts, return directly *)
			let is_simple = match e.eexpr with
				| TConst _ | TLocal _ -> true
				| _ -> false
			in
			if is_simple && total_to_pop = 0 && not has_pending then begin
				spr ctx "return ";
				emit_cexpr ctx cexpr
			end else if is_simple && expr_gc_roots = 0 && not has_pending then begin
				(* Simple value, only function locals to pop *)
				print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d); return " ctx.gc_local_count;
				emit_cexpr ctx cexpr
			end else begin
				(* Complex: emit pending_stmts, evaluate into temp, pop all roots, return temp *)
				spr ctx "{ ";
				(* Emit pending statements FIRST - these declare temp variables needed by the expression *)
				if has_pending then begin
					let w = FiberusSourceWriter.create () in
					List.iter (FiberusSourceWriter.write_stmt w) cexpr.pending_stmts;
					spr ctx (FiberusSourceWriter.contents w)
				end;
				print ctx "%s __ret = " ret_type;
				emit_cexpr ctx cexpr;
				if total_to_pop > 0 then
					print ctx "; gc_pop_temp_roots_ctx(FIB_CTX, %d)" total_to_pop;
				spr ctx "; return __ret; }"
			end)
		(* NOTE: We do NOT reset gc_local_count here because:
		 * 1. The TIf handler properly saves/restores gc_local_count for each branch
		 * 2. Setting it to 0 would corrupt tracking for later code paths *)
	| TBreak -> emit_cstmt_inline ctx TCSBreak
	| TContinue -> emit_cstmt_inline ctx TCSContinue
	| TThrow _ ->
		(* Use C-AST pipeline for throw - handles boxing to FibDynamic *)
		let conv_ctx = make_conv_ctx ctx in
		let stmts = FiberusConvert.convert_stmt conv_ctx e in
		List.iter (fun stmt -> emit_cstmt_inline ctx stmt) stmts

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
	(* Protect GC pointer parameters as temp roots BEFORE any safe point.
	   This is CRITICAL: if GC runs at the safe point below, parameters
	   must already be protected so they get updated during evacuation.
	   The caller protects their local variables, but parameters are copies. *)
	let gc_param_count = List.fold_left (fun count (v, _) ->
		if needs_gc_root ctx v.v_type then begin
			print ctx "gc_push_temp_root_ctx(FIB_CTX, (void**)&%s);" (ident v.v_name);
			newline ctx;
			count + 1
		end else
			count
	) 0 filtered_args in
	(* Also protect 'this' for non-static methods *)
	let gc_param_count = if not is_static then begin
		spr ctx "gc_push_temp_root_ctx(FIB_CTX, (void**)&this);";
		newline ctx;
		gc_param_count + 1
	end else gc_param_count in
	(* NOW inject GC safe point - parameters are protected *)
	spr ctx "GC_SAFE_POINT();";
	newline ctx;
	(* Debug: save base root count for verification at return *)
	(* Note: _fib_gc_ctx is FiberGCContext*, uses tempRootCount (not mTempRootCount) *)
	spr ctx "#ifdef FIBERUS_DEBUG";
	newline ctx;
	spr ctx "size_t _gc_base_count = _fib_gc_ctx ? _fib_gc_ctx->tempRootCount : 0;";
	newline ctx;
	spr ctx "#endif";
	newline ctx;
	(* Reset GC local count and context flag for this function *)
	let old_gc_count = ctx.gc_local_count in
	let old_has_gc_ctx = ctx.has_gc_ctx in
	let old_stack_alloc_vars = ctx.stack_alloc_vars in
	(* Start with parameter count - these were pushed above *)
	ctx.gc_local_count <- gc_param_count;
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
	| Some e when is_compile_time_constant e ->
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
			if is_simple_constructor f then
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
				(* Run escape analysis for constructor body *)
				ctx.stack_alloc_vars <- analyze_escapes f;
				(* Only emit FIB_GC_CTX if constructor body needs it *)
				if init_needs_gc_ctx then begin
					spr ctx "FIB_GC_CTX;";
					newline ctx;
					ctx.has_gc_ctx <- true;
					(* Protect GC pointer parameters as temp roots *)
					let gc_param_count = List.fold_left (fun count (v, _) ->
						if needs_gc_root ctx v.v_type then begin
							print ctx "gc_push_temp_root_ctx(FIB_CTX, (void**)&%s);" (ident v.v_name);
							newline ctx;
							count + 1
						end else
							count
					) 0 filtered_args in
					(* Also protect 'this' *)
					spr ctx "gc_push_temp_root_ctx(FIB_CTX, (void**)&this);";
					newline ctx;
					ctx.gc_local_count <- gc_param_count + 1
				end else begin
					ctx.has_gc_ctx <- false;
					ctx.gc_local_count <- 0
				end;
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
				(* CRITICAL: Protect GC pointer parameters BEFORE allocation.
				   gc_alloc_object_with_class can trigger GC, which would evacuate
				   any nursery objects. Parameters are copies on the stack, so if
				   they're not protected, they become stale after evacuation. *)
				let gc_param_args = List.filter (fun (v, _) -> needs_gc_root ctx v.v_type) filtered_args in
				let has_gc_params = gc_param_args <> [] in
				if has_gc_params then begin
					spr ctx "FIB_GC_CTX;";
					newline ctx;
					List.iter (fun (v, _) ->
						print ctx "gc_push_temp_root_ctx(FIB_CTX, (void**)&%s);" (ident v.v_name);
						newline ctx
					) gc_param_args
				end;
				(* Use gc_alloc_object_with_class - sets clazz atomically before allocStart *)
				print ctx "%s* this = gc_alloc_object_with_class(sizeof(%s), &%s_class);" class_name class_name class_name;
				newline ctx;
				(* Call _init with args - use filtered args for consistency *)
				let arg_names = List.map (fun (v, _) -> ident v.v_name) filtered_args in
				print ctx "%s_init(this%s);" class_name
					(if arg_names = [] then "" else ", " ^ String.concat ", " arg_names);
				newline ctx;
				(* Pop GC roots before return *)
				if has_gc_params then begin
					print ctx "gc_pop_temp_roots_ctx(FIB_CTX, %d);" (List.length gc_param_args);
					newline ctx
				end;
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

		(* Reset global counters for this class - ensures unique names per file *)
		FiberusConvert.reset_counters ();

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
				let type_tc = tc_type_of cf.cf_type in
				needs_gc_marking_tc type_tc
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
			| Some vctx -> FiberusVtable.get_vtable_methods vctx c
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
						if List.exists (fun cf2 -> cf2.cf_name = method_name && FiberusVtable.is_instance_method cf2) c.cl_ordered_fields then
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

		(* Generate closures collected during code generation using C-AST pipeline *)
		if ctx.closures <> [] then begin
			Buffer.clear ctx.buf;
			
			(* Use FiberusSourceWriter to generate forward declarations *)
			let w = FiberusSourceWriter.create () in
			FiberusSourceWriter.write_closures_forward_decls w (List.rev ctx.closures);
			spr ctx (FiberusSourceWriter.contents w);
			
			(* Add main content *)
			spr ctx main_content;
			
			(* Use FiberusSourceWriter to generate implementations *)
			let w2 = FiberusSourceWriter.create () in
			FiberusSourceWriter.write_closures w2 (List.rev ctx.closures) ~debug_level:ctx.debug_level;
			spr ctx (FiberusSourceWriter.contents w2);
			
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
					let arg_tc = tc_type_of t in
					print ctx "_e.params[%d] = " !i;
					gen_box_to_fib_dynamic_tc ctx arg_tc (fun () -> spr ctx (ident n));
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
	spr ctx "#include \"date.h\"\n";
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
	spr ctx "/* NOTE: For object allocation, prefer gc_alloc_object_with_class() to avoid race conditions */\n";
	spr ctx "/* Uses ThreadBlockCache via tls_thread_cache (not tls_current_alloc) */\n";
	spr ctx "static inline void* fib_alloc(size_t size) {\n";
	spr ctx "\treturn fibrix_alloc(size, true);  /* isContainer=true for objects with refs */\n";
	spr ctx "}\n\n";
	spr ctx "/* Atomic allocation - no references to track */\n";
	spr ctx "static inline void* fib_alloc_atomic(size_t size) {\n";
	spr ctx "\treturn fibrix_alloc(size, false);  /* isContainer=false for raw data */\n";
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
	spr ctx "/* Anonymous object creation helpers (standard C, no GCC extensions) */\n";
	spr ctx "static inline FibAnonField* _fib_anon_field(const char* name, FibDynamic value, FibAnonField* next) {\n";
	spr ctx "\tFibAnonField* f = (FibAnonField*)malloc(sizeof(FibAnonField));\n";
	spr ctx "\tf->name = name; f->value = value; f->next = next;\n";
	spr ctx "\treturn f;\n";
	spr ctx "}\n";
	spr ctx "static inline FibDynamic _fib_anon_wrap(FibAnonField* fields) {\n";
	spr ctx "\treturn (FibDynamic){ .type = FIB_TYPE_OBJECT, .data.ptrVal = fields };\n";
	spr ctx "}\n";
	spr ctx "/* FIB_ANON_NEW - create anonymous object with N fields (standard C) */\n";
	spr ctx "#define FIB_ANON_NEW_0() _fib_anon_wrap(NULL)\n";
	spr ctx "#define FIB_ANON_NEW_1(n1, v1) \\\n";
	spr ctx "\t_fib_anon_wrap(_fib_anon_field(n1, v1, NULL))\n";
	spr ctx "#define FIB_ANON_NEW_2(n1, v1, n2, v2) \\\n";
	spr ctx "\t_fib_anon_wrap(_fib_anon_field(n1, v1, _fib_anon_field(n2, v2, NULL)))\n";
	spr ctx "#define FIB_ANON_NEW_3(n1, v1, n2, v2, n3, v3) \\\n";
	spr ctx "\t_fib_anon_wrap(_fib_anon_field(n1, v1, _fib_anon_field(n2, v2, _fib_anon_field(n3, v3, NULL))))\n";
	spr ctx "#define FIB_ANON_NEW_4(n1, v1, n2, v2, n3, v3, n4, v4) \\\n";
	spr ctx "\t_fib_anon_wrap(_fib_anon_field(n1, v1, _fib_anon_field(n2, v2, _fib_anon_field(n3, v3, _fib_anon_field(n4, v4, NULL)))))\n";
	spr ctx "#define FIB_ANON_NEW_5(n1, v1, n2, v2, n3, v3, n4, v4, n5, v5) \\\n";
	spr ctx "\t_fib_anon_wrap(_fib_anon_field(n1, v1, _fib_anon_field(n2, v2, _fib_anon_field(n3, v3, _fib_anon_field(n4, v4, _fib_anon_field(n5, v5, NULL))))))\n";
	spr ctx "#define FIB_ANON_NEW_6(n1, v1, n2, v2, n3, v3, n4, v4, n5, v5, n6, v6) \\\n";
	spr ctx "\t_fib_anon_wrap(_fib_anon_field(n1, v1, _fib_anon_field(n2, v2, _fib_anon_field(n3, v3, _fib_anon_field(n4, v4, _fib_anon_field(n5, v5, _fib_anon_field(n6, v6, NULL)))))))\n";
	spr ctx "/* Note: FIB_ANON_NEW_N macros are called directly with the field count */\n\n";
	spr ctx "/* FIB_STACK_ALLOC - zero-initialized stack allocation (standard C) */\n";
	spr ctx "/* Usage: type* ptr = FIB_STACK_ALLOC(type, varname); */\n";
	spr ctx "/* Note: This expands to a comma expression that declares + returns ptr */\n";
	spr ctx "#define FIB_STACK_ALLOC(type, name) \\\n";
	spr ctx "\t((type*)memset(&(type){0}, 0, sizeof(type)))\n\n";
	spr ctx "/* Dynamic closure call helpers (standard C, no GCC extensions) */\n";
	spr ctx "/* These functions wrap fib_closure_call_dynamic with fixed argument counts */\n";
	spr ctx "static inline FibDynamic _fib_dyn_call_0(FibDynamic c) {\n";
	spr ctx "\treturn fib_closure_call_dynamic((FibClosure*)fib_dynamic_to_object(c), NULL, 0);\n";
	spr ctx "}\n";
	spr ctx "static inline FibDynamic _fib_dyn_call_1(FibDynamic c, FibDynamic a0) {\n";
	spr ctx "\tFibDynamic args[1] = {a0};\n";
	spr ctx "\treturn fib_closure_call_dynamic((FibClosure*)fib_dynamic_to_object(c), args, 1);\n";
	spr ctx "}\n";
	spr ctx "static inline FibDynamic _fib_dyn_call_2(FibDynamic c, FibDynamic a0, FibDynamic a1) {\n";
	spr ctx "\tFibDynamic args[2] = {a0, a1};\n";
	spr ctx "\treturn fib_closure_call_dynamic((FibClosure*)fib_dynamic_to_object(c), args, 2);\n";
	spr ctx "}\n";
	spr ctx "static inline FibDynamic _fib_dyn_call_3(FibDynamic c, FibDynamic a0, FibDynamic a1, FibDynamic a2) {\n";
	spr ctx "\tFibDynamic args[3] = {a0, a1, a2};\n";
	spr ctx "\treturn fib_closure_call_dynamic((FibClosure*)fib_dynamic_to_object(c), args, 3);\n";
	spr ctx "}\n";
	spr ctx "static inline FibDynamic _fib_dyn_call_4(FibDynamic c, FibDynamic a0, FibDynamic a1, FibDynamic a2, FibDynamic a3) {\n";
	spr ctx "\tFibDynamic args[4] = {a0, a1, a2, a3};\n";
	spr ctx "\treturn fib_closure_call_dynamic((FibClosure*)fib_dynamic_to_object(c), args, 4);\n";
	spr ctx "}\n";
	spr ctx "static inline FibDynamic _fib_dyn_call_5(FibDynamic c, FibDynamic a0, FibDynamic a1, FibDynamic a2, FibDynamic a3, FibDynamic a4) {\n";
	spr ctx "\tFibDynamic args[5] = {a0, a1, a2, a3, a4};\n";
	spr ctx "\treturn fib_closure_call_dynamic((FibClosure*)fib_dynamic_to_object(c), args, 5);\n";
	spr ctx "}\n";
	spr ctx "static inline FibDynamic _fib_dyn_call_6(FibDynamic c, FibDynamic a0, FibDynamic a1, FibDynamic a2, FibDynamic a3, FibDynamic a4, FibDynamic a5) {\n";
	spr ctx "\tFibDynamic args[6] = {a0, a1, a2, a3, a4, a5};\n";
	spr ctx "\treturn fib_closure_call_dynamic((FibClosure*)fib_dynamic_to_object(c), args, 6);\n";
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
	spr ctx "}\n";
	spr ctx "/* Fiber_spawnWithStack - spawn fiber with custom stack size */\n";
	spr ctx "static inline Fiber* Fiber_spawnWithStack(size_t stackSize, FibClosure* closure) {\n";
	spr ctx "\t/* Push temp root to protect closure during fiber creation */\n";
	spr ctx "\tgc_push_temp_root((void**)&closure);\n";
	spr ctx "\tFiber* fiber = scheduler_spawn_sized(stackSize, _fib_spawn_closure_trampoline, (void*)closure);\n";
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
	spr ctx "static inline FibString* GC_statsString(void) {\n";
	spr ctx "\tchar* cstr = gc_stats_string();\n";
	spr ctx "\tif (!cstr) return fib_string_new(\"\");\n";
	spr ctx "\tFibString* result = fib_string_new(cstr);\n";
	spr ctx "\tfree(cstr);\n";
	spr ctx "\treturn result;\n";
	spr ctx "}\n";
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
				print ctx "\t%s* this = gc_alloc_object_with_class(sizeof(%s), &%s_class);" class_name class_name class_name;
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
					let is_simple = is_simple_constructor f in
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
						print ctx "\t%s* this = gc_alloc_object_with_class(sizeof(%s), &%s_class);" class_name class_name class_name;
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
		in_fiber_spawn = false;
		spawn_counter = 0;
		gc_local_count = 0;
		loop_depth = 0;
		has_gc_ctx = false;
		stack_alloc_vars = Hashtbl.create 0;
		vtable_ctx = None;
		method_thunks = Hashtbl.create 16;
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
