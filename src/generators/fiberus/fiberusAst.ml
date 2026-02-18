(*
 * FiberusAst - C-AST intermediate representation for Fiberus code generator
 *
 * This module defines the intermediate representation (IR) used between
 * Haxe AST processing and C code emission. It provides:
 * - Type-safe representation of C constructs
 * - Clear separation between analysis and emission phases
 * - Explicit GC integration points
 * - Support for all Fiberus runtime features
 *)

open Globals

(* ============================================================================
 * C Type Representation
 * ============================================================================ *)

(* Array kinds for specialized array types *)
type tc_array_kind =
  | TCArrGeneric                            (* FibArray* *)
  | TCArrInt                                (* FibIntArray* *)
  | TCArrFloat                              (* FibFloatArray* *)
  | TCArrBool                               (* FibBoolArray* *)
  | TCArrUInt8                              (* FibUInt8Array* *)
  | TCArrInt64                              (* FibInt64Array* *)
  | TCArrUInt64                             (* FibUInt64Array* *)
  | TCArrFloat32                            (* FibFloat32Array* *)

(* C type representation - detailed for type safety *)
type tc_type =
  (* Primitives *)
  | TCVoid
  | TCBool
  | TCChar
  | TCInt8 | TCInt16 | TCInt32 | TCInt64
  | TCUInt8 | TCUInt16 | TCUInt32 | TCUInt64
  | TCSizeT
  | TCFloat32 | TCFloat64
  | TCAtomicInt
  
  (* Pointers *)
  | TCPointer of tc_type                    (* T* *)
  | TCConstPointer of tc_type               (* const T* *)
  
  (* Fiberus runtime types *)
  | TCFibDynamic                            (* FibDynamic struct *)
  | TCFibString                             (* FibString* *)
  | TCFibArray of tc_array_kind             (* Specialized arrays *)
  | TCFibClosure                            (* FibClosure* *)
  | TCFibObject                             (* FibObject* *)
  | TCFiber                                 (* Fiber* - runtime fiber struct *)
  | TCFibClass of string                    (* ClassName* *)
  | TCFibEnum of string                     (* EnumName struct *)
  | TCFibIntMap                             (* FibIntMap* *)
  | TCFibStringMap                          (* FibStringMap* *)
  | TCFibInt64Map                           (* FibInt64Map* *)
  | TCFibObjectMap                          (* FibObjectMap* *)
  | TCFibBytesData                          (* FibBytesData* *)
  
  (* Aggregate types *)
  | TCStruct of string                      (* struct Name *)
  | TCUnion of string                       (* union Name *)
  
  (* Function pointer *)
  | TCFuncPtr of tc_type list * tc_type     (* (args) -> ret *)
  
  (* Raw C type (escape hatch) *)
  | TCRaw of string

(* Boxing kinds for FibDynamic conversion *)
type tc_box_kind =
  | TCBoxInt
  | TCBoxInt64
  | TCBoxFloat
  | TCBoxBool
  | TCBoxString
  | TCBoxArray
  | TCBoxObject
  | TCBoxClosure
  | TCBoxEnum of string
  | TCBoxDynamic                            (* Already FibDynamic, passthrough *)
  | TCBoxNull

(* Binary operators *)
type tc_binop =
  | TCOpAdd | TCOpSub | TCOpMul | TCOpDiv | TCOpMod
  | TCOpEq | TCOpNeq | TCOpLt | TCOpLte | TCOpGt | TCOpGte
  | TCOpAnd | TCOpOr | TCOpXor | TCOpShl | TCOpShr | TCOpUShr
  | TCOpBoolAnd | TCOpBoolOr

(* Unary operators *)
type tc_unop =
  | TCUNeg | TCUNot | TCUBitNot
  | TCUPreInc | TCUPreDec | TCUPostInc | TCUPostDec

(* ============================================================================
 * C Expressions
 * ============================================================================ *)

(* Call target variants *)
type tc_call_target =
  | TCTFunc of string                       (* Direct function call *)
  | TCTFuncPtr of tc_expr                   (* Indirect via pointer *)
  | TCTMethod of string * string            (* Class_method *)
  | TCTMacro of string                      (* Macro invocation *)

(* Array access information *)
and tc_array_access = {
  arr: tc_expr;
  idx: tc_expr;
  arr_kind: tc_array_kind;
  elem_type: tc_type;
}

(* C expression with type, position, and GC root tracking *)
and tc_expr = {
  cexpr: tc_expr_kind;
  ctype: tc_type;
  cpos: pos;
  gc_roots: int;  (* Unpaired GC roots this expression leaves on stack.
                   * Used by wrap_with_gc_extraction to track roots that need
                   * to be popped at statement boundaries. Default is 0. *)
  pending_stmts: tc_stmt list;  (* Statements that must be emitted BEFORE this expression.
                                 * Used for lifting complex sub-expressions to statement level,
                                 * avoiding GCC statement expressions ({ ... }).
                                 * Empty list means no pending statements. *)
}

and tc_expr_kind =
  (* Literals *)
  | TCEInt of int32
  | TCEInt64 of int64
  | TCEFloat of string
  | TCEString of string                     (* Creates FibString* via fib_string_new *)
  | TCERawString of string                  (* Raw C string literal "..." *)
  | TCEBool of bool
  | TCENull
  | TCEThis
  | TCESizeOf of tc_type                    (* sizeof(T) *)
  
  (* Variables & Fields *)
  | TCELocal of string                      (* Local variable *)
  | TCEStatic of string * string            (* Class_field *)
  | TCEField of tc_expr * string            (* expr->field or expr.field *)
  | TCEArrow of tc_expr * string            (* expr->field (explicit pointer) *)
  | TCEDot of tc_expr * string              (* expr.field (explicit struct) *)
  | TCEDeref of tc_expr                     (* *expr *)
  | TCEAddrOf of tc_expr                    (* &expr *)
  | TCEParentField of tc_expr * string * string  (* ((ParentType)expr)->field *)
  
  (* Operations *)
  | TCEBinop of tc_binop * tc_expr * tc_expr
  | TCEUnop of tc_unop * tc_expr
  | TCEAssign of tc_expr * tc_expr          (* lvalue = rvalue *)
  | TCEAssignOp of tc_binop * tc_expr * tc_expr  (* lvalue op= rvalue *)
  | TCECast of tc_type * tc_expr            (* (type)expr *)
  | TCETernary of tc_expr * tc_expr * tc_expr  (* cond ? then : else *)
  | TCEComma of tc_expr list                (* (e1, e2, ..., en) *)
  
  (* Calls *)
  | TCECall of tc_call_target * tc_expr list
  | TCEVtableCall of {                      (* Virtual dispatch *)
      obj: tc_expr;
      slot: int;
      this_type: tc_type;
      ret_type: tc_type;
      cast_arg_types: tc_type list;         (* Types for the function pointer cast - from defining class *)
      args: tc_expr list;
      is_interface: bool;                   (* True if called through an interface reference *)
    }
  | TCEClosureCall of {                     (* Closure call *)
      closure: tc_expr;
      arg_types: tc_type list;
      ret_type: tc_type;
      args: tc_expr list;
    }
  | TCEDynamicCall of {                     (* fib_closure_call_dynamic *)
      closure: tc_expr;
      args: tc_expr list;
    }
  | TCEClosureCreate of {                   (* Create a FibClosure *)
      cc_name: string;                        (* _closure_N *)
      cc_impl_name: string;                   (* _closure_N_impl *)
      cc_captures: (string * string * tc_type) list;   (* (capture_expr, var_name, type) triples:
                                                           capture_expr = C expression for the value at creation site (may be _gc.name)
                                                           var_name = bare name used inside the closure body *)
      cc_arg_count: int;
      cc_for_fiber: bool;                     (* Use fib_closure_create_for_fiber *)
    }
  | TCEMethodClosure of {                  (* Create FibClosure from method reference *)
      mc_thunk_name: string;                 (* Typed thunk function name *)
      mc_dyn_thunk_name: string;             (* Dynamic thunk function name *)
      mc_is_static: bool;                    (* Static methods don't capture 'this' *)
      mc_arg_count: int;                     (* Number of method arguments *)
      mc_obj: tc_expr option;                (* 'this' expr for instance methods; None for static *)
    }
  
  (* Memory *)
  | TCEAlloc of string * tc_expr option     (* gc_alloc with optional size expr *)
  | TCEAllocCtx of string                   (* gc_alloc_ctx for hot paths *)
  | TCEStackAlloc of string * tc_type       (* Stack-allocated struct *)
  
  (* Arrays *)
  | TCEArrayGet of tc_array_access
  | TCEArraySet of tc_array_access * tc_expr
  | TCEArrayDecl of tc_expr list * tc_type  (* Compound literal array *)
  | TCEArrayLength of tc_expr * tc_array_kind
  | TCEArrayFromValues of {
      afv_kind: tc_array_kind;
      afv_c_type: string;      (* "int32_t", "double", "FibDynamic", etc. *)
      afv_values: tc_expr list;
    }
  
  (* Boxing/Unboxing (explicit in AST) *)
  | TCEBox of tc_expr * tc_box_kind         (* Wrap value in FibDynamic *)
  | TCEUnbox of tc_expr * tc_type           (* Extract value from FibDynamic *)
  
  (* Enum operations *)
  | TCEEnumIndex of tc_expr                 (* enum.index *)
  | TCEEnumParam of tc_expr * int           (* enum.params[i] *)
  | TCEEnumConstruct of string * string * tc_expr list  (* EnumName_Constructor(args) *)
  | TCEEnumConst of string * string         (* EnumName_Constructor (no args) *)
  
  (* Object operations *)
  | TCENew of string * tc_expr list         (* Class_new(args) *)
  | TCEInstanceOf of tc_expr * string       (* Std.is equivalent *)
  | TCEAnonObject of (string * tc_expr) list * bool  (* Anonymous object { field: value, ... }, heap_alloc *)
  
  (* String operations *)
  | TCEStringConcat of tc_expr * tc_expr    (* fib_string_concat *)
  | TCEStringEq of tc_expr * tc_expr        (* fib_string_eq *)
  | TCEStringCompare of tc_expr * tc_expr   (* fib_string_compare - returns int <0, 0, >0 *)
  | TCEStringLength of tc_expr              (* fib_string_length *)
  
  (* Compound expressions *)
  | TCEBlock of tc_stmt list * tc_expr option  (* ({ stmts; expr }) *)
  | TCERaw of string                        (* Raw C code (escape hatch) *)

(* ============================================================================
 * C Statements
 * ============================================================================ *)

(* GCFrame information for shadow stack frame declaration *)
and gc_frame_slot = {
  gfs_name: string;      (* Slot name (e.g., "param_a", "_gc_tmp0") *)
  gfs_type: tc_type;     (* Type of the slot (e.g., TCFibString) *)
  gfs_init: tc_expr option;  (* Initial value (Some for params, None for temps) *)
}

and gc_frame_info = {
  gfi_name: string;      (* Frame variable name (e.g., "_gc") *)
  gfi_slots: gc_frame_slot list;  (* Ordered list of slots *)
}

and tc_stmt =
  (* Basic *)
  | TCSExpr of tc_expr                      (* expr; *)
  | TCSVar of tc_var_decl                   (* type name = init; *)
  | TCSBlock of tc_stmt list                (* { stmts } *)
  | TCSEmpty                                (* ; *)
  
  (* Control flow *)
  | TCSIf of tc_expr * tc_stmt list * tc_stmt list option
  | TCSWhile of tc_expr * tc_stmt list * bool  (* cond, body, is_do_while *)
  | TCSFor of tc_for_init * tc_expr option * tc_expr option * tc_stmt list
  | TCSSwitch of tc_switch
  | TCSReturn of tc_expr option
  | TCSBreak
  | TCSContinue
  | TCSGoto of string
  | TCSLabel of string
  
  (* Exception handling *)
  | TCSTry of tc_try
  | TCSThrow of tc_expr
  
  (* GC integration (explicit) - legacy push/pop for non-frame contexts *)
  | TCSGCPush of tc_expr                    (* gc_push_temp_root(&expr) *)
  | TCSGCPop of int                         (* gc_pop_temp_roots(n) *)
  | TCSGCCtx                                (* FIB_GC_CTX; *)
  | TCSGCSafePoint                          (* GC_SAFE_POINT(); *)
  | TCSGCRootCheck of int                   (* Debug assertion: check root count equals base + n *)
  
  (* GCFrame-based GC root tracking (shadow stack) *)
  | TCSGCFrameDecl of gc_frame_info         (* Declare + link frame struct *)
  | TCSGCFramePop of string                 (* Unlink frame: GC_FRAME_POP(ctx, name) *)
  | TCSGCFrameAssign of string * string * tc_expr  (* _gc.slot = expr;  (frame_name, slot_name, value) *)
  
  (* Fiber integration *)
  | TCSYieldPoint                           (* FIBER_YIELD_POINT(); *)
  | TCSForceMature of tc_stmt              (* gc_force_mature_begin(); stmt; gc_force_mature_end(); *)
  
  (* Debug/profiling *)
  | TCSStackFrame of tc_stack_frame         (* FIB_STACKFRAME(...) *)
  | TCSLine of int                          (* FIBLINE(n) *)
  
  (* Raw C (escape hatch) *)
  | TCSRaw of string
  | TCSComment of string                    (* /* comment */ *)

and tc_var_decl = {
  vd_name: string;
  vd_type: tc_type;
  vd_init: tc_expr option;
  vd_static: bool;
  vd_const: bool;
  vd_volatile: bool;
}

and tc_for_init =
  | TCForVar of tc_var_decl
  | TCForExpr of tc_expr option

and tc_switch = {
  sw_expr: tc_expr;
  sw_cases: (tc_expr list * tc_stmt list) list;  (* values, body *)
  sw_default: tc_stmt list option;
}

and tc_try = {
  try_body: tc_stmt list;
  try_catches: tc_catch list;
}

(* Haxe-level catch kind for type dispatch *)
and tc_catch_kind =
  | TCCatchDynamic           (* Dynamic - catches everything *)
  | TCCatchInt               (* Int *)
  | TCCatchFloat             (* Float *)
  | TCCatchBool              (* Bool *)
  | TCCatchString            (* String *)
  | TCCatchObject of string  (* Class name (for instanceof check) *)
  | TCCatchEnum of string    (* Enum name (for FIB_TYPE_ENUM + meta check) *)

and tc_catch = {
  catch_var: string;
  catch_type: tc_type;
  catch_kind: tc_catch_kind;
  catch_body: tc_stmt list;
}

and tc_stack_frame = {
  sf_class: string;
  sf_func: string;
  sf_file: string;
  sf_line: int;
}

(* ============================================================================
 * Top-Level Declarations
 * ============================================================================ *)

type tc_decl =
  | TCDStruct of tc_struct_def
  | TCDEnum of tc_enum_def
  | TCDFunc of tc_func_def
  | TCDVar of tc_var_decl
  | TCDTypedef of string * tc_type
  | TCDForwardStruct of string
  | TCDForwardFunc of tc_func_sig
  | TCDExtern of tc_var_decl
  | TCDInclude of string * bool             (* file, is_system_header *)
  | TCDDefine of string * string option     (* name, value *)
  | TCDRaw of string
  | TCDVtable of tc_vtable_def              (* static void* vtable[N] = { ... } *)
  | TCDClassMeta of tc_class_meta           (* FibClass ClassName_class = { ... } *)

and tc_struct_def = {
  sd_name: string;
  sd_parent: string option;                 (* Embedded parent for inheritance *)
  sd_fields: tc_struct_field list;
}

and tc_vtable_def = {
  vt_name: string;                          (* e.g., "ClassName_vtable" *)
  vt_size: int;                             (* Array size (max_slot + 1) *)
  vt_entries: tc_vtable_entry list;         (* Populated slots; gaps filled with NULL *)
}

and tc_class_meta = {
  cm_name: string;                          (* Display name, e.g. "tests.SimplePerson" *)
  cm_var_name: string;                      (* C variable prefix, e.g. "tests_SimplePerson" *)
  cm_class_id: int;
  cm_instance_size: string;                 (* sizeof expression, e.g. "sizeof(ClassName)" *)
  cm_super: string option;                  (* Parent class C name, or None *)
  cm_mark_func: string option;              (* Mark function name, or None *)
  cm_tostring_func: string option;          (* toString function name, or None *)
  cm_vtable_name: string option;            (* Vtable variable name, or None *)
  cm_vtable_size: int;
  cm_ivtable_name: string option;           (* Interface vtable variable name, or None *)
  cm_fields: (string * tc_type) list;        (* Instance fields: (name, type) for Reflect *)
  cm_methods: tc_method_desc list;           (* Instance methods for dynamic dispatch *)
  cm_static_fields: (string * tc_type) list; (* Static fields: (name, type) for getClassFields *)
  cm_static_methods: tc_method_desc list;    (* Static methods for class-as-value dispatch *)
  cm_ctor: tc_method_desc option;            (* Constructor thunk for Type.createInstance *)
  cm_interfaces: string list;                (* Interface class C names this class implements *)
}

(* Method descriptor for fib_dynamic_get_field runtime lookup *)
and tc_method_desc = {
  md_name: string;                           (* Haxe method name (e.g. "iterator") *)
  md_thunk_name: string;                     (* Typed thunk C function name *)
  md_dyn_thunk_name: string;                 (* Dynamic thunk C function name *)
  md_arg_count: int;                         (* Number of params (excluding 'this') *)
}

and tc_vtable_entry = {
  ve_slot: int;
  ve_method_name: string;
  ve_impl_name: string;
}

and tc_struct_field = {
  sf_name: string;
  sf_type: tc_type;
  sf_comment: string option;
}

and tc_enum_def = {
  ed_name: string;
  ed_constrs: tc_enum_constr list;
  ed_max_params: int;                       (* For params array size *)
}

and tc_enum_constr = {
  ec_name: string;
  ec_index: int;
  ec_params: (string * tc_type) list;
}

and tc_func_def = {
  fd_name: string;
  fd_ret: tc_type;
  fd_args: tc_func_arg list;
  fd_body: tc_stmt list;
  fd_static: bool;                          (* static keyword *)
  fd_inline: bool;                          (* inline keyword *)
  fd_attrs: string list;                    (* __attribute__(...) *)
}

and tc_func_arg = {
  fa_name: string;
  fa_type: tc_type;
}

and tc_func_sig = {
  fs_name: string;
  fs_ret: tc_type;
  fs_args: tc_type list;
}

(* ============================================================================
 * Method Thunk Representation (for FClosure / method-as-value)
 * ============================================================================ *)

(* A method thunk wraps a class method so it can be called via FibClosure.
 * Two functions are generated per thunk:
 *   - Typed thunk: takes typed parameters, calls the real method
 *   - Dynamic thunk: takes FibDynamic params, unboxes, calls typed thunk *)
type tc_method_thunk = {
  mth_thunk_name: string;           (* e.g. __ClassName_method_thunk *)
  mth_dyn_thunk_name: string;       (* e.g. __ClassName_method_thunk_dyn *)
  mth_is_static: bool;              (* Static methods don't capture 'this' *)
  mth_class_name: string;           (* C name of the class *)
  mth_method_name: string;          (* C name of the method *)
  mth_args: (string * tc_type) list; (* (param_name, param_type) pairs *)
  mth_ret_type: tc_type;            (* Return type *)
  mth_c_func: string option;        (* Override C function name, e.g. "fib_array_iterator" *)
  mth_this_expr: string option;     (* Override this-extract expression, e.g. "fib_dynamic_to_array(...)" *)
  mth_vtable_slot: int option;      (* Interface vtable slot for dispatch instead of direct call *)
  mth_defaults: string option list; (* Per-arg default C literal for null substitution in dynamic thunks, e.g. Some "2", Some "4.25" *)
}

(* ============================================================================
 * Closure Representation
 * ============================================================================ *)

type tc_closure = {
  cl_id: int;                               (* Unique ID *)
  cl_name: string;                          (* _closure_N *)
  cl_impl_name: string;                     (* _closure_N_impl *)
  cl_args: tc_func_arg list;
  cl_ret: tc_type;
  cl_captures: tc_capture list;
  cl_body: tc_stmt list;
  cl_defaults: tc_expr option list;         (* Per-arg default value for wrapper null checks *)
}

and tc_capture = {
  cap_var: string;
  cap_type: tc_type;
  cap_index: int;
}

(* ============================================================================
 * Class Representation
 * ============================================================================ *)

type tc_class = {
  tcl_name: string;
  tcl_path: path;
  tcl_id: int;
  tcl_struct: tc_struct_def;
  tcl_class_meta: tc_class_meta;
  tcl_constructor: tc_func_def option;
  tcl_new_func: tc_func_def option;
  tcl_static_funcs: tc_func_def list;
  tcl_methods: tc_func_def list;
  tcl_static_vars: tc_var_decl list;
  tcl_closures: tc_closure list;
  tcl_boot_func: tc_func_def option;
  tcl_vtable: tc_vtable_entry list;
  tcl_mark_func: tc_func_def option;        (* GC mark function *)
}

(* ============================================================================
 * Compilation Unit
 * ============================================================================ *)

type tc_unit = {
  tu_includes: string list;
  tu_decls: tc_decl list;
}

(* ============================================================================
 * Helper Functions
 * ============================================================================ *)

(* Create a simple expression with null position, zero gc_roots, and no pending statements *)
let mk_expr kind typ =
  { cexpr = kind; ctype = typ; cpos = null_pos; gc_roots = 0; pending_stmts = [] }

(* Create an expression with position, zero gc_roots, and no pending statements *)
let mk_expr_pos kind typ pos =
  { cexpr = kind; ctype = typ; cpos = pos; gc_roots = 0; pending_stmts = [] }

(* Create an expression with explicit GC root count and no pending statements *)
let mk_expr_gc kind typ gc_roots =
  { cexpr = kind; ctype = typ; cpos = null_pos; gc_roots; pending_stmts = [] }

(* Create an expression with position, explicit GC root count, and no pending statements *)
let mk_expr_pos_gc kind typ pos gc_roots =
  { cexpr = kind; ctype = typ; cpos = pos; gc_roots; pending_stmts = [] }

(* Create an expression with pending statements (for lifting) *)
let mk_expr_lifted kind typ pending_stmts =
  { cexpr = kind; ctype = typ; cpos = null_pos; gc_roots = 0; pending_stmts }

(* Create an expression with pending statements and gc_roots *)
let mk_expr_lifted_gc kind typ pending_stmts gc_roots =
  { cexpr = kind; ctype = typ; cpos = null_pos; gc_roots; pending_stmts }

(* Sum gc_roots from multiple sub-expressions *)
let sum_gc_roots exprs =
  List.fold_left (fun acc e -> acc + e.gc_roots) 0 exprs

(* Collect all pending_stmts from multiple sub-expressions *)
let collect_pending exprs =
  List.concat_map (fun e -> e.pending_stmts) exprs

(* Maximum gc_roots from expressions (for control flow branches) *)
let max_gc_roots exprs =
  List.fold_left (fun acc e -> max acc e.gc_roots) 0 exprs

(* Create an expression inheriting gc_roots and pending_stmts from sub-expressions *)
let mk_expr_inherit kind typ sub_exprs =
  { cexpr = kind; ctype = typ; cpos = null_pos; 
    gc_roots = sum_gc_roots sub_exprs; 
    pending_stmts = collect_pending sub_exprs }

(* Add pending statements to an existing expression *)
let with_pending stmts expr =
  { expr with pending_stmts = stmts @ expr.pending_stmts }

(* Extract a pure expression (no pending_stmts) and its pending statements *)
let flatten_expr expr =
  (expr.pending_stmts, { expr with pending_stmts = [] })

(* Create an integer literal *)
let mk_int i =
  mk_expr (TCEInt i) TCInt32

(* Create an int64 literal *)
let mk_int64 i =
  mk_expr (TCEInt64 i) TCInt64

(* Create a float literal *)
let mk_float s =
  mk_expr (TCEFloat s) TCFloat64

(* Create a boolean literal *)
let mk_bool b =
  mk_expr (TCEBool b) TCBool

(* Create a null literal *)
let mk_null typ =
  mk_expr TCENull typ

(* Create a string literal *)
let mk_string s =
  mk_expr (TCEString s) TCFibString

(* Create a raw string literal *)
let mk_raw_string s =
  mk_expr (TCERawString s) (TCPointer TCChar)

(* Create a local variable reference *)
let mk_local name typ =
  mk_expr (TCELocal name) typ

(* Create this reference *)
let mk_this class_name =
  mk_expr TCEThis (TCFibClass class_name)

(* Create a field access *)
let mk_field obj field_name field_type =
  mk_expr (TCEField (obj, field_name)) field_type

(* Create a function call *)
let mk_call func_name args ret_type =
  mk_expr (TCECall (TCTFunc func_name, args)) ret_type

(* Create a method call *)
let mk_method_call class_name method_name args ret_type =
  mk_expr (TCECall (TCTMethod (class_name, method_name), args)) ret_type

(* Create an assignment *)
let mk_assign lhs rhs =
  mk_expr (TCEAssign (lhs, rhs)) lhs.ctype

(* Create a binary operation *)
let mk_binop op lhs rhs result_type =
  mk_expr (TCEBinop (op, lhs, rhs)) result_type

(* Create a cast *)
let mk_cast target_type expr =
  mk_expr (TCECast (target_type, expr)) target_type

(* Create boxing to FibDynamic *)
let mk_box expr kind =
  mk_expr (TCEBox (expr, kind)) TCFibDynamic

(* Create unboxing from FibDynamic *)
let mk_unbox expr target_type =
  mk_expr (TCEUnbox (expr, target_type)) target_type

(* Create a variable declaration statement *)
let mk_var_stmt name typ init =
  TCSVar { vd_name = name; vd_type = typ; vd_init = init; vd_static = false; vd_const = false; vd_volatile = false }

(* Create an expression statement *)
let mk_expr_stmt expr =
  TCSExpr expr

(* Create a return statement *)
let mk_return expr =
  TCSReturn expr

(* Create an if statement *)
let mk_if cond then_stmts else_stmts =
  TCSIf (cond, then_stmts, else_stmts)

(* Create a while loop *)
let mk_while cond body =
  TCSWhile (cond, body, false)

(* Create a do-while loop *)
let mk_do_while body cond =
  TCSWhile (cond, body, true)

(* Check if type is a pointer type *)
let is_pointer_type = function
  | TCPointer _ | TCConstPointer _ | TCFibString | TCFibClosure
  | TCFibObject | TCFiber | TCFibClass _ | TCFibArray _ 
  | TCFibIntMap | TCFibStringMap | TCFibInt64Map | TCFibObjectMap
  | TCFibBytesData -> true
  (* Map iterator types are pointers *)
  | TCRaw "FibIntMapKeyIterator*" | TCRaw "FibIntMapValueIterator*"
  | TCRaw "FibStringMapKeyIterator*" | TCRaw "FibStringMapValueIterator*"
  | TCRaw "FibInt64MapKeyIterator*" | TCRaw "FibInt64MapValueIterator*"
  | TCRaw "FibObjectMapKeyIterator*" | TCRaw "FibObjectMapValueIterator*" -> true
  | _ -> false

(* Check if type is a primitive type *)
let is_primitive_type = function
  | TCVoid | TCBool | TCChar
  | TCInt8 | TCInt16 | TCInt32 | TCInt64
  | TCUInt8 | TCUInt16 | TCUInt32 | TCUInt64
  | TCSizeT | TCFloat32 | TCFloat64 | TCAtomicInt -> true
  | _ -> false

(* Check if type needs GC tracking *)
let rec needs_gc_tracking = function
  | TCFibString | TCFibClosure | TCFibObject | TCFiber | TCFibClass _
  | TCFibArray _ | TCFibDynamic
  | TCFibIntMap | TCFibStringMap | TCFibInt64Map | TCFibObjectMap
  | TCFibBytesData -> true
  | TCPointer inner -> needs_gc_tracking inner
  (* Map iterator types are GC-allocated and need tracking *)
  | TCRaw "FibIntMapKeyIterator*" | TCRaw "FibIntMapValueIterator*"
  | TCRaw "FibStringMapKeyIterator*" | TCRaw "FibStringMapValueIterator*"
  | TCRaw "FibInt64MapKeyIterator*" | TCRaw "FibInt64MapValueIterator*"
  | TCRaw "FibObjectMapKeyIterator*" | TCRaw "FibObjectMapValueIterator*" -> true
  | _ -> false
