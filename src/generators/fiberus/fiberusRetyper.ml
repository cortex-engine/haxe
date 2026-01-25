(*
 * FiberusRetyper - Haxe AST to C-AST conversion utilities
 *
 * This module provides utilities for converting Haxe typed AST to the
 * Fiberus C-AST (FiberusAst). It handles:
 * - Basic expression conversion
 * - Type coercion detection
 * - Boxing/unboxing requirements
 * - Operator mapping
 *
 * The full expression conversion is complex and tightly integrated with
 * the generator context; this module provides the building blocks.
 *)

open Globals
open Ast
open Type
open FiberusAst
open FiberusTypeUtils

(* ============================================================================
 * Operator Conversion
 * ============================================================================ *)

(* Convert Haxe binary operator to C-AST binary operator *)
let convert_binop (op : Ast.binop) : tc_binop option =
  match op with
  | OpAdd -> Some TCOpAdd
  | OpSub -> Some TCOpSub
  | OpMult -> Some TCOpMul
  | OpDiv -> Some TCOpDiv
  | OpMod -> Some TCOpMod
  | OpEq -> Some TCOpEq
  | OpNotEq -> Some TCOpNeq
  | OpLt -> Some TCOpLt
  | OpLte -> Some TCOpLte
  | OpGt -> Some TCOpGt
  | OpGte -> Some TCOpGte
  | OpAnd -> Some TCOpAnd
  | OpOr -> Some TCOpOr
  | OpXor -> Some TCOpXor
  | OpShl -> Some TCOpShl
  | OpShr -> Some TCOpShr
  | OpUShr -> Some TCOpUShr  (* Note: needs special handling at codegen *)
  | OpBoolAnd -> Some TCOpBoolAnd
  | OpBoolOr -> Some TCOpBoolOr
  | OpAssign -> None  (* Assignment handled separately *)
  | OpAssignOp _ -> None  (* Compound assignment handled separately *)
  | OpInterval -> None  (* Not a C operator *)
  | OpArrow -> None  (* Not a C operator *)
  | OpIn -> None  (* Not a C operator *)
  | OpNullCoal -> None  (* Needs special handling *)

(* Convert Haxe unary operator to C-AST unary operator *)
let convert_unop (op : Ast.unop) (is_postfix : bool) : tc_unop option =
  match op, is_postfix with
  | Neg, false -> Some TCUNeg
  | Not, false -> Some TCUNot
  | NegBits, false -> Some TCUBitNot
  | Increment, false -> Some TCUPreInc
  | Increment, true -> Some TCUPostInc
  | Decrement, false -> Some TCUPreDec
  | Decrement, true -> Some TCUPostDec
  | Spread, _ -> None  (* Not a C operator *)
  | _, _ -> None

(* ============================================================================
 * Constant Conversion
 * ============================================================================ *)

(* Convert Haxe constant to C-AST expression *)
let convert_constant (c : tconstant) (pos : pos) : tc_expr =
  match c with
  | TInt i -> 
      { cexpr = TCEInt i; ctype = TCInt32; cpos = pos }
  | TFloat s -> 
      { cexpr = TCEFloat s; ctype = TCFloat64; cpos = pos }
  | TString s -> 
      { cexpr = TCEString s; ctype = TCFibString; cpos = pos }
  | TBool b -> 
      { cexpr = TCEBool b; ctype = TCBool; cpos = pos }
  | TNull -> 
      { cexpr = TCENull; ctype = TCFibDynamic; cpos = pos }
  | TThis -> 
      { cexpr = TCEThis; ctype = TCFibObject; cpos = pos }  (* Type refined by context *)
  | TSuper -> 
      (* Super is handled specially in field access *)
      { cexpr = TCEThis; ctype = TCFibObject; cpos = pos }

(* ============================================================================
 * Type Coercion Detection
 * ============================================================================ *)

(* Coercion kinds for value conversion *)
type coercion =
  | NoCoercion                          (* Types match, no conversion needed *)
  | BoxToDynamic of tc_box_kind         (* Wrap primitive in FibDynamic *)
  | UnboxFromDynamic of tc_type         (* Extract primitive from FibDynamic *)
  | CastToClass of string               (* Cast FibObject/FibDynamic to class pointer *)
  | CastToObject                        (* Cast class pointer to FibObject *)
  | StringToFibString                   (* Raw C string to FibString (rare) *)
  | NumericCast of tc_type              (* Numeric type cast (int to float, etc.) *)

(* Determine what coercion is needed to convert from source to target type *)
let get_coercion (source : tc_type) (target : tc_type) : coercion =
  if source = target then NoCoercion
  else match source, target with
  (* Boxing to FibDynamic *)
  | TCInt32, TCFibDynamic -> BoxToDynamic TCBoxInt
  | TCInt64, TCFibDynamic -> BoxToDynamic TCBoxInt64
  | TCFloat64, TCFibDynamic -> BoxToDynamic TCBoxFloat
  | TCFloat32, TCFibDynamic -> BoxToDynamic TCBoxFloat
  | TCBool, TCFibDynamic -> BoxToDynamic TCBoxBool
  | TCFibString, TCFibDynamic -> BoxToDynamic TCBoxString
  | TCFibArray _, TCFibDynamic -> BoxToDynamic TCBoxArray
  | TCFibClosure, TCFibDynamic -> BoxToDynamic TCBoxClosure
  | TCFibObject, TCFibDynamic -> BoxToDynamic TCBoxObject
  | TCFibClass _, TCFibDynamic -> BoxToDynamic TCBoxObject
  | TCFibEnum name, TCFibDynamic -> BoxToDynamic (TCBoxEnum name)
  
  (* Unboxing from FibDynamic *)
  | TCFibDynamic, TCInt32 -> UnboxFromDynamic TCInt32
  | TCFibDynamic, TCInt64 -> UnboxFromDynamic TCInt64
  | TCFibDynamic, TCFloat64 -> UnboxFromDynamic TCFloat64
  | TCFibDynamic, TCFloat32 -> UnboxFromDynamic TCFloat32
  | TCFibDynamic, TCBool -> UnboxFromDynamic TCBool
  | TCFibDynamic, TCFibString -> UnboxFromDynamic TCFibString
  | TCFibDynamic, TCFibArray k -> UnboxFromDynamic (TCFibArray k)
  | TCFibDynamic, TCFibClosure -> UnboxFromDynamic TCFibClosure
  | TCFibDynamic, TCFibObject -> UnboxFromDynamic TCFibObject
  | TCFibDynamic, TCFibClass name -> CastToClass name
  
  (* Class pointer conversions *)
  | TCFibClass _, TCFibObject -> CastToObject
  | TCFibObject, TCFibClass name -> CastToClass name
  | TCFibClass _, TCFibClass name -> CastToClass name  (* Upcast/downcast *)
  
  (* Numeric conversions *)
  | TCInt32, TCFloat64 -> NumericCast TCFloat64
  | TCFloat64, TCInt32 -> NumericCast TCInt32
  | TCInt32, TCInt64 -> NumericCast TCInt64
  | TCInt64, TCInt32 -> NumericCast TCInt32
  | TCFloat32, TCFloat64 -> NumericCast TCFloat64
  | TCFloat64, TCFloat32 -> NumericCast TCFloat32
  
  (* Default: no coercion (may need explicit cast in generated code) *)
  | _, _ -> NoCoercion

(* Apply coercion to an expression, returning a new expression *)
let apply_coercion (coercion : coercion) (expr : tc_expr) : tc_expr =
  match coercion with
  | NoCoercion -> expr
  | BoxToDynamic kind ->
      { cexpr = TCEBox (expr, kind); ctype = TCFibDynamic; cpos = expr.cpos }
  | UnboxFromDynamic target_type ->
      { cexpr = TCEUnbox (expr, target_type); ctype = target_type; cpos = expr.cpos }
  | CastToClass name ->
      { cexpr = TCECast (TCFibClass name, expr); ctype = TCFibClass name; cpos = expr.cpos }
  | CastToObject ->
      { cexpr = TCECast (TCFibObject, expr); ctype = TCFibObject; cpos = expr.cpos }
  | StringToFibString ->
      { cexpr = TCECall (TCTFunc "fib_string_new", [expr]); ctype = TCFibString; cpos = expr.cpos }
  | NumericCast target_type ->
      { cexpr = TCECast (target_type, expr); ctype = target_type; cpos = expr.cpos }

(* Coerce expression to target type if needed *)
let coerce_to (expr : tc_expr) (target : tc_type) : tc_expr =
  let coercion = get_coercion expr.ctype target in
  apply_coercion coercion expr

(* ============================================================================
 * Expression Helpers
 * ============================================================================ *)

(* Create a local variable reference *)
let make_local (v : tvar) : tc_expr =
  let tc_type = tc_type_of v.v_type in
  { cexpr = TCELocal (FiberusStrings.ident v.v_name); ctype = tc_type; cpos = null_pos }

(* Create a 'this' reference for a class *)
let make_this (class_name : string) : tc_expr =
  { cexpr = TCEThis; ctype = TCFibClass class_name; cpos = null_pos }

(* Create a null check expression *)
let make_null_check (expr : tc_expr) : tc_expr =
  { cexpr = TCEBinop (TCOpNeq, expr, { cexpr = TCENull; ctype = expr.ctype; cpos = expr.cpos });
    ctype = TCBool;
    cpos = expr.cpos }

(* Create a field access *)
let make_field_access (obj : tc_expr) (field : string) (field_type : tc_type) : tc_expr =
  { cexpr = TCEField (obj, field); ctype = field_type; cpos = obj.cpos }

(* Create a static field reference *)
let make_static_field (class_name : string) (field : string) (field_type : tc_type) : tc_expr =
  { cexpr = TCEStatic (class_name, field); ctype = field_type; cpos = null_pos }

(* Create a function call *)
let make_call (func : string) (args : tc_expr list) (ret_type : tc_type) : tc_expr =
  { cexpr = TCECall (TCTFunc func, args); ctype = ret_type; cpos = null_pos }

(* Create a method call *)
let make_method_call (class_name : string) (method_name : string) (args : tc_expr list) (ret_type : tc_type) : tc_expr =
  { cexpr = TCECall (TCTMethod (class_name, method_name), args); ctype = ret_type; cpos = null_pos }

(* ============================================================================
 * Statement Helpers
 * ============================================================================ *)

(* Create an expression statement *)
let make_expr_stmt (expr : tc_expr) : tc_stmt =
  TCSExpr expr

(* Create a variable declaration *)
let make_var_decl (name : string) (typ : tc_type) (init : tc_expr option) : tc_stmt =
  TCSVar { vd_name = name; vd_type = typ; vd_init = init; vd_static = false; vd_const = false }

(* Create a return statement *)
let make_return (expr : tc_expr option) : tc_stmt =
  TCSReturn expr

(* Create an if statement *)
let make_if (cond : tc_expr) (then_stmts : tc_stmt list) (else_stmts : tc_stmt list option) : tc_stmt =
  TCSIf (cond, then_stmts, else_stmts)

(* Create a while loop *)
let make_while (cond : tc_expr) (body : tc_stmt list) : tc_stmt =
  TCSWhile (cond, body, false)

(* Create a block *)
let make_block (stmts : tc_stmt list) : tc_stmt =
  TCSBlock stmts

(* ============================================================================
 * GC Integration Helpers
 * ============================================================================ *)

(* Create GC push statement for a local variable *)
let make_gc_push (var_name : string) (var_type : tc_type) : tc_stmt =
  let var_ref = { cexpr = TCELocal var_name; ctype = var_type; cpos = null_pos } in
  TCSGCPush var_ref

(* Create GC pop statement *)
let make_gc_pop (count : int) : tc_stmt =
  TCSGCPop count

(* Create GC context declaration *)
let make_gc_ctx () : tc_stmt =
  TCSGCCtx

(* Check if a type needs GC root tracking *)
let type_needs_gc_root (t : tc_type) : bool =
  needs_gc_root t

(* ============================================================================
 * Array Access Helpers
 * ============================================================================ *)

(* Create array access info from Haxe array expression *)
let make_array_access (arr : tc_expr) (idx : tc_expr) (arr_type : Type.t) : tc_array_access =
  let arr_kind = match tc_type_of arr_type with
    | TCFibArray k -> k
    | _ -> TCArrGeneric
  in
  let elem_type = get_array_elem_type arr_type in
  { arr; idx; arr_kind; elem_type }

(* Create array get expression *)
let make_array_get (access : tc_array_access) : tc_expr =
  { cexpr = TCEArrayGet access; ctype = access.elem_type; cpos = access.arr.cpos }

(* Create array set expression *)
let make_array_set (access : tc_array_access) (value : tc_expr) : tc_expr =
  { cexpr = TCEArraySet (access, value); ctype = access.elem_type; cpos = access.arr.cpos }

(* ============================================================================
 * String Operation Helpers
 * ============================================================================ *)

(* Create string concatenation *)
let make_string_concat (lhs : tc_expr) (rhs : tc_expr) : tc_expr =
  { cexpr = TCEStringConcat (lhs, rhs); ctype = TCFibString; cpos = lhs.cpos }

(* Create string equality check *)
let make_string_eq (lhs : tc_expr) (rhs : tc_expr) : tc_expr =
  { cexpr = TCEStringEq (lhs, rhs); ctype = TCBool; cpos = lhs.cpos }

(* Check if binary operation on strings needs special handling *)
let is_string_binop (op : Ast.binop) (lhs_type : tc_type) (rhs_type : tc_type) : bool =
  (lhs_type = TCFibString || rhs_type = TCFibString) &&
  match op with
  | OpAdd -> true  (* String concatenation *)
  | OpEq | OpNotEq -> true  (* String comparison *)
  | _ -> false

(* ============================================================================
 * Enum Helpers
 * ============================================================================ *)

(* Create enum index access *)
let make_enum_index (enum_expr : tc_expr) : tc_expr =
  { cexpr = TCEEnumIndex enum_expr; ctype = TCInt32; cpos = enum_expr.cpos }

(* Create enum parameter access *)
let make_enum_param (enum_expr : tc_expr) (param_idx : int) : tc_expr =
  { cexpr = TCEEnumParam (enum_expr, param_idx); ctype = TCFibDynamic; cpos = enum_expr.cpos }

(* Create enum constructor call *)
let make_enum_construct (enum_name : string) (constr : string) (args : tc_expr list) : tc_expr =
  { cexpr = TCEEnumConstruct (enum_name, constr, args); ctype = TCFibEnum enum_name; cpos = null_pos }

(* ============================================================================
 * Object Construction Helpers
 * ============================================================================ *)

(* Create object allocation *)
let make_new (class_name : string) (args : tc_expr list) : tc_expr =
  { cexpr = TCENew (class_name, args); ctype = TCFibClass class_name; cpos = null_pos }

(* Create instanceof check *)
let make_instanceof (obj : tc_expr) (class_name : string) : tc_expr =
  { cexpr = TCEInstanceOf (obj, class_name); ctype = TCBool; cpos = obj.cpos }
