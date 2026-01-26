(*
 * FiberusConvert - Haxe AST to C-AST conversion
 *
 * This module implements Phase 1 of the code generation pipeline:
 * converting Haxe typed AST (texpr) to C-AST (tc_expr/tc_stmt).
 *
 * The goal is to separate type analysis from string emission,
 * enabling better optimization and cleaner code generation.
 *)

open Globals
open Ast
open Type
open FiberusAst
open FiberusTypeUtils
open FiberusStrings
open FiberusEscape

(* ============================================================================
 * Conversion Context
 * ============================================================================ *)

(* Conversion context - minimal state needed during conversion *)
type conv_ctx = {
  current_class: tclass option;       (* Current class being processed *)
  current_class_name: string option;  (* Current class C name *)
  vtable_ctx: FiberusVtable.vtable_context option;  (* Vtable for virtual dispatch *)
  current_ret_type: tc_type option;   (* Expected return type for coercion *)
  (* GC tracking for statement conversion *)
  mutable gc_local_count: int;        (* Current temp roots pushed in this scope *)
  mutable loop_depth: int;            (* Nesting depth for yield points *)
}

(* Create an empty conversion context *)
let empty_ctx = {
  current_class = None;
  current_class_name = None;
  vtable_ctx = None;
  current_ret_type = None;
  gc_local_count = 0;
  loop_depth = 0;
}

(* Create context with current class *)
let ctx_with_class c = {
  empty_ctx with
  current_class = Some c;
  current_class_name = Some (flat_path c.cl_path);
  current_ret_type = None;
}

(* Create a context copy for nested scope (preserves gc_local_count for tracking) *)
let ctx_for_scope ctx = {
  ctx with
  gc_local_count = ctx.gc_local_count;  (* Will be mutated independently *)
}

(* ============================================================================
 * GC-Aware Conversion Helpers
 * ============================================================================ *)

(* Check if a tc_type needs GC root registration when stored in a local variable *)
let needs_gc_root_tc = FiberusTypeUtils.needs_gc_root

(* Generate GC push statement if type needs it, incrementing gc_local_count *)
let gc_push_if_needed ctx var_name var_type =
  if needs_gc_root_tc var_type then begin
    ctx.gc_local_count <- ctx.gc_local_count + 1;
    [TCSGCPush (mk_expr (TCELocal var_name) var_type)]
  end else
    []

(* Generate GC pop statement for n roots, decrementing gc_local_count *)
let gc_pop_roots ctx n =
  if n > 0 then begin
    ctx.gc_local_count <- ctx.gc_local_count - n;
    [TCSGCPop n]
  end else
    []

(* Calculate how many roots to pop to return to saved count *)
let gc_roots_to_pop ctx saved_count =
  ctx.gc_local_count - saved_count

(* Save current gc_local_count for later restoration *)
let gc_save_count ctx = ctx.gc_local_count

(* Coerce an expression to a target type (boxing/unboxing as needed) *)
let coerce_to_type expr target_tc =
  if expr.ctype = target_tc then expr
  else if target_tc = TCFibDynamic && expr.ctype <> TCFibDynamic then
    (* Box to FibDynamic *)
    mk_expr (TCEBox (expr, box_kind_of_type expr.ctype)) TCFibDynamic
  else if expr.ctype = TCFibDynamic && target_tc <> TCFibDynamic then
    (* Unbox from FibDynamic *)
    mk_expr (TCEUnbox (expr, target_tc)) target_tc
  else
    (* Other type conversions - just return as-is for now *)
    expr

(* ============================================================================
 * Operator Conversion
 * ============================================================================ *)

(* Convert Haxe binary operator to C-AST binary operator *)
let rec convert_binop = function
  | OpAdd -> TCOpAdd
  | OpMult -> TCOpMul
  | OpDiv -> TCOpDiv
  | OpSub -> TCOpSub
  | OpEq -> TCOpEq
  | OpNotEq -> TCOpNeq
  | OpGt -> TCOpGt
  | OpGte -> TCOpGte
  | OpLt -> TCOpLt
  | OpLte -> TCOpLte
  | OpAnd -> TCOpAnd
  | OpOr -> TCOpOr
  | OpXor -> TCOpXor
  | OpBoolAnd -> TCOpBoolAnd
  | OpBoolOr -> TCOpBoolOr
  | OpShl -> TCOpShl
  | OpShr -> TCOpShr
  | OpUShr -> TCOpUShr
  | OpMod -> TCOpMod
  | OpAssign -> TCOpAdd  (* Assignment handled separately *)
  | OpAssignOp op -> convert_binop op
  | OpInterval -> TCOpAdd  (* Not used in C *)
  | OpArrow -> TCOpAdd     (* Not used in C *)
  | OpIn -> TCOpAdd        (* Not used in C *)
  | OpNullCoal -> TCOpAdd  (* Handled specially *)

(* Convert Haxe unary operator to C-AST unary operator *)
let convert_unop op flag =
  match op, flag with
  | Increment, Prefix -> TCUPreInc
  | Decrement, Prefix -> TCUPreDec
  | Not, Prefix -> TCUNot
  | Neg, Prefix -> TCUNeg
  | NegBits, Prefix -> TCUBitNot
  | Increment, Postfix -> TCUPostInc
  | Decrement, Postfix -> TCUPostDec
  | Spread, _ -> TCUNot  (* Not really used *)
  | _, _ -> TCUNot       (* Fallback *)

(* ============================================================================
 * Expression Conversion - Literals
 * ============================================================================ *)

(* Convert Haxe constant to C-AST expression *)
let convert_constant pos = function
  | TInt i -> 
      mk_expr_pos (TCEInt i) TCInt32 pos
  | TFloat s -> 
      mk_expr_pos (TCEFloat s) TCFloat64 pos
  | TString s ->
      mk_expr_pos (TCEString s) TCFibString pos
  | TBool b ->
      mk_expr_pos (TCEBool b) TCBool pos
  | TNull ->
      (* Type depends on context - use void pointer as default *)
      mk_expr_pos TCENull (TCPointer TCVoid) pos
  | TThis ->
      mk_expr_pos TCEThis (TCPointer TCVoid) pos
  | TSuper ->
      (* Super is treated as this in C *)
      mk_expr_pos TCEThis (TCPointer TCVoid) pos

(* Convert constant with known target type for null handling *)
let convert_constant_typed pos target_tc = function
  | TNull ->
      (* Use target type for null *)
      mk_expr_pos TCENull target_tc pos
  | c -> convert_constant pos c

(* ============================================================================
 * Expression Conversion - Core
 * ============================================================================ *)

(* Forward declaration for mutual recursion *)
let rec convert_expr (ctx : conv_ctx) (e : texpr) : tc_expr =
  let tc = tc_type_of e.etype in
  let pos = e.epos in
  match e.eexpr with
  (* Literals *)
  | TConst c ->
      convert_constant_typed pos tc c
  
  (* Local variable reference *)
  | TLocal v ->
      let name = ident v.v_name in
      let vtype = tc_type_of v.v_type in
      mk_expr_pos (TCELocal name) vtype pos
  
  (* Parentheses - just unwrap *)
  | TParenthesis inner ->
      convert_expr ctx inner
  
  (* Meta annotations - just unwrap *)
  | TMeta (_, inner) ->
      convert_expr ctx inner
  
  (* Type cast *)
  | TCast (inner, _) ->
      let inner_expr = convert_expr ctx inner in
      let from_tc = inner_expr.ctype in
      if from_tc = tc then
        inner_expr
      else if from_tc = TCFibDynamic then
        (* Unbox from FibDynamic to target type *)
        mk_expr_pos (TCEUnbox (inner_expr, tc)) tc pos
      else if tc = TCFibDynamic then
        (* Box to FibDynamic *)
        let box_kind = box_kind_of_type from_tc in
        mk_expr_pos (TCEBox (inner_expr, box_kind)) tc pos
      else
        (* Regular cast *)
        mk_expr_pos (TCECast (tc, inner_expr)) tc pos
  
  (* Binary operations *)
  | TBinop (op, e1, e2) ->
      convert_binop_expr ctx op e1 e2 tc pos
  
  (* Unary operations *)
  | TUnop (op, flag, inner) ->
      convert_unop_expr ctx op flag inner tc pos
  
  (* Block expression - last expression is the value *)
  | TBlock exprs ->
      convert_block_expr ctx exprs tc pos
  
  (* Array literal *)
  | TArrayDecl items ->
      convert_array_literal ctx items tc pos
  
  (* Object instantiation *)
  | TNew (c, tl, args) ->
      (* Special handling for Array<T> -> fib_*_array_new() *)
      if c.cl_path = ([], "Array") then begin
        let arr_func = match tl with
          | [elem_t] ->
              (match Type.follow elem_t with
              | TAbstract ({ a_path = ([], "Int") }, []) -> "fib_int_array_new"
              | TAbstract ({ a_path = ([], "Float") }, []) -> "fib_float_array_new"
              | TAbstract ({ a_path = ([], "Bool") }, []) -> "fib_bool_array_new"
              | TAbstract ({ a_path = (["fiberus"], "UInt8") }, []) -> "fib_uint8_array_new"
              | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "fib_int64_array_new"
              | TAbstract ({ a_path = (["fiberus"], "UInt64") }, []) -> "fib_uint64_array_new"
              | TAbstract ({ a_path = (["fiberus"], "Float32") }, []) -> "fib_float32_array_new"
              | _ -> "fib_array_new")
          | _ -> "fib_array_new"
        in
        mk_expr_pos (TCECall (TCTFunc arr_func, [])) tc pos
      end
      (* Hash map types *)
      else if c.cl_path = (["haxe"; "ds"], "IntMap") then
        mk_expr_pos (TCECall (TCTFunc "fib_int_map_new", [])) TCFibIntMap pos
      else if c.cl_path = (["haxe"; "ds"], "StringMap") then
        mk_expr_pos (TCECall (TCTFunc "fib_string_map_new", [])) TCFibStringMap pos
      else if c.cl_path = (["haxe"; "ds"], "Int64Map") then
        mk_expr_pos (TCECall (TCTFunc "fib_int64_map_new", [])) TCFibInt64Map pos
      else if c.cl_path = (["haxe"; "ds"], "ObjectMap") then
        mk_expr_pos (TCECall (TCTFunc "fib_object_map_new", [])) TCFibObjectMap pos
      else begin
        let class_name = flat_path c.cl_path in
        let arg_exprs = List.map (convert_expr ctx) args in
        mk_expr_pos (TCENew (class_name, arg_exprs)) (TCFibClass class_name) pos
      end
  
  (* If expression (ternary) *)
  | TIf (cond, ethen, Some eelse) when not (is_void tc) ->
      let cond_expr = convert_expr ctx cond in
      (* Extract bool from FibDynamic condition *)
      let cond_expr = 
        if cond_expr.ctype = TCFibDynamic then
          mk_expr (TCECall (TCTFunc "fib_dynamic_to_bool", [cond_expr])) TCBool
        else
          cond_expr
      in
      let then_expr = convert_expr ctx ethen in
      let else_expr = convert_expr ctx eelse in
      let then_tc = then_expr.ctype in
      let else_tc = else_expr.ctype in
      (* Coerce branches to same type if one is FibDynamic *)
      let then_expr, else_expr, result_tc = 
        if then_tc = TCFibDynamic && else_tc <> TCFibDynamic then
          (then_expr, mk_expr (TCEBox (else_expr, box_kind_of_type else_tc)) TCFibDynamic, TCFibDynamic)
        else if else_tc = TCFibDynamic && then_tc <> TCFibDynamic then
          (mk_expr (TCEBox (then_expr, box_kind_of_type then_tc)) TCFibDynamic, else_expr, TCFibDynamic)
        else
          (then_expr, else_expr, tc)
      in
      mk_expr_pos (TCETernary (cond_expr, then_expr, else_expr)) result_tc pos
  
  (* Field access *)
  | TField (obj, fa) ->
      convert_field_access ctx obj fa tc pos
  
  (* Array access *)
  | TArray (arr, idx) ->
      convert_array_access ctx arr idx tc pos
  
  (* Function call *)
  | TCall (callee, args) ->
      convert_call ctx callee args tc pos
  
  (* Return (in expression context, e.g., block returning value) *)
  | TReturn (Some inner) ->
      let inner_expr = convert_expr ctx inner in
      (* In expression context, this is unusual but handle it *)
      inner_expr
  
  (* Enum construction with index *)
  | TEnumIndex inner ->
      let inner_expr = convert_expr ctx inner in
      (* Check if inner expression is from dynamic field access *)
      let is_dyn = match inner.eexpr with
        | TField (_, FAnon _) | TField (_, FDynamic _) -> true
        | _ -> false
      in
      if is_dyn then
        (* FibDynamic enum - use helper function *)
        mk_expr_pos (TCECall (TCTFunc "fib_dynamic_enum_index", [inner_expr])) TCInt32 pos
      else
        mk_expr_pos (TCEEnumIndex inner_expr) TCInt32 pos
  
  (* Enum parameter access *)
  | TEnumParameter (inner, _, idx) ->
      let inner_expr = convert_expr ctx inner in
      let param_access = mk_expr_pos (TCEEnumParam (inner_expr, idx)) TCFibDynamic pos in
      (* Unbox from FibDynamic if target type isn't FibDynamic *)
      if tc = TCFibDynamic then
        param_access
      else
        mk_expr_pos (TCEUnbox (param_access, tc)) tc pos
  
  (* Raw identifier (used for __fiberus__ and similar) *)
  | TIdent s ->
      mk_expr_pos (TCELocal (ident s)) tc pos
  
  (* Type expression - just emit the type name as a local variable reference *)
  | TTypeExpr mt ->
      let path = Type.t_path mt in
      let name = flat_path path in
      mk_expr_pos (TCELocal name) tc pos
  
  (* For remaining unhandled cases, emit raw placeholder *)
  | TVar _ | TFunction _ | TWhile _ | TSwitch _ | TTry _ | TBreak | TContinue | TThrow _ ->
      (* These are statements, not value expressions - shouldn't reach here in value context *)
      mk_expr_pos (TCERaw (Printf.sprintf "/* stmt in expr context: %s */" (Type.s_expr_kind e))) tc pos
  
  | TObjectDecl fl ->
      (* Anonymous object declaration *)
      if fl = [] then
        mk_expr_pos (TCECall (TCTFunc "fib_anon_new", [])) TCFibDynamic pos
      else begin
        (* Build list of field assignments for TCEAnonObject *)
        let fields = List.map (fun ((name, _, _), field_e) ->
          let field_expr = convert_expr ctx field_e in
          (* Box to FibDynamic based on type *)
          let boxed = match field_expr.ctype with
            | TCFibDynamic -> field_expr
            | TCInt32 -> mk_expr (TCEBox (field_expr, TCBoxInt)) TCFibDynamic
            | TCFloat64 -> mk_expr (TCEBox (field_expr, TCBoxFloat)) TCFibDynamic
            | TCBool -> mk_expr (TCEBox (field_expr, TCBoxBool)) TCFibDynamic
            | TCFibString -> mk_expr (TCECall (TCTFunc "fib_string_to_dynamic", [field_expr])) TCFibDynamic
            | _ -> field_expr
          in
          (name, boxed)
        ) fl in
        mk_expr_pos (TCEAnonObject fields) TCFibDynamic pos
      end
  
  | TIf (cond, ethen, None) ->
      (* If without else in expression context - return fib_dynamic_null for else *)
      let cond_expr = convert_expr ctx cond in
      let cond_expr = 
        if cond_expr.ctype = TCFibDynamic then
          mk_expr (TCECall (TCTFunc "fib_dynamic_to_bool", [cond_expr])) TCBool
        else
          cond_expr
      in
      let then_expr = convert_expr ctx ethen in
      let then_tc = then_expr.ctype in
      (* Box then branch if needed, else is always FibDynamic null *)
      let then_expr = 
        if then_tc <> TCFibDynamic then
          mk_expr (TCEBox (then_expr, box_kind_of_type then_tc)) TCFibDynamic
        else
          then_expr
      in
      let else_expr = mk_expr (TCECall (TCTFunc "fib_dynamic_null", [])) TCFibDynamic in
      mk_expr_pos (TCETernary (cond_expr, then_expr, else_expr)) TCFibDynamic pos
  
  | TReturn None ->
      (* Return without value in expression context - unusual *)
      mk_expr_pos (TCERaw "/* return void */") TCVoid pos

(* ============================================================================
 * Binary Operation Conversion
 * ============================================================================ *)

and convert_binop_expr ctx op e1 e2 result_tc pos =
  (* Check for null constant *)
  let is_null_const e = match e.Type.eexpr with Type.TConst Type.TNull -> true | _ -> false in
  let is_null_compare = is_null_const e1 || is_null_const e2 in
  
  (* Check if type is enum struct *)
  let is_enum_struct_type t = match Type.follow t with Type.TEnum _ -> true | _ -> false in
  
  (* Check if expression came from dynamic field access *)
  let rec is_dynamic_access e = match e.Type.eexpr with
    | Type.TField (_, Type.FAnon _) | Type.TField (_, Type.FDynamic _) -> true
    | Type.TCast (inner, _) | Type.TMeta (_, inner) | Type.TParenthesis inner -> is_dynamic_access inner
    | _ -> false
  in
  
  (* Check for enum struct that's not from dynamic access *)
  let is_enum_struct_expr e =
    not (is_null_const e) && is_enum_struct_type e.Type.etype && not (is_dynamic_access e)
  in
  
  (* Check if this is a string operation *)
  let is_string_op = FiberusBuiltins.is_string_type e1.Type.etype || 
                     FiberusBuiltins.is_string_type e2.Type.etype in
  
  match op with
  (* === ASSIGNMENT OPERATIONS === *)
  
  (* Array element assignment: arr[i] = value *)
  | OpAssign when (match e1.Type.eexpr with Type.TArray _ -> true | _ -> false) ->
      convert_array_assign ctx e1 e2 pos
  
  (* Field assignment - may need write barrier *)
  | OpAssign when (match e1.Type.eexpr with Type.TField (_, Type.FInstance _) -> true | _ -> false) ->
      convert_field_assign ctx e1 e2 pos
  
  (* Regular assignment with FibDynamic boxing if needed *)
  | OpAssign ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let rhs = box_if_needed e1_expr.ctype e2_expr in
      mk_expr_pos (TCEAssign (e1_expr, rhs)) e1_expr.ctype pos
  
  (* Unsigned right shift assignment *)
  | OpAssignOp OpUShr ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let e1_ex = extract_fib_dynamic e1_expr TCInt32 in
      let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
      let unsigned = mk_expr (TCECast (TCUInt32, e1_ex)) TCUInt32 in
      let shifted = mk_expr (TCEBinop (TCOpShr, unsigned, e2_ex)) TCUInt32 in
      let result = mk_expr (TCECast (TCInt32, shifted)) TCInt32 in
      if e1_expr.ctype = TCFibDynamic then
        let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [result])) TCFibDynamic in
        mk_expr_pos (TCEAssign (e1_expr, boxed)) TCFibDynamic pos
      else
        mk_expr_pos (TCEAssign (e1_expr, result)) TCInt32 pos
  
  (* Array compound assignment: arr[i] op= value *)
  | OpAssignOp inner_op when (match e1.Type.eexpr with Type.TArray _ -> true | _ -> false) ->
      convert_array_compound_assign ctx inner_op e1 e2 pos
  
  (* String compound assignment: s += "str" *)
  | OpAssignOp OpAdd when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = ensure_string ctx e1 e1_expr in
      let s2 = ensure_string ctx e2 e2_expr in
      let concat = mk_expr (TCEStringConcat (s1, s2)) TCFibString in
      mk_expr_pos (TCEAssign (e1_expr, concat)) TCFibString pos
  
  (* FibDynamic compound assignment: dyn op= value *)
  | OpAssignOp inner_op when (tc_type_of e1.Type.etype) = TCFibDynamic ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let e1_ex = extract_fib_dynamic e1_expr TCInt32 in
      let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
      let c_op = convert_binop inner_op in
      let result = mk_expr (TCEBinop (c_op, e1_ex, e2_ex)) TCInt32 in
      let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [result])) TCFibDynamic in
      mk_expr_pos (TCEAssign (e1_expr, boxed)) TCFibDynamic pos
  
  (* Regular compound assignment *)
  | OpAssignOp inner_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let e2_ex = extract_fib_dynamic e2_expr e1_expr.ctype in
      let c_op = convert_binop inner_op in
      mk_expr_pos (TCEAssignOp (c_op, e1_expr, e2_ex)) e1_expr.ctype pos
  
  (* === NULL COMPARISONS === *)
  
  (* Enum null check: enum == null -> enum.index == -1 *)
  | OpEq when is_null_compare && (is_enum_struct_expr e1 || is_enum_struct_expr e2) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let enum_expr = if is_null_const e1 then e2_expr else e1_expr in
      let index = mk_expr (TCEDot (enum_expr, "index")) TCInt32 in
      let neg_one = mk_int (-1l) in
      mk_expr_pos (TCEBinop (TCOpEq, index, neg_one)) TCBool pos
  
  | OpNotEq when is_null_compare && (is_enum_struct_expr e1 || is_enum_struct_expr e2) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let enum_expr = if is_null_const e1 then e2_expr else e1_expr in
      let index = mk_expr (TCEDot (enum_expr, "index")) TCInt32 in
      let neg_one = mk_int (-1l) in
      mk_expr_pos (TCEBinop (TCOpNeq, index, neg_one)) TCBool pos
  
  (* FibDynamic null check: dyn == null -> fib_dynamic_is_null(dyn) *)
  | OpEq when is_null_compare ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then
        let dyn_expr = if is_null_const e1 then e2_expr else e1_expr in
        mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_null", [dyn_expr])) TCBool pos
      else
        (* Regular null comparison *)
        mk_expr_pos (TCEBinop (TCOpEq, e1_expr, e2_expr)) TCBool pos
  
  | OpNotEq when is_null_compare ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then
        let dyn_expr = if is_null_const e1 then e2_expr else e1_expr in
        let is_null = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [dyn_expr])) TCBool in
        mk_expr_pos (TCEUnop (TCUNot, is_null)) TCBool pos
      else
        mk_expr_pos (TCEBinop (TCOpNeq, e1_expr, e2_expr)) TCBool pos
  
  (* === ENUM COMPARISONS === *)
  
  (* Enum struct comparison: enum1 == enum2 -> enum1.index == enum2.index *)
  | OpEq when is_enum_struct_expr e1 && is_enum_struct_expr e2 ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let idx1 = mk_expr (TCEDot (e1_expr, "index")) TCInt32 in
      let idx2 = mk_expr (TCEDot (e2_expr, "index")) TCInt32 in
      mk_expr_pos (TCEBinop (TCOpEq, idx1, idx2)) TCBool pos
  
  | OpNotEq when is_enum_struct_expr e1 && is_enum_struct_expr e2 ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let idx1 = mk_expr (TCEDot (e1_expr, "index")) TCInt32 in
      let idx2 = mk_expr (TCEDot (e2_expr, "index")) TCInt32 in
      mk_expr_pos (TCEBinop (TCOpNeq, idx1, idx2)) TCBool pos
  
  (* === STRING OPERATIONS === *)
  
  (* String concatenation *)
  | OpAdd when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = ensure_string ctx e1 e1_expr in
      let s2 = ensure_string ctx e2 e2_expr in
      mk_expr_pos (TCEStringConcat (s1, s2)) TCFibString pos
  
  (* String equality *)
  | OpEq when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = if e1_expr.ctype = TCFibDynamic 
               then mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [e1_expr])) TCFibString 
               else e1_expr in
      let s2 = if e2_expr.ctype = TCFibDynamic 
               then mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [e2_expr])) TCFibString 
               else e2_expr in
      mk_expr_pos (TCEStringEq (s1, s2)) TCBool pos
  
  (* String inequality *)
  | OpNotEq when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = if e1_expr.ctype = TCFibDynamic 
               then mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [e1_expr])) TCFibString 
               else e1_expr in
      let s2 = if e2_expr.ctype = TCFibDynamic 
               then mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [e2_expr])) TCFibString 
               else e2_expr in
      let eq = mk_expr (TCEStringEq (s1, s2)) TCBool in
      mk_expr_pos (TCEUnop (TCUNot, eq)) TCBool pos
  
  (* === UNSIGNED RIGHT SHIFT === *)
  
  | OpUShr ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let e1_ex = extract_fib_dynamic e1_expr TCInt32 in
      let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
      let unsigned = mk_expr_pos (TCECast (TCUInt32, e1_ex)) TCUInt32 pos in
      let shift = mk_expr_pos (TCEBinop (TCOpShr, unsigned, e2_ex)) TCUInt32 pos in
      mk_expr_pos (TCECast (TCInt32, shift)) TCInt32 pos
  
  (* === FIBDYNAMIC ARITHMETIC === *)
  
  (* Arithmetic operations - extract FibDynamic operands *)
  | (OpAdd | OpSub | OpMult | OpDiv | OpMod) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let target_tc = if result_tc = TCFibDynamic then TCInt32 else result_tc in
        let e1_ex = extract_fib_dynamic e1_expr target_tc in
        let e2_ex = extract_fib_dynamic e2_expr target_tc in
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) target_tc pos
      end else begin
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) result_tc pos
      end
  
  (* Comparison operations - extract FibDynamic operands *)
  | (OpLt | OpLte | OpGt | OpGte) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let target_tc = if e1_expr.ctype <> TCFibDynamic then e1_expr.ctype
                        else if e2_expr.ctype <> TCFibDynamic then e2_expr.ctype
                        else TCInt32 in
        let e1_ex = extract_fib_dynamic e1_expr target_tc in
        let e2_ex = extract_fib_dynamic e2_expr target_tc in
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCBool pos
      end else begin
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) TCBool pos
      end
  
  (* Equality with FibDynamic - extract to primitive for comparison *)
  | (OpEq | OpNotEq) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let target_tc = if e1_expr.ctype <> TCFibDynamic then e1_expr.ctype
                        else if e2_expr.ctype <> TCFibDynamic then e2_expr.ctype
                        else TCInt32 in
        let e1_ex = extract_fib_dynamic e1_expr target_tc in
        let e2_ex = extract_fib_dynamic e2_expr target_tc in
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCBool pos
      end else begin
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) TCBool pos
      end
  
  (* Bitwise operations - extract FibDynamic to int *)
  | (OpAnd | OpOr | OpXor | OpShl | OpShr) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let e1_ex = extract_fib_dynamic e1_expr TCInt32 in
        let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCInt32 pos
      end else begin
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) result_tc pos
      end
  
  (* Boolean operations - extract FibDynamic to bool *)
  | (OpBoolAnd | OpBoolOr) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let e1_ex = extract_fib_dynamic e1_expr TCBool in
        let e2_ex = extract_fib_dynamic e2_expr TCBool in
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCBool pos
      end else begin
        let c_op = convert_binop op in
        mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) TCBool pos
      end
  
  (* Remaining operators *)
  | _ ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let c_op = convert_binop op in
      mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) result_tc pos

(* Extract value from FibDynamic if needed *)
and extract_fib_dynamic expr target_tc =
  if expr.ctype <> TCFibDynamic then expr
  else
    let func = match target_tc with
      | TCInt32 -> "fib_dynamic_to_int"
      | TCInt64 -> "fib_dynamic_to_int64"
      | TCFloat64 -> "fib_dynamic_to_float"
      | TCBool -> "fib_dynamic_to_bool"
      | _ -> "fib_dynamic_to_int"
    in
    mk_expr (TCECall (TCTFunc func, [expr])) target_tc

(* Box value to FibDynamic if LHS is FibDynamic and RHS is not *)
and box_if_needed lhs_tc rhs_expr =
  if lhs_tc = TCFibDynamic && rhs_expr.ctype <> TCFibDynamic then
    mk_expr (TCEBox (rhs_expr, box_kind_of_type rhs_expr.ctype)) TCFibDynamic
  else
    rhs_expr

(* Convert array element assignment: arr[i] = value *)
and convert_array_assign ctx e1 e2 pos =
  match e1.Type.eexpr with
  | Type.TArray (arr, idx) ->
      let arr_expr = convert_expr ctx arr in
      let idx_expr = convert_expr ctx idx in
      let val_expr = convert_expr ctx e2 in
      let arr_kind = match arr_expr.ctype with TCFibArray k -> k | _ -> TCArrGeneric in
      let access = { arr = arr_expr; idx = idx_expr; arr_kind; elem_type = val_expr.ctype } in
      if arr_kind <> TCArrGeneric then
        (* Specialized array: fib_*_array_set(arr, idx, value) *)
        mk_expr_pos (TCEArraySet (access, val_expr)) val_expr.ctype pos
      else begin
        (* Generic array: box value to FibDynamic *)
        let boxed = 
          if val_expr.ctype = TCFibDynamic then val_expr
          else mk_expr (TCEBox (val_expr, box_kind_of_type val_expr.ctype)) TCFibDynamic
        in
        mk_expr_pos (TCEArraySet (access, boxed)) TCFibDynamic pos
      end
  | _ -> 
      (* Fallback - shouldn't happen *)
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      mk_expr_pos (TCEAssign (e1_expr, e2_expr)) e1_expr.ctype pos

(* Convert field assignment - may need write barrier *)
and convert_field_assign ctx e1 e2 pos =
  match e1.Type.eexpr with
  | Type.TField (obj, fa) ->
      let obj_expr = convert_expr ctx obj in
      let val_expr = convert_expr ctx e2 in
      let lhs_tc = tc_type_of e1.Type.etype in
      let rhs_tc = val_expr.ctype in
      (* Check if this is an instance field (has an object to barrier) *)
      let is_instance_field = match fa with
        | Type.FInstance _ | Type.FAnon _ | Type.FDynamic _ -> true
        | Type.FClosure (Some _, _) -> true
        | Type.FStatic _ | Type.FEnum _ | Type.FClosure (None, _) -> false
      in
      (* Convert the LHS field expression *)
      let lhs_expr = convert_expr ctx e1 in
      let rhs = box_if_needed lhs_tc val_expr in
      (* Check if write barrier needed - object pointers need barriers *)
      let needs_barrier = is_instance_field && needs_write_barrier_tc rhs_tc in
      if needs_barrier then
        (* Emit: (FIBRIX_WRITE_BARRIER(obj, value), obj->field = value) *)
        let barrier = mk_expr (TCECall (TCTMacro "FIBRIX_WRITE_BARRIER", [obj_expr; rhs])) TCVoid in
        let assign = mk_expr (TCEAssign (lhs_expr, rhs)) lhs_tc in
        mk_expr_pos (TCEComma [barrier; assign]) lhs_tc pos
      else
        mk_expr_pos (TCEAssign (lhs_expr, rhs)) lhs_tc pos
  | _ ->
      (* Fallback - regular assignment *)
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let rhs = box_if_needed e1_expr.ctype e2_expr in
      mk_expr_pos (TCEAssign (e1_expr, rhs)) e1_expr.ctype pos

(* Convert array compound assignment: arr[i] op= value *)
and convert_array_compound_assign ctx inner_op e1 e2 pos =
  match e1.Type.eexpr with
  | Type.TArray (arr, idx) ->
      let arr_expr = convert_expr ctx arr in
      let idx_expr = convert_expr ctx idx in
      let val_expr = convert_expr ctx e2 in
      let arr_kind = match arr_expr.ctype with TCFibArray k -> k | _ -> TCArrGeneric in
      let prefix = array_kind_prefix arr_kind in
      let elem_tc = match arr_kind with
        | TCArrInt -> TCInt32 | TCArrFloat -> TCFloat64 | TCArrBool -> TCBool
        | TCArrInt64 -> TCInt64 | TCArrUInt64 -> TCUInt64 | TCArrFloat32 -> TCFloat32
        | TCArrUInt8 -> TCUInt8 | TCArrGeneric -> TCFibDynamic
      in
      if arr_kind <> TCArrGeneric then begin
        (* Specialized: set(arr, idx, get(arr, idx) op value) *)
        let get_call = mk_expr (TCECall (TCTFunc (prefix ^ "get"), [arr_expr; idx_expr])) elem_tc in
        let c_op = convert_binop inner_op in
        let new_val = mk_expr (TCEBinop (c_op, get_call, val_expr)) elem_tc in
        mk_expr_pos (TCECall (TCTFunc (prefix ^ "set"), [arr_expr; idx_expr; new_val])) elem_tc pos
      end else begin
        (* Generic: set(arr, idx, fib_dynamic_int(fib_dynamic_to_int(get(arr, idx)) op value)) *)
        let get_call = mk_expr (TCECall (TCTFunc "fib_array_get", [arr_expr; idx_expr])) TCFibDynamic in
        let extracted = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [get_call])) TCInt32 in
        let val_ex = extract_fib_dynamic val_expr TCInt32 in
        let c_op = convert_binop inner_op in
        let computed = mk_expr (TCEBinop (c_op, extracted, val_ex)) TCInt32 in
        let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [computed])) TCFibDynamic in
        mk_expr_pos (TCECall (TCTFunc "fib_array_set", [arr_expr; idx_expr; boxed])) TCFibDynamic pos
      end
  | _ ->
      (* Fallback *)
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let c_op = convert_binop inner_op in
      mk_expr_pos (TCEAssignOp (c_op, e1_expr, e2_expr)) e1_expr.ctype pos

(* Ensure expression is a string (for concatenation) *)
and ensure_string _ctx _orig_expr c_expr =
  match c_expr.ctype with
  | TCFibString -> c_expr
  | TCInt32 ->
      mk_expr (TCECall (TCTFunc "fib_string_from_int", [c_expr])) TCFibString
  | TCInt64 ->
      mk_expr (TCECall (TCTFunc "fib_string_from_int64", [c_expr])) TCFibString
  | TCFloat64 ->
      mk_expr (TCECall (TCTFunc "fib_string_from_float", [c_expr])) TCFibString
  | TCBool ->
      (* Bool to string: use ternary *)
      mk_expr (TCETernary (c_expr, 
        mk_expr (TCEString "true") TCFibString,
        mk_expr (TCEString "false") TCFibString)) TCFibString
  | TCFibDynamic ->
      mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [c_expr])) TCFibString
  | TCFibClass _ | TCFibObject ->
      (* Object toString via dynamic call *)
      mk_expr (TCECall (TCTFunc "fib_object_to_string", [mk_expr (TCECast (TCFibObject, c_expr)) TCFibObject])) TCFibString
  | _ ->
      (* Default: convert to dynamic then to string *)
      let dyn = mk_expr (TCEBox (c_expr, box_kind_of_type c_expr.ctype)) TCFibDynamic in
      mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [dyn])) TCFibString

(* ============================================================================
 * Unary Operation Conversion
 * ============================================================================ *)

and convert_unop_expr ctx op flag inner result_tc pos =
  let inner_expr = convert_expr ctx inner in
  let inner_tc = inner_expr.ctype in
  
  match op, flag with
  (* Increment/Decrement on array element: arr[i]++ -> set(arr, i, get(arr, i) + 1) *)
  | (Ast.Increment | Ast.Decrement), _ when (match inner.eexpr with TArray _ -> true | _ -> false) ->
      (match inner.eexpr with
      | TArray (arr, idx) ->
          let arr_expr = convert_expr ctx arr in
          let idx_expr = convert_expr ctx idx in
          let arr_kind = match arr_expr.ctype with TCFibArray k -> k | _ -> TCArrGeneric in
          let delta_op = match op with Ast.Increment -> TCOpAdd | _ -> TCOpSub in
          let one = mk_int 1l in
          if arr_kind <> TCArrGeneric then begin
            (* Specialized array: prefix_set(arr, idx, prefix_get(arr, idx) +/- 1) *)
            let prefix = array_kind_prefix arr_kind in
            let get_call = mk_expr (TCECall (TCTFunc (prefix ^ "get"), [arr_expr; idx_expr])) result_tc in
            let new_val = mk_expr (TCEBinop (delta_op, get_call, one)) result_tc in
            mk_expr_pos (TCECall (TCTFunc (prefix ^ "set"), [arr_expr; idx_expr; new_val])) result_tc pos
          end else begin
            (* Generic array - just use standard operator *)
            let c_op = convert_unop op flag in
            mk_expr_pos (TCEUnop (c_op, inner_expr)) inner_tc pos
          end
      | _ -> 
          let c_op = convert_unop op flag in
          mk_expr_pos (TCEUnop (c_op, inner_expr)) inner_tc pos)
  
  (* Increment/Decrement on FibDynamic *)
  | (Ast.Increment | Ast.Decrement), _ when inner_tc = TCFibDynamic ->
      let delta_op = match op with Ast.Increment -> TCOpAdd | _ -> TCOpSub in
      let one = mk_int 1l in
      (* Extract int, compute, re-box, assign back *)
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [inner_expr])) TCInt32 in
      if flag = Ast.Prefix then begin
        (* Pre: ({ e = fib_dynamic_int(fib_dynamic_to_int(e) +/- 1); fib_dynamic_to_int(e); }) *)
        let new_val = mk_expr (TCEBinop (delta_op, extract, one)) TCInt32 in
        let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [new_val])) TCFibDynamic in
        let assign = TCSExpr (mk_expr (TCEAssign (inner_expr, boxed)) TCFibDynamic) in
        let result = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [inner_expr])) TCInt32 in
        mk_expr_pos (TCEBlock ([assign], Some result)) TCInt32 pos
      end else begin
        (* Post: ({ int32_t _old = fib_dynamic_to_int(e); e = fib_dynamic_int(_old +/- 1); _old; }) *)
        let old_var = TCSVar { vd_name = "_old"; vd_type = TCInt32; vd_init = Some extract; vd_static = false; vd_const = false } in
        let old_ref = mk_expr (TCELocal "_old") TCInt32 in
        let new_val = mk_expr (TCEBinop (delta_op, old_ref, one)) TCInt32 in
        let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [new_val])) TCFibDynamic in
        let assign = TCSExpr (mk_expr (TCEAssign (inner_expr, boxed)) TCFibDynamic) in
        mk_expr_pos (TCEBlock ([old_var; assign], Some old_ref)) TCInt32 pos
      end
  
  (* Regular increment/decrement *)
  | (Ast.Increment | Ast.Decrement), _ ->
      let c_op = convert_unop op flag in
      mk_expr_pos (TCEUnop (c_op, inner_expr)) inner_tc pos
  
  (* Not/Neg/NegBits on FibDynamic - need extraction *)
  | Ast.Not, _ when inner_tc = TCFibDynamic ->
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_bool", [inner_expr])) TCBool in
      mk_expr_pos (TCEUnop (TCUNot, extract)) TCBool pos
  
  | Ast.Neg, _ when inner_tc = TCFibDynamic ->
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [inner_expr])) TCInt32 in
      mk_expr_pos (TCEUnop (TCUNeg, extract)) TCInt32 pos
  
  | Ast.NegBits, _ when inner_tc = TCFibDynamic ->
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [inner_expr])) TCInt32 in
      mk_expr_pos (TCEUnop (TCUBitNot, extract)) TCInt32 pos
  
  (* Standard unary operations *)
  | _ ->
      let c_op = convert_unop op flag in
      mk_expr_pos (TCEUnop (c_op, inner_expr)) result_tc pos

(* ============================================================================
 * Block Expression Conversion
 * ============================================================================ *)

(* Convert a Haxe expression to C-AST statements - for use in block expressions.
   This handles statement-like expressions (TVar) that need GC tracking. *)
and convert_expr_as_stmt ctx (e : texpr) : tc_stmt list =
  match e.eexpr with
  | TVar (v, init_opt) ->
      let name = ident v.v_name in
      let vtype = tc_type_of v.v_type in
      let init = Option.map (convert_expr ctx) init_opt in
      let var_stmt = TCSVar { vd_name = name; vd_type = vtype; vd_init = init; vd_static = false; vd_const = false } in
      (* Add GC push for pointer types *)
      let gc_stmts = gc_push_if_needed ctx name vtype in
      var_stmt :: gc_stmts
  | TBlock exprs ->
      (* Nested block - flatten into statements *)
      List.concat_map (convert_expr_as_stmt ctx) exprs
  | TIf (cond, ethen, eelse_opt) ->
      let cond_expr = convert_expr ctx cond in
      let then_stmts = convert_expr_as_stmt ctx ethen in
      let else_stmts = Option.map (convert_expr_as_stmt ctx) eelse_opt in
      [TCSIf (cond_expr, then_stmts, else_stmts)]
  | TWhile (cond, body, flag) ->
      let cond_expr = convert_expr ctx cond in
      let body_stmts = convert_expr_as_stmt ctx body in
      let is_do_while = (flag = DoWhile) in
      [TCSWhile (cond_expr, body_stmts, is_do_while)]
  | TReturn expr_opt ->
      let ret_expr = match expr_opt with
        | None -> None
        | Some inner ->
            let inner_expr = convert_expr ctx inner in
            (* Coerce to return type if known *)
            match ctx.current_ret_type with
            | Some ret_tc -> Some (coerce_to_type inner_expr ret_tc)
            | None -> Some inner_expr
      in
      [TCSReturn ret_expr]
  | TBreak ->
      [TCSBreak]
  | TContinue ->
      [TCSContinue]
  | TThrow exc ->
      let exc_expr = convert_expr ctx exc in
      let boxed_expr = 
        if exc_expr.ctype = TCFibDynamic then exc_expr
        else mk_expr (TCEBox (exc_expr, box_kind_of_type exc_expr.ctype)) TCFibDynamic
      in
      [TCSThrow boxed_expr]
  | _ ->
      (* Regular expression - wrap in TCSExpr *)
      [TCSExpr (convert_expr ctx e)]

and convert_block_expr ctx exprs result_tc pos =
  match exprs with
  | [] ->
      (* Empty block - return void/null *)
      mk_expr_pos TCENull result_tc pos
  | [single] ->
      (* Single expression - just convert it *)
      convert_expr ctx single
  | _ ->
      (* Multiple expressions - create statement block with result *)
      (* Save GC count at start of block *)
      let saved_gc_count = gc_save_count ctx in
      (* Convert all but last expression as statements (may push GC roots) *)
      let init_exprs = List.rev (List.tl (List.rev exprs)) in
      let stmts = List.concat_map (convert_expr_as_stmt ctx) init_exprs in
      (* Convert last expression as value *)
      let last_haxe_expr = List.hd (List.rev exprs) in
      let last_expr = convert_expr ctx last_haxe_expr in
      (* Calculate GC roots to pop *)
      let to_pop = gc_roots_to_pop ctx saved_gc_count in
      (* Check if block ends with return (return handles its own cleanup) *)
      let block_returns = ends_with_return last_haxe_expr in
      (* Add GC pop statement if needed *)
      let final_stmts = 
        if to_pop > 0 && not block_returns then
          stmts @ (gc_pop_roots ctx to_pop)
        else begin
          (* Restore count even if we don't emit pop *)
          ctx.gc_local_count <- saved_gc_count;
          stmts
        end
      in
      mk_expr_pos (TCEBlock (final_stmts, Some last_expr)) result_tc pos

(* ============================================================================
 * Array Literal Conversion
 * ============================================================================ *)

and convert_array_literal ctx items result_tc pos =
  let arr_kind = match result_tc with
    | TCFibArray k -> k
    | _ -> TCArrGeneric
  in
  
  (* Empty array - just call new() *)
  if items = [] then
    let prefix = array_kind_prefix arr_kind in
    mk_expr_pos (TCECall (TCTFunc (prefix ^ "new"), [])) result_tc pos
  else begin
    (* Non-empty array - use from_values with compound literal *)
    let c_elem_type = array_kind_c_elem_type arr_kind in
    let item_exprs = List.map (fun item ->
      let expr = convert_expr ctx item in
      (* For generic arrays, box each element to FibDynamic *)
      if arr_kind = TCArrGeneric && expr.ctype <> TCFibDynamic then
        mk_expr (TCEBox (expr, box_kind_of_type expr.ctype)) TCFibDynamic
      else
        expr
    ) items in
    mk_expr_pos (TCEArrayFromValues {
      afv_kind = arr_kind;
      afv_c_type = c_elem_type;
      afv_values = item_exprs;
    }) result_tc pos
  end

(* ============================================================================
 * Field Access Conversion
 * ============================================================================ *)

(* Check if expression came from dynamic field access *)
and is_dynamic_field_expr e = match e.Type.eexpr with
  | Type.TField (_, Type.FAnon _) | Type.TField (_, Type.FDynamic _) -> true
  | _ -> false

and convert_field_access ctx obj fa result_tc pos =
  let obj_expr = convert_expr ctx obj in
  match fa with
  (* Static field *)
  | FStatic (c, cf) ->
      let class_name = flat_path c.cl_path in
      mk_expr_pos (TCEStatic (class_name, ident cf.cf_name)) result_tc pos
  
  (* Instance field - special cases for Array.length and String.length *)
  | FInstance (c, _, cf) ->
      (* Array.length -> fib_*_array_length() *)
      if FiberusBuiltins.is_array_type obj.Type.etype && cf.cf_name = "length" then begin
        let arr_kind = get_array_kind obj.Type.etype in
        (* If object came from dynamic field, need to convert from FibDynamic first *)
        let arr_expr = 
          if is_dynamic_field_expr obj then
            mk_expr (TCECall (TCTFunc "fib_dynamic_to_array", [obj_expr])) (TCFibArray TCArrGeneric)
          else
            obj_expr
        in
        mk_expr_pos (TCEArrayLength (arr_expr, arr_kind)) TCInt32 pos
      end
      (* String.length -> fib_string_length() *)
      else if FiberusBuiltins.is_string_type obj.Type.etype && cf.cf_name = "length" then begin
        (* If object came from dynamic field, need to convert from FibDynamic first *)
        let str_expr = 
          if is_dynamic_field_expr obj then
            mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [obj_expr])) TCFibString
          else
            obj_expr
        in
        mk_expr_pos (TCEStringLength str_expr) TCInt32 pos
      end
      else begin
        (* Regular instance field access - check for inherited field cast *)
        let needs_cast = match obj.Type.etype with
          | Type.TInst (obj_class, _) -> obj_class.cl_path <> c.cl_path
          | _ -> false
        in
        if needs_cast then begin
          (* Cast to parent class type for inherited field access *)
          let class_name = flat_path c.cl_path in
          let cast_expr = mk_expr (TCECast (TCFibClass class_name, obj_expr)) (TCFibClass class_name) in
          mk_expr_pos (TCEArrow (cast_expr, ident cf.cf_name)) result_tc pos
        end else
          mk_expr_pos (TCEArrow (obj_expr, ident cf.cf_name)) result_tc pos
      end
  
  (* Enum field *)
  | FEnum (e, ef) ->
      let enum_name = flat_path e.e_path in
      mk_expr_pos (TCEEnumConst (enum_name, ident ef.ef_name)) result_tc pos
  
  (* Anonymous/dynamic field access - always returns FibDynamic *)
  | FAnon cf ->
      (* Access via fib_field_get returns FibDynamic, regardless of declared type *)
      let field_name = mk_raw_string cf.cf_name in
      mk_expr_pos (TCECall (TCTFunc "fib_field_get", [obj_expr; field_name])) TCFibDynamic pos
  
  | FDynamic name ->
      let field_name = mk_raw_string name in
      mk_expr_pos (TCECall (TCTFunc "fib_field_get", [obj_expr; field_name])) TCFibDynamic pos
  
  (* Closure field - method as value *)
  | FClosure (_, cf) ->
      (* This creates a closure wrapper around the method *)
      (* For now, emit a TODO - this needs thunk generation *)
      mk_expr_pos (TCERaw (Printf.sprintf "/* TODO: method closure %s */" cf.cf_name)) result_tc pos

(* ============================================================================
 * Array Access Conversion
 * ============================================================================ *)

and convert_array_access ctx arr idx result_tc pos =
  let arr_expr = convert_expr ctx arr in
  let idx_expr = convert_expr ctx idx in
  (* Check if array expression is FibDynamic and needs conversion *)
  let arr_expr = 
    if arr_expr.ctype = TCFibDynamic then
      mk_expr (TCECall (TCTFunc "fib_dynamic_to_array", [arr_expr])) (TCFibArray TCArrGeneric)
    else
      arr_expr
  in
  let arr_kind = match arr_expr.ctype with
    | TCFibArray k -> k
    | _ -> TCArrGeneric
  in
  (* For specialized arrays, direct access returns the element type *)
  if arr_kind <> TCArrGeneric then begin
    let access = {
      arr = arr_expr;
      idx = idx_expr;
      arr_kind = arr_kind;
      elem_type = result_tc;
    } in
    mk_expr_pos (TCEArrayGet access) result_tc pos
  end else begin
    (* Generic array returns FibDynamic - need to unbox based on element type *)
    let access = {
      arr = arr_expr;
      idx = idx_expr;
      arr_kind = TCArrGeneric;
      elem_type = TCFibDynamic;
    } in
    let get_expr = mk_expr_pos (TCEArrayGet access) TCFibDynamic pos in
    (* Unbox based on expected element type using field suffix *)
    let suffix = fib_dynamic_field_suffix result_tc in
    if suffix = "" then
      get_expr
    else
      (* For object types, need cast to extract objectVal from FibDynamic *)
      match result_tc with
      | TCFibClass _ | TCFibObject ->
          let data_field = mk_expr (TCEDot (get_expr, "data")) TCFibDynamic in
          let obj_val = mk_expr (TCEDot (data_field, "objectVal")) TCFibObject in
          mk_expr_pos (TCECast (result_tc, obj_val)) result_tc pos
      | _ ->
          (* For primitives: fib_array_get(...).data.intVal etc *)
          let data_field = mk_expr (TCEDot (get_expr, "data")) TCFibDynamic in
          let field_name = 
            match result_tc with
            | TCInt32 -> "intVal"
            | TCFloat64 -> "floatVal"
            | TCBool -> "boolVal"
            | TCFibString -> "stringVal"
            | _ -> "ptrVal"
          in
          mk_expr_pos (TCEDot (data_field, field_name)) result_tc pos
  end

(* ============================================================================
 * Call Conversion
 * ============================================================================ *)

(* Convert array method call *)
and convert_array_call ctx arr arr_expr args arg_exprs method_name result_tc pos =
  let arr_tc = arr_expr.ctype in
  (* Coerce FibDynamic to array if needed *)
  let arr_expr = 
    if arr_tc = TCFibDynamic then
      mk_expr (TCECall (TCTFunc "fib_dynamic_to_array", [arr_expr])) (TCFibArray TCArrGeneric)
    else arr_expr
  in
  let arr_kind = match arr_expr.ctype with TCFibArray k -> k | _ -> TCArrGeneric in
  let is_specialized = arr_kind <> TCArrGeneric in
  let prefix = array_kind_prefix arr_kind in
  
  (* Helper to get default value for optional int params *)
  let arg_or_default idx default =
    if idx < List.length args then
      let arg = List.nth args idx in
      match arg.Type.eexpr with
      | Type.TConst Type.TNull -> mk_int (Int32.of_int default)
      | _ -> List.nth arg_exprs idx
    else mk_int (Int32.of_int default)
  in
  
  match method_name with
  | "push" ->
      let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      let val_expr = 
        if is_specialized then val_expr
        else mk_expr (TCEBox (val_expr, box_kind_of_type val_expr.ctype)) TCFibDynamic
      in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "push"), [arr_expr; val_expr])) TCInt32 pos
  
  | "pop" ->
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "pop"), [arr_expr])) result_tc pos in
      if is_specialized then call
      else mk_expr_pos (TCEUnbox (call, result_tc)) result_tc pos
  
  | "shift" ->
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "shift"), [arr_expr])) result_tc pos in
      if is_specialized then call
      else mk_expr_pos (TCEUnbox (call, result_tc)) result_tc pos
  
  | "unshift" ->
      let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "unshift"), [arr_expr; val_expr])) TCVoid pos
  
  | "insert" ->
      let idx_expr = if List.length arg_exprs > 0 then List.nth arg_exprs 0 else mk_int 0l in
      let val_expr = if List.length arg_exprs > 1 then List.nth arg_exprs 1 else mk_int 0l in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "insert"), [arr_expr; idx_expr; val_expr])) TCVoid pos
  
  | "remove" ->
      let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "remove"), [arr_expr; val_expr])) TCBool pos
  
  | "indexOf" ->
      let val_expr = if List.length arg_exprs > 0 then List.nth arg_exprs 0 else mk_int 0l in
      let start_expr = arg_or_default 1 0 in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "index_of"), [arr_expr; val_expr; start_expr])) TCInt32 pos
  
  | "contains" ->
      let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "contains"), [arr_expr; val_expr])) TCBool pos
  
  | "reverse" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "reverse"), [arr_expr])) TCVoid pos
  
  | "slice" ->
      let start_expr = arg_or_default 0 0 in
      let end_expr = arg_or_default 1 (-1) in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "slice"), [arr_expr; start_expr; end_expr])) arr_expr.ctype pos
  
  | "concat" ->
      let other_expr = if arg_exprs = [] then arr_expr else List.hd arg_exprs in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "concat"), [arr_expr; other_expr])) arr_expr.ctype pos
  
  | "join" ->
      let sep_expr = 
        if arg_exprs = [] then mk_expr (TCEString ",") TCFibString 
        else List.hd arg_exprs 
      in
      mk_expr_pos (TCECall (TCTFunc "fib_array_join", [arr_expr; sep_expr])) TCFibString pos
  
  | "iterator" ->
      mk_expr_pos (TCECall (TCTFunc "fib_array_iterator", [arr_expr])) result_tc pos
  
  | _ ->
      (* Fallback to generic Array_method call *)
      mk_expr_pos (TCECall (TCTMethod ("Array", ident method_name), arr_expr :: arg_exprs)) result_tc pos

(* Convert string method call *)
and convert_string_call ctx str_expr args arg_exprs method_name result_tc pos =
  (* Coerce FibDynamic to string if needed *)
  let str_expr = 
    if str_expr.ctype = TCFibDynamic then
      mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [str_expr])) TCFibString
    else str_expr
  in
  
  (* Check if expression is null *)
  let is_null_expr e = match e.cexpr with
    | TCENull -> true
    | TCECall (TCTFunc "fib_dynamic_null", []) -> true
    | _ -> false
  in
  (* Helper to get arg or default (use default if arg is null or missing) *)
  let arg_or_int_default idx default =
    if idx < List.length arg_exprs then
      let arg = List.nth arg_exprs idx in
      if is_null_expr arg then mk_int (Int32.of_int default) else arg
    else mk_int (Int32.of_int default)
  in
  let arg_or_string_default idx default =
    if idx < List.length arg_exprs then
      let arg = List.nth arg_exprs idx in
      if is_null_expr arg then mk_expr (TCEString default) TCFibString else arg
    else mk_expr (TCEString default) TCFibString
  in
  
  match method_name with
  | "charAt" ->
      let idx_expr = arg_or_int_default 0 0 in
      mk_expr_pos (TCECall (TCTFunc "fib_string_char_at_str", [str_expr; idx_expr])) TCFibString pos
  
  | "charCodeAt" ->
      let idx_expr = arg_or_int_default 0 0 in
      mk_expr_pos (TCECall (TCTFunc "fib_string_char_code_at", [str_expr; idx_expr])) TCInt32 pos
  
  | "substring" | "substr" ->
      let start_expr = arg_or_int_default 0 0 in
      let len_expr = arg_or_int_default 1 (-1) in
      mk_expr_pos (TCECall (TCTFunc "fib_string_substr", [str_expr; start_expr; len_expr])) TCFibString pos
  
  | "indexOf" ->
      let needle_expr = arg_or_string_default 0 "" in
      let start_expr = arg_or_int_default 1 0 in
      mk_expr_pos (TCECall (TCTFunc "fib_string_index_of", [str_expr; needle_expr; start_expr])) TCInt32 pos
  
  | "lastIndexOf" ->
      let needle_expr = arg_or_string_default 0 "" in
      let start_expr = arg_or_int_default 1 (-1) in
      mk_expr_pos (TCECall (TCTFunc "fib_string_last_index_of", [str_expr; needle_expr; start_expr])) TCInt32 pos
  
  | "split" ->
      let delim_expr = arg_or_string_default 0 "" in
      mk_expr_pos (TCECall (TCTFunc "fib_string_split", [str_expr; delim_expr])) (TCFibArray TCArrGeneric) pos
  
  | "toUpperCase" ->
      mk_expr_pos (TCECall (TCTFunc "fib_string_to_upper", [str_expr])) TCFibString pos
  
  | "toLowerCase" ->
      mk_expr_pos (TCECall (TCTFunc "fib_string_to_lower", [str_expr])) TCFibString pos
  
  | "trim" ->
      mk_expr_pos (TCECall (TCTFunc "fib_string_trim", [str_expr])) TCFibString pos
  
  | "length" ->
      mk_expr_pos (TCEStringLength str_expr) TCInt32 pos
  
  | _ ->
      (* Fallback to generic String_method call *)
      mk_expr_pos (TCECall (TCTMethod ("String", ident method_name), str_expr :: arg_exprs)) result_tc pos

(* Convert map method call *)
and convert_map_call ctx map_expr args arg_exprs kind method_name value_type result_tc pos =
  let prefix = FiberusBuiltins.map_kind_prefix kind in
  
  (* ObjectMap needs key cast to FibObject* *)
  let cast_key key_expr =
    if kind = FiberusBuiltins.MapObject then
      mk_expr (TCECast (TCFibObject, key_expr)) TCFibObject
    else key_expr
  in
  
  (* Get value suffix for typed set operations *)
  let value_suffix val_tc =
    match val_tc with
    | TCInt32 -> "_int"
    | TCFloat64 -> "_float"
    | TCFibString -> "_string"
    | TCInt64 -> "_int64"
    | _ -> "_dynamic"
  in
  
  (* Get typed getter function name *)
  let get_func_name () =
    match value_type with
    | TCInt32 -> prefix ^ "get_int"
    | TCFloat64 -> prefix ^ "get_float"
    | TCFibString -> prefix ^ "get_string"
    | TCInt64 -> prefix ^ "get_int64"
    | _ -> prefix ^ "get_dynamic"
  in
  
  match method_name with
  | "set" ->
      let key_expr = if List.length arg_exprs > 0 then cast_key (List.nth arg_exprs 0) else mk_int 0l in
      let val_expr = if List.length arg_exprs > 1 then List.nth arg_exprs 1 else mk_int 0l in
      let suffix = value_suffix val_expr.ctype in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "set" ^ suffix), [map_expr; key_expr; val_expr])) TCVoid pos
  
  | "get" ->
      let key_expr = if List.length arg_exprs > 0 then cast_key (List.nth arg_exprs 0) else mk_int 0l in
      let func_name = get_func_name () in
      (* Use actual value_type as return type since typed getter returns concrete type *)
      mk_expr_pos (TCECall (TCTFunc func_name, [map_expr; key_expr])) value_type pos
  
  | "exists" ->
      let key_expr = if List.length arg_exprs > 0 then cast_key (List.nth arg_exprs 0) else mk_int 0l in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "exists"), [map_expr; key_expr])) TCBool pos
  
  | "remove" ->
      let key_expr = if List.length arg_exprs > 0 then cast_key (List.nth arg_exprs 0) else mk_int 0l in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "remove"), [map_expr; key_expr])) TCBool pos
  
  | "keys" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "keys"), [map_expr])) result_tc pos
  
  | "iterator" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "iterator"), [map_expr])) result_tc pos
  
  | "copy" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "copy"), [map_expr])) result_tc pos
  
  | "toString" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "to_string"), [map_expr])) TCFibString pos
  
  | "clear" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "clear"), [map_expr])) TCVoid pos
  
  | "size" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "size"), [map_expr])) TCInt32 pos
  
  | _ ->
      (* Fallback *)
      let map_name = match kind with
        | FiberusBuiltins.MapInt -> "IntMap"
        | FiberusBuiltins.MapString -> "StringMap"
        | FiberusBuiltins.MapInt64 -> "Int64Map"
        | FiberusBuiltins.MapObject -> "ObjectMap"
      in
      mk_expr_pos (TCECall (TCTMethod (map_name, ident method_name), map_expr :: arg_exprs)) result_tc pos

(* Get map value type from type parameters *)
and get_map_value_type map_type kind =
  match Type.follow map_type with
  | Type.TInst (_, [_; t]) when kind = FiberusBuiltins.MapObject -> tc_type_of (Type.follow t)
  | Type.TInst (_, [t]) -> tc_type_of (Type.follow t)
  | _ -> TCFibDynamic

and convert_call ctx callee args result_tc pos =
  let arg_exprs = List.map (convert_expr ctx) args in
  
  (* Check for builtin intrinsics first *)
  match FiberusBuiltins.get_intrinsic callee with
  | Some FiberusBuiltins.IExceptionStack ->
      mk_expr_pos (TCECall (TCTFunc "fib_get_exception_stack_array", [])) result_tc pos
  
  | Some FiberusBuiltins.ICallStack ->
      mk_expr_pos (TCECall (TCTFunc "fib_get_call_stack_array", [])) result_tc pos
  
  | Some FiberusBuiltins.IStdInt ->
      let arg = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      mk_expr_pos (TCECast (TCInt32, arg)) TCInt32 pos
  
  | Some FiberusBuiltins.IStdString ->
      let arg = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      (match arg.ctype with
       | TCFibString -> arg
       | TCInt32 -> mk_expr_pos (TCECall (TCTFunc "fib_string_from_int", [arg])) TCFibString pos
       | TCFloat64 | TCFloat32 -> mk_expr_pos (TCECall (TCTFunc "fib_string_from_float", [arg])) TCFibString pos
       | TCInt64 -> mk_expr_pos (TCECall (TCTFunc "fib_string_from_int64", [arg])) TCFibString pos
       | TCBool -> mk_expr_pos (TCETernary (arg, mk_expr (TCEString "true") TCFibString, mk_expr (TCEString "false") TCFibString)) TCFibString pos
       | _ -> mk_expr_pos (TCECall (TCTFunc "fib_dynamic_to_string", [arg])) TCFibString pos)
  
  | Some FiberusBuiltins.IStdIsOfType ->
      (* Std.isOfType(value, Type) - check type at runtime *)
      (match args with
       | [_; type_arg] ->
           let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
           (match type_arg.Type.eexpr with
            | Type.TTypeExpr (Type.TClassDecl c) ->
                (match c.cl_path with
                 | ([], "String") -> mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_string", [val_expr])) TCBool pos
                 | ([], "Array") -> mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_array", [val_expr])) TCBool pos
                 | ([], ("Int" | "Float" | "Bool")) -> mk_expr_pos (TCEBool false) TCBool pos
                 | _ when not (has_class_flag c CExtern) ->
                     let target_class = flat_path c.cl_path in
                     let cast_obj = mk_expr (TCECast (TCFibObject, val_expr)) TCFibObject in
                     mk_expr_pos (TCECall (TCTFunc "fib_object_instanceof", [cast_obj; mk_expr (TCELocal (target_class ^ "_class")) (TCPointer TCVoid)])) TCBool pos
                 | _ -> mk_expr_pos (TCEBool false) TCBool pos)
            | _ -> mk_expr_pos (TCEBool false) TCBool pos)
       | _ -> mk_expr_pos (TCEBool false) TCBool pos)
  
  (* Fiber.spawn/spawnOn/spawnAny are handled in gen_call due to closure complexity *)
  | Some (FiberusBuiltins.IFiberSpawn | FiberusBuiltins.IFiberSpawnOn | FiberusBuiltins.IFiberSpawnAny) ->
      (* Fallback - let gen_call handle these *)
      mk_expr_pos (TCERaw "/* Fiber spawn handled by gen_call */") result_tc pos
  
  (* trace() is handled in gen_call due to gen_trace_value complexity *)
  | Some FiberusBuiltins.ITrace ->
      mk_expr_pos (TCERaw "/* trace handled by gen_call */") result_tc pos
  
  (* __fiberus__() raw code emission - concatenate string literals with converted expressions *)
  | Some FiberusBuiltins.IFiberus ->
      (* Build raw C code by iterating through arguments:
         - String constants are emitted directly
         - Other expressions are converted to C-AST and serialized *)
      let buf = Buffer.create 64 in
      List.iter (fun arg ->
        match arg.Type.eexpr with
        | Type.TConst (Type.TString s) -> Buffer.add_string buf s
        | _ ->
            (* Convert expression to C-AST and serialize via SourceWriter *)
            let arg_expr = convert_expr ctx arg in
            let w = FiberusSourceWriter.create () in
            FiberusSourceWriter.write_expr w arg_expr;
            Buffer.add_string buf (FiberusSourceWriter.contents w)
      ) args;
      mk_expr_pos (TCERaw (Buffer.contents buf)) result_tc pos
  
  | None ->
  
  (* Helper to coerce argument to expected parameter type *)
  let coerce_arg arg_expr param_tc =
    (* Special handling for null - convert to appropriate default for primitives *)
    let is_null_expr = match arg_expr.cexpr with TCENull -> true | _ -> false in
    let is_dynamic_null = 
      match arg_expr.cexpr with 
      | TCECall (TCTFunc "fib_dynamic_null", []) -> true 
      | _ -> false 
    in
    if (is_null_expr || is_dynamic_null) && param_tc <> TCFibDynamic then
      (* Null being passed to non-Dynamic parameter - use appropriate default *)
      match param_tc with
      | TCInt32 | TCInt8 | TCInt16 | TCUInt8 | TCUInt16 | TCUInt32 -> mk_int 0l
      | TCInt64 | TCUInt64 -> mk_expr (TCEInt64 0L) param_tc
      | TCFloat32 | TCFloat64 -> mk_expr (TCEFloat "0.0") param_tc
      | TCBool -> mk_expr (TCEBool false) TCBool
      | _ -> mk_expr TCENull param_tc  (* Pointer types can use NULL *)
    else if arg_expr.ctype = param_tc then arg_expr
    else if param_tc = TCFibDynamic && arg_expr.ctype <> TCFibDynamic then
      (* Box to FibDynamic *)
      mk_expr (TCEBox (arg_expr, box_kind_of_type arg_expr.ctype)) TCFibDynamic
    else if arg_expr.ctype = TCFibDynamic && param_tc <> TCFibDynamic then
      (* Unbox from FibDynamic - except for null which should use default *)
      mk_expr (TCEUnbox (arg_expr, param_tc)) param_tc
    else
      arg_expr
  in
  
  (* Get parameter types from function type *)
  let get_param_tc_types func_type =
    match Type.follow func_type with
    | Type.TFun (params, _) -> List.map (fun (_, _, t) -> tc_type_of t) params
    | _ -> []
  in
  
  (* Coerce all arguments to match parameter types *)
  let coerce_args arg_exprs param_types =
    let rec coerce acc args params =
      match args, params with
      | [], _ -> List.rev acc
      | arg :: rest_args, param :: rest_params -> 
          coerce (coerce_arg arg param :: acc) rest_args rest_params
      | arg :: rest_args, [] ->
          (* More args than params - pass as-is *)
          coerce (arg :: acc) rest_args []
    in
    coerce [] arg_exprs param_types
  in
  
  match callee.eexpr with
  (* Static method call *)
  | TField (_, FStatic (c, cf)) ->
      let class_name = flat_path c.cl_path in
      let method_name = ident cf.cf_name in
      let param_types = get_param_tc_types cf.cf_type in
      let coerced_args = coerce_args arg_exprs param_types in
      mk_expr_pos (TCECall (TCTMethod (class_name, method_name), coerced_args)) result_tc pos
  
  (* Array method call *)
  | TField (arr, FInstance (_, _, cf)) when FiberusBuiltins.is_array_type arr.Type.etype ->
      let arr_expr = convert_expr ctx arr in
      convert_array_call ctx arr arr_expr args arg_exprs cf.cf_name result_tc pos
  
  (* String method call *)
  | TField (str, FInstance (_, _, cf)) when FiberusBuiltins.is_string_type str.Type.etype ->
      let str_expr = convert_expr ctx str in
      convert_string_call ctx str_expr args arg_exprs cf.cf_name result_tc pos
  
  (* Map method call (IntMap, StringMap, Int64Map, ObjectMap) *)
  | TField (map, FInstance (_, _, cf)) when FiberusBuiltins.map_kind_of_type map.Type.etype <> None ->
      let map_expr = convert_expr ctx map in
      let kind = match FiberusBuiltins.map_kind_of_type map.Type.etype with Some k -> k | None -> FiberusBuiltins.MapInt in
      let value_type = get_map_value_type map.Type.etype kind in
      convert_map_call ctx map_expr args arg_exprs kind cf.cf_name value_type result_tc pos
  
  (* Instance method call *)
  | TField (obj, FInstance (c, _, cf)) ->
      let obj_expr = convert_expr ctx obj in
      let class_name = flat_path c.cl_path in
      let method_name = ident cf.cf_name in
      let param_types = get_param_tc_types cf.cf_type in
      let coerced_args = coerce_args arg_exprs param_types in
      let is_interface_call = FiberusVtable.is_interface c in
      (* Check if this needs vtable dispatch *)
      (match ctx.vtable_ctx with
      | Some vtctx ->
          if is_interface_call then begin
            (* Interface calls ALWAYS need vtable dispatch *)
            match FiberusVtable.get_interface_slot vtctx c cf with
            | Some slot ->
                (* Interface calls use FibObject as this type since we don't know concrete class *)
                mk_expr_pos (TCEVtableCall {
                  obj = obj_expr;
                  slot = slot;
                  this_type = TCFibObject;
                  ret_type = result_tc;
                  args = coerced_args;
                }) result_tc pos
            | None ->
                mk_expr_pos (TCERaw (Printf.sprintf "/* ERROR: Interface method %s has no vtable slot */" cf.cf_name)) result_tc pos
          end else begin
            match FiberusVtable.get_vtable_slot vtctx c cf with
            | Some slot_info ->
                (* Virtual dispatch through vtable *)
                mk_expr_pos (TCEVtableCall {
                  obj = obj_expr;
                  slot = slot_info.FiberusVtable.slot_index;
                  this_type = TCFibClass class_name;
                  ret_type = result_tc;
                  args = coerced_args;
                }) result_tc pos
            | None ->
                (* Direct call *)
                mk_expr_pos (TCECall (TCTMethod (class_name, method_name), obj_expr :: coerced_args)) result_tc pos
          end
      | None ->
          (* No vtable context - direct call *)
          mk_expr_pos (TCECall (TCTMethod (class_name, method_name), obj_expr :: coerced_args)) result_tc pos)
  
  (* Constructor call - TNew handles this, but might appear as call too *)
  | TField (_, FEnum (e, ef)) ->
      let enum_name = flat_path e.e_path in
      let constr_name = ident ef.ef_name in
      mk_expr_pos (TCEEnumConstruct (enum_name, constr_name, arg_exprs)) (TCFibEnum enum_name) pos
  
  (* Dynamic/anonymous field call *)
  | TField (obj, FAnon cf) ->
      let obj_expr = convert_expr ctx obj in
      let field_name = mk_raw_string cf.cf_name in
      (* Get closure from dynamic field, then call it *)
      let closure = mk_expr (TCECall (TCTFunc "fib_dynamic_get_field", [obj_expr; field_name])) TCFibClosure in
      mk_expr_pos (TCEDynamicCall { closure; args = arg_exprs }) result_tc pos
  
  | TField (obj, FDynamic name) ->
      let obj_expr = convert_expr ctx obj in
      let field_name = mk_raw_string name in
      let closure = mk_expr (TCECall (TCTFunc "fib_dynamic_get_field", [obj_expr; field_name])) TCFibClosure in
      mk_expr_pos (TCEDynamicCall { closure; args = arg_exprs }) result_tc pos
  
  (* Super constructor call: super(args) -> ParentClass_init(this, args) *)
  | TConst TSuper ->
      (match ctx.current_class with
      | Some c ->
          (match c.cl_super with
          | Some (parent_c, _) ->
              let parent_name = flat_path parent_c.cl_path in
              (* Get parent constructor parameter types *)
              let param_types = match parent_c.cl_constructor with
                | Some cf -> get_param_tc_types cf.cf_type
                | None -> []
              in
              let coerced_args = coerce_args arg_exprs param_types in
              (* Cast this to parent type *)
              let parent_this = mk_expr (TCECast (TCPointer (TCFibClass parent_name), mk_expr TCEThis (TCPointer TCVoid))) (TCPointer (TCFibClass parent_name)) in
              mk_expr_pos (TCECall (TCTMethod (parent_name, "init"), parent_this :: coerced_args)) TCVoid pos
          | None ->
              mk_expr_pos (TCERaw "/* super() with no parent class */") TCVoid pos)
      | None ->
          mk_expr_pos (TCERaw "/* super() outside of class context */") TCVoid pos)
  
  (* Closure call - callee is already a closure value *)
  | _ ->
      let callee_expr = convert_expr ctx callee in
      (match callee_expr.ctype with
      | TCFibClosure ->
          (* Get arg types from the function type *)
          let arg_types = List.map (fun e -> e.ctype) arg_exprs in
          mk_expr_pos (TCEClosureCall {
            closure = callee_expr;
            arg_types = arg_types;
            ret_type = result_tc;
            args = arg_exprs;
          }) result_tc pos
      | _ ->
          (* Unknown callable - use dynamic call *)
          mk_expr_pos (TCEDynamicCall { closure = callee_expr; args = arg_exprs }) result_tc pos)

(* ============================================================================
 * Statement Conversion
 * ============================================================================ *)

let rec convert_stmt (ctx : conv_ctx) (e : texpr) : tc_stmt list =
  match e.eexpr with
  (* Variable declaration *)
  | TVar (v, init_opt) ->
      let name = ident v.v_name in
      let vtype = tc_type_of v.v_type in
      let init = Option.map (convert_expr ctx) init_opt in
      let var_stmt = TCSVar { vd_name = name; vd_type = vtype; vd_init = init; vd_static = false; vd_const = false } in
      (* Add GC push for pointer types *)
      let gc_stmts = gc_push_if_needed ctx name vtype in
      var_stmt :: gc_stmts
  
  (* Block of statements *)
  | TBlock exprs ->
      [TCSBlock (List.concat_map (convert_stmt ctx) exprs)]
  
  (* If statement *)
  | TIf (cond, ethen, eelse_opt) ->
      let cond_expr = convert_expr ctx cond in
      let then_stmts = convert_stmt ctx ethen in
      let else_stmts = Option.map (convert_stmt ctx) eelse_opt in
      [TCSIf (cond_expr, then_stmts, else_stmts)]
  
  (* While loop *)
  | TWhile (cond, body, flag) ->
      let cond_expr = convert_expr ctx cond in
      let body_stmts = convert_stmt ctx body in
      let is_do_while = (flag = DoWhile) in
      [TCSWhile (cond_expr, body_stmts, is_do_while)]
  
  (* Return statement *)
  | TReturn expr_opt ->
      let ret_expr = Option.map (convert_expr ctx) expr_opt in
      [TCSReturn ret_expr]
  
  (* Break *)
  | TBreak ->
      [TCSBreak]
  
  (* Continue *)
  | TContinue ->
      [TCSContinue]
  
  (* Throw *)
  | TThrow e ->
      let exc_expr = convert_expr ctx e in
      (* Box to FibDynamic if not already *)
      let boxed_expr = 
        if exc_expr.ctype = TCFibDynamic then exc_expr
        else mk_expr (TCEBox (exc_expr, box_kind_of_type exc_expr.ctype)) TCFibDynamic
      in
      [TCSThrow boxed_expr]
  
  (* Try/catch *)
  | TTry (body, catches) ->
      let body_stmts = convert_stmt ctx body in
      let catch_blocks = List.map (fun (v, catch_body) ->
        {
          catch_var = ident v.v_name;
          catch_type = tc_type_of v.v_type;
          catch_body = convert_stmt ctx catch_body;
        }
      ) catches in
      [TCSTry { try_body = body_stmts; try_catches = catch_blocks }]
  
  (* Switch *)
  | TSwitch sw ->
      let cond_expr = convert_expr ctx sw.switch_subject in
      let case_blocks = List.map (fun case ->
        let value_exprs = List.map (convert_expr ctx) case.case_patterns in
        let body_stmts = convert_stmt ctx case.case_expr in
        (value_exprs, body_stmts)
      ) sw.switch_cases in
      let default_stmts = Option.map (convert_stmt ctx) sw.switch_default in
      [TCSSwitch { sw_expr = cond_expr; sw_cases = case_blocks; sw_default = default_stmts }]
  
  (* Expression statement *)
  | _ ->
      let expr = convert_expr ctx e in
      [TCSExpr expr]

(* ============================================================================
 * Function Conversion
 * ============================================================================ *)

(* Convert a Haxe function to C-AST function definition *)
let convert_function ctx name func is_static class_name_opt =
  let ret_type = tc_type_of func.tf_type in
  let args = List.map (fun (v, _) ->
    { fa_name = ident v.v_name; fa_type = tc_type_of v.v_type }
  ) func.tf_args in
  (* Add 'this' parameter for instance methods *)
  let args = match class_name_opt with
    | Some class_name when not is_static ->
        { fa_name = "this"; fa_type = TCFibClass class_name } :: args
    | _ -> args
  in
  let body = convert_stmt ctx func.tf_expr in
  {
    fd_name = name;
    fd_ret = ret_type;
    fd_args = args;
    fd_body = body;
    fd_static = false;  (* C static keyword, not Haxe static *)
    fd_inline = false;
    fd_attrs = [];
  }
