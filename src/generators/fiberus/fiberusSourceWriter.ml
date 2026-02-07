(*
 * FiberusSourceWriter - C code emission from C-AST
 *
 * This module converts C-AST (FiberusAst) to actual C source code.
 * It handles:
 * - Type emission
 * - Expression emission
 * - Statement emission
 * - Declaration emission
 * - Proper indentation and formatting
 *)

open FiberusAst
open FiberusTypeUtils

(* ============================================================================
 * Writer State
 * ============================================================================ *)

type writer = {
  buf: Buffer.t;
  mutable indent: int;
  mutable at_line_start: bool;
}

(* Create a new writer *)
let create () : writer = {
  buf = Buffer.create 4096;
  indent = 0;
  at_line_start = true;
}

(* Get the buffer contents *)
let contents (w : writer) : string =
  Buffer.contents w.buf

(* Clear the buffer *)
let clear (w : writer) : unit =
  Buffer.clear w.buf;
  w.indent <- 0;
  w.at_line_start <- true

(* ============================================================================
 * Basic Output Primitives
 * ============================================================================ *)

(* Write indentation if at line start *)
let write_indent (w : writer) : unit =
  if w.at_line_start then begin
    for _ = 1 to w.indent do
      Buffer.add_char w.buf '\t'
    done;
    w.at_line_start <- false
  end

(* Write a string *)
let write (w : writer) (s : string) : unit =
  write_indent w;
  Buffer.add_string w.buf s

(* Write a formatted string *)
let writef (w : writer) fmt =
  Printf.ksprintf (write w) fmt

(* Write a newline *)
let newline (w : writer) : unit =
  Buffer.add_char w.buf '\n';
  w.at_line_start <- true

(* Increase indentation *)
let indent (w : writer) : unit =
  w.indent <- w.indent + 1

(* Decrease indentation *)
let dedent (w : writer) : unit =
  w.indent <- max 0 (w.indent - 1)

(* Write with block (handles { } and indentation) *)
let with_block (w : writer) (f : unit -> unit) : unit =
  write w "{";
  newline w;
  indent w;
  f ();
  dedent w;
  write w "}"

(* ============================================================================
 * Type Emission
 * ============================================================================ *)

(* Write a type *)
let write_type (w : writer) (t : tc_type) : unit =
  write w (tc_type_to_string t)

(* Write a type with a name (for declarations) *)
let write_type_with_name (w : writer) (t : tc_type) (name : string) : unit =
  write w (tc_type_with_name t name)

(* ============================================================================
 * Operator Emission
 * ============================================================================ *)

(* Check if unboxing needs a cast (for object types) *)
let unbox_needs_cast (t : tc_type) : bool =
  match t with
  | TCInt32 | TCInt64 | TCFloat32 | TCFloat64 | TCBool | TCFibString -> false
  | TCFibDynamic -> false
  | _ -> true  (* Object types need cast from FibObject* *)

let binop_to_string = function
  | TCOpAdd -> "+"
  | TCOpSub -> "-"
  | TCOpMul -> "*"
  | TCOpDiv -> "/"
  | TCOpMod -> "%"
  | TCOpEq -> "=="
  | TCOpNeq -> "!="
  | TCOpLt -> "<"
  | TCOpLte -> "<="
  | TCOpGt -> ">"
  | TCOpGte -> ">="
  | TCOpAnd -> "&"
  | TCOpOr -> "|"
  | TCOpXor -> "^"
  | TCOpShl -> "<<"
  | TCOpShr -> ">>"
  | TCOpUShr -> ">>"  (* Note: unsigned shift needs special handling *)
  | TCOpBoolAnd -> "&&"
  | TCOpBoolOr -> "||"

let unop_to_string = function
  | TCUNeg -> "-"
  | TCUNot -> "!"
  | TCUBitNot -> "~"
  | TCUPreInc -> "++"
  | TCUPreDec -> "--"
  | TCUPostInc -> "++"
  | TCUPostDec -> "--"

let is_postfix_unop = function
  | TCUPostInc | TCUPostDec -> true
  | _ -> false

(* ============================================================================
 * Expression Emission
 * ============================================================================ *)

(* Forward declaration for mutual recursion *)
let rec write_expr (w : writer) (e : tc_expr) : unit =
  write_expr_kind w e.cexpr e.ctype

and write_expr_kind (w : writer) (ek : tc_expr_kind) (t : tc_type) : unit =
  match ek with
  (* Literals *)
  | TCEInt i -> writef w "%ld" i
  | TCEInt64 i -> writef w "%LdLL" i
  | TCEFloat s -> write w s
  | TCEString s -> writef w "fib_string_new(\"%s\")" (StringHelper.s_escape s)
  | TCERawString s -> writef w "\"%s\"" (StringHelper.s_escape s)
  | TCEBool b -> write w (if b then "true" else "false")
  | TCENull ->
      (* Null depends on type - enum structs use sentinel, others use NULL *)
      (match t with
       | TCFibEnum name -> writef w "(%s){ .index = -1 }" name
       | TCFibDynamic -> write w "fib_dynamic_null()"
       | _ -> write w "NULL")
  | TCEThis -> write w "this"
  | TCESizeOf typ -> write w "sizeof("; write_type w typ; write w ")"
  
  (* Variables & Fields *)
  | TCELocal name -> write w name
  | TCEStatic (cls, field) -> writef w "%s_%s" cls field
  | TCEField (obj, field) -> write_expr w obj; writef w "->%s" field
  | TCEArrow (obj, field) -> write_expr w obj; writef w "->%s" field
  | TCEDot (obj, field) -> write_expr w obj; writef w ".%s" field
  | TCEDeref e -> write w "(*"; write_expr w e; write w ")"
  | TCEAddrOf e -> write w "(&"; write_expr w e; write w ")"
  | TCEParentField (obj, parent_type, field) ->
      writef w "((%s*)(" parent_type;
      write_expr w obj;
      writef w "))->%s" field
  
  (* Operations *)
  | TCEBinop (op, lhs, rhs) ->
      write w "(";
      write_expr w lhs;
      writef w " %s " (binop_to_string op);
      write_expr w rhs;
      write w ")"
  | TCEUnop (op, e) ->
      if is_postfix_unop op then begin
        write w "(";
        write_expr w e;
        write w (unop_to_string op);
        write w ")"
      end else begin
        write w "(";
        write w (unop_to_string op);
        write_expr w e;
        write w ")"
      end
  | TCEAssign (lhs, rhs) ->
      write w "(";
      write_expr w lhs;
      write w " = ";
      write_expr w rhs;
      write w ")"
  | TCEAssignOp (op, lhs, rhs) ->
      write w "(";
      write_expr w lhs;
      writef w " %s= " (binop_to_string op);
      write_expr w rhs;
      write w ")"
  | TCECast (typ, e) ->
      write w "((";
      write_type w typ;
      write w ")";
      write_expr w e;
      write w ")"
  | TCETernary (cond, then_e, else_e) ->
      write w "(";
      write_expr w cond;
      write w " ? ";
      write_expr w then_e;
      write w " : ";
      write_expr w else_e;
      write w ")"
  | TCEComma exprs ->
      write w "(";
      List.iteri (fun i e ->
        if i > 0 then write w ", ";
        write_expr w e
      ) exprs;
      write w ")"
  
  (* Calls *)
  | TCECall (target, args) ->
      write_call_target w target;
      write w "(";
      List.iteri (fun i arg ->
        if i > 0 then write w ", ";
        write_expr w arg
      ) args;
      write w ")"
  | TCEVtableCall { obj; slot; this_type; ret_type; args } ->
      write w "((";
      write_type w ret_type;
      write w " (*)(";
      write_type w this_type;
      List.iter (fun arg ->
        write w ", ";
        write_type w arg.ctype
      ) args;
      write w "))((FibObject*)(";
      write_expr w obj;
      writef w "))->clazz->vtable[%d])(" slot;
      write w "((";
      write_type w this_type;
      write w ")";
      write_expr w obj;
      write w ")";
      List.iter (fun arg ->
        write w ", ";
        write_expr w arg
      ) args;
      write w ")"
  | TCEClosureCall { closure; arg_types; ret_type; args } ->
      let cast = tc_func_ptr_cast ret_type arg_types in
      writef w "((%s" cast;
      write_expr w closure;
      write w "->fn)(";
      write_expr w closure;
      List.iter (fun arg ->
        write w ", ";
        write_expr w arg
      ) args;
      write w "))"
  | TCEDynamicCall { closure; args } ->
      (* Use helper functions instead of GCC statement expressions *)
      let n = List.length args in
      writef w "_fib_dyn_call_%d(" n;
      write_expr w closure;
      List.iter (fun arg ->
        write w ", ";
        write_expr w arg
      ) args;
      write w ")"
  
  (* Memory *)
  | TCEAlloc (cls, size_opt) ->
      (match size_opt with
      | Some size ->
          writef w "gc_alloc(\"%s\", " cls;
          write_expr w size;
          write w ")"
      | None ->
          writef w "gc_alloc(\"%s\", sizeof(%s))" cls cls)
  | TCEAllocCtx cls ->
      writef w "gc_alloc_ctx(FIB_CTX, \"%s\", sizeof(%s))" cls cls
  | TCEStackAlloc (name, typ) ->
      (* Stack allocation should be lifted to statement level via pending_stmts.
       * This macro provides a fallback.
       * Macro: FIB_STACK_ALLOC(type, name) returns pointer to zeroed stack var *)
      writef w "FIB_STACK_ALLOC(%s, %s)"
        (tc_type_to_string typ) name
  
  (* Arrays *)
  | TCEArrayGet { arr; idx; arr_kind; elem_type = _ } ->
      let prefix = array_kind_prefix arr_kind in
      writef w "%sget(" prefix;
      write_expr w arr;
      write w ", ";
      write_expr w idx;
      write w ")"
  | TCEArraySet ({ arr; idx; arr_kind; elem_type = _ }, value) ->
      let prefix = array_kind_prefix arr_kind in
      writef w "%sset(" prefix;
      write_expr w arr;
      write w ", ";
      write_expr w idx;
      write w ", ";
      write_expr w value;
      write w ")"
  | TCEArrayDecl (elems, _elem_type) ->
      write w "(";
      write_type w t;
      write w "){";
      List.iteri (fun i e ->
        if i > 0 then write w ", ";
        write_expr w e
      ) elems;
      write w "}"
  | TCEArrayLength (arr, arr_kind) ->
      let prefix = array_kind_prefix arr_kind in
      writef w "%slength(" prefix;
      write_expr w arr;
      write w ")"
  | TCEArrayFromValues { afv_kind; afv_c_type; afv_values } ->
      let prefix = array_kind_prefix afv_kind in
      writef w "%sfrom_values((%s[]){" prefix afv_c_type;
      List.iteri (fun i v ->
        if i > 0 then write w ", ";
        write_expr w v
      ) afv_values;
      writef w "}, %d)" (List.length afv_values)
  
  (* Boxing/Unboxing *)
  | TCEBox (e, kind) ->
      let func = box_func_name kind in
      if func = "" then
        write_expr w e  (* Already dynamic *)
      else begin
        writef w "%s(" func;
        (match kind with
        | TCBoxObject | TCBoxClosure ->
            write w "(FibObject*)";
            write_expr w e
        | TCBoxEnum enum_name ->
            write w "&";
            write_expr w e;
            writef w ", sizeof(%s)" enum_name
        | _ ->
            write_expr w e);
        write w ")"
      end
  | TCEUnbox (e, target_type) ->
      let func = unbox_func_name target_type in
      if func = "" then
        write_expr w e  (* Already the right type *)
      else if unbox_is_enum target_type then begin
        (* Enum unboxing with null check: 
           (fib_dynamic_is_null(e) ? (EnumType){ .index = -1 } : (*(EnumType*)fib_dynamic_to_ptr(e))) *)
        let enum_name = match target_type with TCFibEnum n -> n | _ -> "UNKNOWN" in
        writef w "(fib_dynamic_is_null(";
        write_expr w e;
        writef w ") ? (%s){ .index = -1 } : (*(%s*)fib_dynamic_to_ptr(" enum_name enum_name;
        write_expr w e;
        write w ")))"
      end else begin
        if unbox_needs_cast target_type then begin
          write w "(";
          write_type w target_type;
          write w ")"
        end;
        writef w "%s(" func;
        write_expr w e;
        write w ")"
      end
  
  (* Enum operations *)
  | TCEEnumIndex e ->
      write_expr w e;
      write w ".index"
  | TCEEnumParam (e, idx) ->
      write_expr w e;
      writef w ".params[%d]" idx
  | TCEEnumConstruct (enum_name, constr, args) ->
      writef w "%s_%s(" enum_name constr;
      List.iteri (fun i arg ->
        if i > 0 then write w ", ";
        write_expr w arg
      ) args;
      write w ")"
  | TCEEnumConst (enum_name, constr) ->
      writef w "%s_%s" enum_name constr
  
  (* Object operations *)
  | TCENew (cls, args) ->
      writef w "%s_new(" cls;
      List.iteri (fun i arg ->
        if i > 0 then write w ", ";
        write_expr w arg
      ) args;
      write w ")"
  | TCEInstanceOf (e, cls) ->
      writef w "fib_is_instance(";
      write_expr w e;
      writef w ", &%s_class)" cls
  | TCEAnonObject fields ->
      (* Use numbered helper macro to create anonymous object.
       * This avoids GCC statement expressions.
       * Macro: FIB_ANON_NEW_N("name1", val1, "name2", val2, ...) *)
      let n = List.length fields in
      if n = 0 then
        write w "FIB_ANON_NEW_0()"
      else begin
        writef w "FIB_ANON_NEW_%d(" n;
        let first = ref true in
        List.iter (fun (name, value) ->
          if not !first then write w ", ";
          first := false;
          writef w "\"%s\", " name;
          write_expr w value
        ) fields;
        write w ")"
      end
  
  (* String operations *)
  | TCEStringConcat (lhs, rhs) ->
      write w "fib_string_concat(";
      write_expr w lhs;
      write w ", ";
      write_expr w rhs;
      write w ")"
  | TCEStringEq (lhs, rhs) ->
      write w "fib_string_eq(";
      write_expr w lhs;
      write w ", ";
      write_expr w rhs;
      write w ")"
  | TCEStringLength str ->
      write w "fib_string_length(";
      write_expr w str;
      write w ")"
  
  (* Compound expressions - TCEBlock should now be rare; we use pending_stmts instead.
   * If we still encounter a block, emit it as standard C (not GCC extension).
   * This can only work if the block is in statement context. *)
  | TCEBlock (stmts, result) ->
      (* DEPRECATED: TCEBlock as expression should be avoided.
       * The new model uses pending_stmts on expressions instead.
       * This is here for backwards compatibility only. *)
      (match result with
      | Some e when stmts = [] ->
          (* Just the result expression *)
          write_expr w e
      | Some e ->
          (* Block with result - emit as comma expression if simple, else error *)
          write w "(";
          List.iter (fun s ->
            (* Can only handle TCSExpr as comma operands *)
            match s with
            | TCSExpr stmt_e -> 
                write_expr w stmt_e;
                write w ", "
            | _ -> 
                (* Complex statement in expression block - emit placeholder *)
                write w "/* complex stmt in block expr */ 0, "
          ) stmts;
          write_expr w e;
          write w ")"
      | None ->
          (* Block without result - shouldn't be in expression context *)
          write w "/* void block in expr context */ ((void)0)")
  
  (* Closure creation - emitted as a simple call when no captures, 
   * or with comma operator for captures (avoiding GCC statement expressions).
   * Complex closures should be lifted to statement level via pending_stmts. *)
  | TCEClosureCreate cc ->
      if cc.cc_captures = [] then begin
        (* No captures - simple call *)
        if cc.cc_for_fiber then
          write w "fib_closure_create_for_fiber"
        else
          write w "fib_closure_create";
        writef w "((void*)%s, (void*)%s, 0, %d)" 
          cc.cc_impl_name cc.cc_name cc.cc_arg_count
      end else begin
        (* With captures - this should ideally be in pending_stmts.
         * For now, emit a helper macro call that handles the creation.
         * The macro is: FIB_CLOSURE_CREATE(impl, thunk, n_caps, n_args, cap0, cap1, ...) *)
        if cc.cc_for_fiber then
          write w "FIB_CLOSURE_CREATE_FOR_FIBER("
        else
          write w "FIB_CLOSURE_CREATE(";
        writef w "(void*)%s, (void*)%s, %d, %d" 
          cc.cc_impl_name cc.cc_name (List.length cc.cc_captures) cc.cc_arg_count;
        (* Emit capture values *)
        List.iter (fun (var_name, var_type) ->
          write w ", ";
          (* Box the captured value appropriately *)
          match var_type with
          | TCInt32 -> writef w "fib_dynamic_int(%s)" var_name
          | TCInt64 -> writef w "fib_dynamic_int64(%s)" var_name
          | TCFloat64 -> writef w "fib_dynamic_float(%s)" var_name
          | TCBool -> writef w "fib_dynamic_bool(%s)" var_name
          | TCFibString -> writef w "fib_dynamic_string(%s)" var_name
          | _ -> writef w "(FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=%s}" var_name
        ) cc.cc_captures;
        write w ")"
      end
  
  | TCERaw s ->
      write w s

and write_call_target (w : writer) (target : tc_call_target) : unit =
  match target with
  | TCTFunc name -> write w name
  | TCTFuncPtr e -> write w "(*"; write_expr w e; write w ")"
  | TCTMethod (cls, method_name) -> writef w "%s_%s" cls method_name
  | TCTMacro name -> write w name

(* ============================================================================
 * Statement Emission
 * ============================================================================ *)

(* Emit any pending statements from an expression.
 * This handles the lifting of sub-expressions to statement level. *)
and emit_pending_stmts (w : writer) (e : tc_expr) : unit =
  List.iter (write_stmt w) e.pending_stmts

and write_stmt (w : writer) (s : tc_stmt) : unit =
  match s with
  | TCSExpr e ->
      (* Emit pending statements first (lifted from sub-expressions) *)
      emit_pending_stmts w e;
      write_expr w e;
      write w ";";
      newline w
  | TCSVar vd ->
      (* Emit pending statements from initializer first *)
      (match vd.vd_init with
      | Some init_e -> emit_pending_stmts w init_e
      | None -> ());
      write_var_decl w vd;
      write w ";";
      newline w
  | TCSBlock stmts ->
      with_block w (fun () ->
        List.iter (write_stmt w) stmts
      );
      newline w
  | TCSEmpty ->
      write w ";";
      newline w
  
  (* Control flow *)
  | TCSIf (cond, then_stmts, else_stmts) ->
      (* Emit pending statements from condition first *)
      emit_pending_stmts w cond;
      write w "if (";
      write_expr w cond;
      write w ") ";
      with_block w (fun () ->
        List.iter (write_stmt w) then_stmts
      );
      (match else_stmts with
      | Some stmts when stmts <> [] ->
          write w " else ";
          with_block w (fun () ->
            List.iter (write_stmt w) stmts
          )
      | _ -> ());
      newline w
  | TCSWhile (cond, body, is_do_while) ->
      if is_do_while then begin
        write w "do ";
        with_block w (fun () ->
          List.iter (write_stmt w) body
        );
        (* Emit pending statements from condition - rare but possible *)
        emit_pending_stmts w cond;
        write w " while (";
        write_expr w cond;
        write w ");";
        newline w
      end else begin
        (* Emit pending statements from condition - rare but possible *)
        emit_pending_stmts w cond;
        write w "while (";
        write_expr w cond;
        write w ") ";
        with_block w (fun () ->
          List.iter (write_stmt w) body
        );
        newline w
      end
  | TCSFor (init, cond, incr, body) ->
      write w "for (";
      (match init with
      | TCForVar vd -> write_var_decl w vd
      | TCForExpr (Some e) -> write_expr w e
      | TCForExpr None -> ());
      write w "; ";
      (match cond with Some e -> write_expr w e | None -> ());
      write w "; ";
      (match incr with Some e -> write_expr w e | None -> ());
      write w ") ";
      with_block w (fun () ->
        List.iter (write_stmt w) body
      );
      newline w
  | TCSSwitch sw ->
      (* Emit pending statements from switch expression *)
      emit_pending_stmts w sw.sw_expr;
      write w "switch (";
      write_expr w sw.sw_expr;
      write w ") ";
      with_block w (fun () ->
        List.iter (fun (values, stmts) ->
          List.iter (fun v ->
            write w "case ";
            write_expr w v;
            write w ":";
            newline w
          ) values;
          indent w;
          List.iter (write_stmt w) stmts;
          write w "break;";
          newline w;
          dedent w
        ) sw.sw_cases;
        (match sw.sw_default with
        | Some stmts ->
            write w "default:";
            newline w;
            indent w;
            List.iter (write_stmt w) stmts;
            dedent w
        | None -> ())
      );
      newline w
  | TCSReturn (Some e) ->
      (* Emit pending statements first (lifted from sub-expressions) *)
      emit_pending_stmts w e;
      write w "return ";
      write_expr w e;
      write w ";";
      newline w
  | TCSReturn None ->
      write w "return;";
      newline w
  | TCSBreak ->
      write w "break;";
      newline w
  | TCSContinue ->
      write w "continue;";
      newline w
  | TCSGoto label ->
      writef w "goto %s;" label;
      newline w
  | TCSLabel label ->
      dedent w;
      writef w "%s:" label;
      newline w;
      indent w
  
  (* Exception handling *)
  | TCSTry tr ->
      write w "FIB_TRY ";
      with_block w (fun () ->
        List.iter (write_stmt w) tr.try_body
      );
      List.iter (fun catch ->
        writef w " FIB_CATCH(%s, " catch.catch_var;
        write_type w catch.catch_type;
        write w ") ";
        with_block w (fun () ->
          List.iter (write_stmt w) catch.catch_body
        )
      ) tr.try_catches;
      write w " FIB_END_TRY";
      newline w
  | TCSThrow e ->
      (* Emit pending statements from thrown expression *)
      emit_pending_stmts w e;
      (* Exception throw: begin unwinding, then throw boxed FibDynamic *)
      write w "fib_exception_begin(); fib_throw(";
      write_expr w e;
      write w ")";
      newline w
  
  (* GC integration *)
  | TCSGCPush e ->
      write w "gc_push_temp_root_ctx(FIB_CTX, (void**)&";
      write_expr w e;
      write w ");";
      newline w
  | TCSGCPop n when n > 0 ->
      writef w "gc_pop_temp_roots_ctx(FIB_CTX, %d);" n;
      newline w
  | TCSGCPop _ ->
      () (* n=0, emit nothing *)
  | TCSGCCtx ->
      write w "FIB_GC_CTX;";
      newline w
  | TCSGCSafePoint ->
      write w "GC_SAFE_POINT();";
      newline w
  | TCSGCRootCheck expected ->
      (* Debug assertion for GC root count verification.
       * Only emitted under FIBERUS_DEBUG to catch push/pop imbalances.
       * Note: _fib_gc_ctx is FiberGCContext*, uses tempRootCount (not mTempRootCount) *)
      write w "#ifdef FIBERUS_DEBUG";
      newline w;
      writef w "if (_fib_gc_ctx && _fib_gc_ctx->tempRootCount != _gc_base_count + %d) {" expected;
      newline w;
      write w "  fprintf(stderr, \"[GC ROOT MISMATCH] expected %%zu got %%zu\\n\", ";
      writef w "(size_t)(_gc_base_count + %d), (size_t)_fib_gc_ctx->tempRootCount);" expected;
      newline w;
      write w "  __builtin_trap();";
      newline w;
      write w "}";
      newline w;
      write w "#endif";
      newline w
  
  (* Fiber integration *)
  | TCSYieldPoint ->
      write w "FIBER_YIELD_POINT();";
      newline w
  | TCSForceMature inner ->
      write w "gc_force_mature_begin();";
      newline w;
      write_stmt w inner;
      write w "gc_force_mature_end();";
      newline w
  
  (* Debug/profiling *)
  | TCSStackFrame sf ->
      writef w "FIB_LOCAL_STACK_FRAME(_fib_pos_%s_%s, \"%s\", \"%s\", \"%s.%s\", \"%s\", %d);"
        sf.sf_class sf.sf_func sf.sf_class sf.sf_func sf.sf_class sf.sf_func sf.sf_file sf.sf_line;
      newline w;
      writef w "FIB_STACKFRAME(&_fib_pos_%s_%s);" sf.sf_class sf.sf_func;
      newline w
  | TCSLine n ->
      writef w "FIBLINE(%d);" n;
      newline w
  
  (* Raw C *)
  | TCSRaw s ->
      write w s;
      newline w
  | TCSComment s ->
      writef w "/* %s */" s;
      newline w

and write_var_decl (w : writer) (vd : tc_var_decl) : unit =
  if vd.vd_static then write w "static ";
  if vd.vd_const then write w "const ";
  write_type_with_name w vd.vd_type vd.vd_name;
  match vd.vd_init with
  | Some e -> write w " = "; write_expr w e
  | None -> ()

(* ============================================================================
 * Declaration Emission
 * ============================================================================ *)

let write_decl (w : writer) (d : tc_decl) : unit =
  match d with
  | TCDStruct sd ->
      writef w "struct %s " sd.sd_name;
      with_block w (fun () ->
        (match sd.sd_parent with
        | Some parent -> writef w "%s _parent;" parent; newline w
        | None -> ());
        List.iter (fun sf ->
          write_type_with_name w sf.sf_type sf.sf_name;
          write w ";";
          (match sf.sf_comment with
          | Some c -> writef w " /* %s */" c
          | None -> ());
          newline w
        ) sd.sd_fields
      );
      write w ";";
      newline w;
      newline w
  | TCDEnum ed ->
      writef w "typedef struct %s " ed.ed_name;
      with_block w (fun () ->
        write w "int index;";
        newline w;
        if ed.ed_max_params > 0 then begin
          writef w "FibDynamic params[%d];" ed.ed_max_params;
          newline w
        end
      );
      writef w " %s;" ed.ed_name;
      newline w;
      newline w;
      (* Constructor functions *)
      List.iter (fun ec ->
        writef w "static inline %s %s_%s(" ed.ed_name ed.ed_name ec.ec_name;
        List.iteri (fun i (name, typ) ->
          if i > 0 then write w ", ";
          write_type_with_name w typ name
        ) ec.ec_params;
        if ec.ec_params = [] then write w "void";
        write w ") ";
        with_block w (fun () ->
          writef w "%s _e = { .index = %d };" ed.ed_name ec.ec_index;
          newline w;
          List.iteri (fun i (name, _) ->
            writef w "_e.params[%d] = %s;" i name;
            newline w
          ) ec.ec_params;
          write w "return _e;";
          newline w
        );
        newline w;
        newline w
      ) ed.ed_constrs
  | TCDFunc fd ->
      if fd.fd_static then write w "static ";
      if fd.fd_inline then write w "inline ";
      List.iter (fun attr -> writef w "__attribute__((%s)) " attr) fd.fd_attrs;
      write_type w fd.fd_ret;
      writef w " %s(" fd.fd_name;
      List.iteri (fun i arg ->
        if i > 0 then write w ", ";
        write_type_with_name w arg.fa_type arg.fa_name
      ) fd.fd_args;
      if fd.fd_args = [] then write w "void";
      write w ") ";
      with_block w (fun () ->
        List.iter (write_stmt w) fd.fd_body
      );
      newline w;
      newline w
  | TCDVar vd ->
      write_var_decl w vd;
      write w ";";
      newline w
  | TCDTypedef (name, typ) ->
      write w "typedef ";
      write_type_with_name w typ name;
      write w ";";
      newline w
  | TCDForwardStruct name ->
      writef w "struct %s;" name;
      newline w
  | TCDForwardFunc fs ->
      write_type w fs.fs_ret;
      writef w " %s(" fs.fs_name;
      List.iteri (fun i typ ->
        if i > 0 then write w ", ";
        write_type w typ
      ) fs.fs_args;
      write w ");";
      newline w
  | TCDExtern vd ->
      write w "extern ";
      write_var_decl w vd;
      write w ";";
      newline w
  | TCDInclude (file, is_system) ->
      if is_system then
        writef w "#include <%s>" file
      else
        writef w "#include \"%s\"" file;
      newline w
  | TCDDefine (name, value) ->
      (match value with
      | Some v -> writef w "#define %s %s" name v
      | None -> writef w "#define %s" name);
      newline w
  | TCDRaw s ->
      write w s;
      newline w

(* ============================================================================
 * Closure Implementation Generation
 * ============================================================================ *)

(* Helper: get C string for extracting capture from FibDynamic based on type *)
let capture_extract_expr (cap : tc_capture) : string =
  let idx = cap.cap_index in
  match cap.cap_type with
  | TCInt32 -> Printf.sprintf "_closure->captures[%d].data.intVal" idx
  | TCInt64 -> Printf.sprintf "_closure->captures[%d].data.int64Val" idx
  | TCFloat64 -> Printf.sprintf "_closure->captures[%d].data.floatVal" idx
  | TCBool -> Printf.sprintf "_closure->captures[%d].data.boolVal" idx
  | TCFibString -> Printf.sprintf "_closure->captures[%d].data.stringVal" idx
  | TCFibClosure -> Printf.sprintf "(FibClosure*)_closure->captures[%d].data.ptrVal" idx
  | t -> Printf.sprintf "(%s)_closure->captures[%d].data.ptrVal" (tc_type_to_string t) idx

(* Helper: get C expression for boxing value to FibDynamic based on type *)
let box_to_dynamic (var_name : string) (t : tc_type) : string =
  match t with
  | TCInt32 -> Printf.sprintf "fib_dynamic_int(%s)" var_name
  | TCInt64 -> Printf.sprintf "fib_dynamic_int64(%s)" var_name
  | TCFloat64 -> Printf.sprintf "fib_dynamic_float(%s)" var_name
  | TCBool -> Printf.sprintf "fib_dynamic_bool(%s)" var_name
  | TCFibString -> Printf.sprintf "fib_dynamic_string(%s)" var_name
  | TCVoid -> "fib_dynamic_null()"
  | _ -> Printf.sprintf "(FibDynamic){.type=FIB_TYPE_OBJECT, .data.ptrVal=%s}" var_name

(* Helper: get C expression for unboxing FibDynamic to typed value *)
let unbox_from_dynamic (arg_name : string) (t : tc_type) : string =
  match t with
  | TCInt32 -> Printf.sprintf "fib_dynamic_to_int(%s)" arg_name
  | TCInt64 -> Printf.sprintf "fib_dynamic_to_int64(%s)" arg_name
  | TCFloat64 -> Printf.sprintf "fib_dynamic_to_float(%s)" arg_name
  | TCBool -> Printf.sprintf "fib_dynamic_to_bool(%s)" arg_name
  | TCFibString -> Printf.sprintf "fib_dynamic_to_string(%s)" arg_name
  | TCFibClosure -> Printf.sprintf "(FibClosure*)fib_dynamic_to_object(%s)" arg_name
  | TCFibDynamic -> arg_name  (* Pass through unchanged *)
  | t -> Printf.sprintf "(%s)fib_dynamic_to_object(%s)" (tc_type_to_string t) arg_name

(* Generate forward declarations for a closure *)
let write_closure_forward_decls (w : writer) (cl : tc_closure) : unit =
  (* Forward declaration for typed impl function *)
  write w "static ";
  write_type w cl.cl_ret;
  writef w " %s(FibClosure* _closure" cl.cl_impl_name;
  List.iter (fun arg ->
    write w ", ";
    write_type_with_name w arg.fa_type arg.fa_name
  ) cl.cl_args;
  write w ");";
  newline w;
  
  (* Forward declaration for dynamic thunk *)
  writef w "static FibDynamic %s(FibClosure* _closure" cl.cl_name;
  List.iteri (fun i _ ->
    writef w ", FibDynamic _arg%d" i
  ) cl.cl_args;
  write w ");";
  newline w

(* Generate the typed implementation function for a closure *)
let write_closure_impl (w : writer) (cl : tc_closure) ~(debug_level : int) : unit =
  (* Function signature *)
  write w "static ";
  write_type w cl.cl_ret;
  writef w " %s(FibClosure* _closure" cl.cl_impl_name;
  List.iter (fun arg ->
    write w ", ";
    write_type_with_name w arg.fa_type arg.fa_name
  ) cl.cl_args;
  write w ") {";
  newline w;
  indent w;
  
  (* GC context *)
  write w "FIB_GC_CTX;";
  newline w;
  
  (* Debug stack frame *)
  if debug_level > 0 then begin
    writef w "FIB_LOCAL_STACK_FRAME(_fib_pos_%s, \"<closure>\", \"%s\", \"<closure>.%s\", \"generated\", 0);"
      cl.cl_impl_name cl.cl_name cl.cl_name;
    newline w;
    writef w "FIB_STACKFRAME(&_fib_pos_%s);" cl.cl_impl_name;
    newline w
  end;
  
  (* GC root the _closure parameter *)
  write w "gc_push_temp_root_ctx(FIB_CTX, (void**)&_closure);";
  newline w;
  let gc_count = ref 1 in
  
  (* GC root other GC-typed parameters *)
  List.iter (fun arg ->
    if needs_gc_root arg.fa_type then begin
      writef w "gc_push_temp_root_ctx(FIB_CTX, (void**)&%s);" arg.fa_name;
      newline w;
      incr gc_count
    end
  ) cl.cl_args;
  
  (* Suppress unused _closure warning if no captures *)
  if cl.cl_captures = [] then begin
    write w "(void)_closure;";
    newline w
  end;
  
  (* Extract captured variables and GC root pointer-type captures.
   * Without rooting, if GC evacuates objects during this closure's execution,
   * local copies of captured pointers become stale (point to old/freed memory).
   * The closure itself is rooted, so its captures get updated, but we also need
   * the extracted local variables to be GC roots so they get updated too. *)
  List.iter (fun cap ->
    write_type w cap.cap_type;
    writef w " %s = %s;" cap.cap_var (capture_extract_expr cap);
    newline w;
    if needs_gc_root cap.cap_type then begin
      writef w "gc_push_temp_root_ctx(FIB_CTX, (void**)&%s);" cap.cap_var;
      newline w;
      incr gc_count
    end
  ) cl.cl_captures;
  
  (* Helper to write statements, transforming returns to include gc_pop.
   * This fixes the bug where gc_pop was placed after return statements. *)
  let rec write_stmt_with_gc_cleanup stmt =
    match stmt with
    | TCSReturn (Some e) when !gc_count > 0 ->
        (* For non-void returns: evaluate to temp, pop roots, return temp *)
        emit_pending_stmts w e;
        write w "{ ";
        write_type w cl.cl_ret;
        write w " _ret = ";
        write_expr w e;
        writef w "; gc_pop_temp_roots_ctx(FIB_CTX, %d); return _ret; }" !gc_count;
        newline w
    | TCSReturn None when !gc_count > 0 ->
        (* For void returns: pop roots, then return *)
        writef w "gc_pop_temp_roots_ctx(FIB_CTX, %d); return;" !gc_count;
        newline w
    | TCSReturn _ ->
        (* No GC roots to pop, emit normally *)
        write_stmt w stmt
    | TCSBlock stmts ->
        (* Recurse into blocks to find nested returns *)
        write w "{";
        newline w;
        indent w;
        List.iter write_stmt_with_gc_cleanup stmts;
        dedent w;
        write w "}";
        newline w
    | TCSIf (cond, then_stmts, else_opt) ->
        (* Recurse into if branches *)
        emit_pending_stmts w cond;
        write w "if (";
        write_expr w cond;
        write w ") {";
        newline w;
        indent w;
        List.iter write_stmt_with_gc_cleanup then_stmts;
        dedent w;
        write w "}";
        (match else_opt with
        | Some else_stmts ->
            write w " else {";
            newline w;
            indent w;
            List.iter write_stmt_with_gc_cleanup else_stmts;
            dedent w;
            write w "}"
        | None -> ());
        newline w
    | TCSWhile (cond, body, is_do_while) ->
        (* Recurse into while loops *)
        if is_do_while then begin
          write w "do {";
          newline w;
          indent w;
          List.iter write_stmt_with_gc_cleanup body;
          dedent w;
          write w "} while (";
          write_expr w cond;
          write w ");";
          newline w
        end else begin
          write w "while (";
          write_expr w cond;
          write w ") {";
          newline w;
          indent w;
          List.iter write_stmt_with_gc_cleanup body;
          dedent w;
          write w "}";
          newline w
        end
    | TCSSwitch sw ->
        (* Recurse into switch cases *)
        write w "switch (";
        write_expr w sw.sw_expr;
        write w ") {";
        newline w;
        List.iter (fun (values, stmts) ->
          List.iter (fun v ->
            write w "case ";
            write_expr w v;
            write w ":";
            newline w
          ) values;
          indent w;
          List.iter write_stmt_with_gc_cleanup stmts;
          write w "break;";
          newline w;
          dedent w
        ) sw.sw_cases;
        (match sw.sw_default with
        | Some stmts ->
            write w "default:";
            newline w;
            indent w;
            List.iter write_stmt_with_gc_cleanup stmts;
            dedent w
        | None -> ());
        newline w
    | TCSTry tr ->
        (* Recurse into try/catch blocks *)
        write w "FIB_TRY {";
        newline w;
        indent w;
        List.iter write_stmt_with_gc_cleanup tr.try_body;
        dedent w;
        write w "}";
        List.iter (fun catch ->
          writef w " FIB_CATCH(%s, " catch.catch_var;
          write_type w catch.catch_type;
          write w ") {";
          newline w;
          indent w;
          List.iter write_stmt_with_gc_cleanup catch.catch_body;
          dedent w;
          write w "}"
        ) tr.try_catches;
        write w " FIB_END_TRY";
        newline w
    | _ ->
        (* All other statements: emit normally *)
        write_stmt w stmt
  in
  
  (* Body statements with GC cleanup transformation *)
  List.iter write_stmt_with_gc_cleanup cl.cl_body;
  
  (* Fall-through cleanup for void closures that don't explicitly return *)
  if !gc_count > 0 && cl.cl_ret = TCVoid then begin
    writef w "gc_pop_temp_roots_ctx(FIB_CTX, %d);" !gc_count;
    newline w
  end;
  
  dedent w;
  write w "}";
  newline w;
  newline w

(* Generate the dynamic thunk for a closure *)
let write_closure_thunk (w : writer) (cl : tc_closure) : unit =
  (* Function signature *)
  writef w "static FibDynamic %s(FibClosure* _closure" cl.cl_name;
  List.iteri (fun i _ ->
    writef w ", FibDynamic _arg%d" i
  ) cl.cl_args;
  write w ") {";
  newline w;
  indent w;
  
  (* Convert FibDynamic args to typed *)
  List.iteri (fun i arg ->
    write_type w arg.fa_type;
    writef w " _typed%d = %s;" i (unbox_from_dynamic (Printf.sprintf "_arg%d" i) arg.fa_type);
    newline w
  ) cl.cl_args;
  
  (* Call the impl function *)
  let call_args = String.concat ", " (
    "_closure" :: List.mapi (fun i _ -> Printf.sprintf "_typed%d" i) cl.cl_args
  ) in
  
  if cl.cl_ret = TCVoid then begin
    writef w "%s(%s);" cl.cl_impl_name call_args;
    newline w;
    write w "return fib_dynamic_null();";
    newline w
  end else begin
    writef w "return %s;" (box_to_dynamic (Printf.sprintf "%s(%s)" cl.cl_impl_name call_args) cl.cl_ret);
    newline w
  end;
  
  dedent w;
  write w "}";
  newline w;
  newline w

(* Generate all code for a closure (forward decls + impl + thunk) *)
let write_closure (w : writer) (cl : tc_closure) ~(debug_level : int) : unit =
  write_closure_impl w cl ~debug_level;
  write_closure_thunk w cl

(* Generate forward declarations for multiple closures *)
let write_closures_forward_decls (w : writer) (closures : tc_closure list) : unit =
  if closures <> [] then begin
    write w "/* Closure forward declarations */";
    newline w;
    List.iter (write_closure_forward_decls w) closures;
    newline w
  end

(* Generate implementations for multiple closures *)
let write_closures (w : writer) (closures : tc_closure list) ~(debug_level : int) : unit =
  if closures <> [] then begin
    write w "/* Closure implementations */";
    newline w;
    List.iter (fun cl -> write_closure w cl ~debug_level) closures
  end

(* ============================================================================
 * Compilation Unit Emission
 * ============================================================================ *)

let write_unit (w : writer) (u : tc_unit) : unit =
  (* Includes *)
  List.iter (fun inc ->
    writef w "#include \"%s\"" inc;
    newline w
  ) u.tu_includes;
  if u.tu_includes <> [] then newline w;
  
  (* Declarations *)
  List.iter (write_decl w) u.tu_decls

(* Convenience function to generate C code from a compilation unit *)
let generate (u : tc_unit) : string =
  let w = create () in
  write_unit w u;
  contents w
