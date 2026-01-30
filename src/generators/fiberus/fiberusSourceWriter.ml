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
      write w "({ FibClosure* _dc = ";
      write_expr w closure;
      writef w "; FibDynamic _args[%d] = {" (List.length args);
      List.iteri (fun i arg ->
        if i > 0 then write w ", ";
        write_expr w arg
      ) args;
      writef w "}; fib_closure_call_dynamic(_dc, _args, %d); })" (List.length args)
  
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
      writef w "({ %s %s; memset(&%s, 0, sizeof(%s)); &%s; })"
        (tc_type_to_string typ) name name name name
  
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
      (* ({ FibDynamic _anon = fib_anon_new(); fib_anon_set(&_anon, "name", value); ... _anon; }) *)
      write w "({ FibDynamic _anon = fib_anon_new(); ";
      List.iter (fun (name, value) ->
        writef w "fib_anon_set(&_anon, \"%s\", " name;
        write_expr w value;
        write w "); "
      ) fields;
      write w "_anon; })"
  
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
  
  (* Compound expressions *)
  | TCEBlock (stmts, result) ->
      write w "({";
      newline w;
      indent w;
      List.iter (fun s -> write_stmt w s) stmts;
      (match result with
      | Some e -> write_expr w e; write w ";"
      | None -> ());
      newline w;
      dedent w;
      write w "})"
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

and write_stmt (w : writer) (s : tc_stmt) : unit =
  match s with
  | TCSExpr e ->
      write_expr w e;
      write w ";";
      newline w
  | TCSVar vd ->
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
        write w " while (";
        write_expr w cond;
        write w ");";
        newline w
      end else begin
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
       * Only emitted under FIBERUS_DEBUG to catch push/pop imbalances. *)
      write w "#ifdef FIBERUS_DEBUG";
      newline w;
      writef w "if (_fib_ctx && _fib_ctx->mTempRootCount != _gc_base_count + %d) {" expected;
      newline w;
      write w "  fprintf(stderr, \"[GC ROOT MISMATCH] expected %%zu got %%zu\\n\", ";
      writef w "(size_t)(_gc_base_count + %d), (size_t)_fib_ctx->mTempRootCount);" expected;
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
