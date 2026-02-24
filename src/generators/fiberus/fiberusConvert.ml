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
  mutable gc_local_count: int;        (* Current temp roots pushed in this scope (legacy) *)
  mutable loop_depth: int;            (* Nesting depth for yield points *)
  (* Exception handler stack cleanup for return/break/continue inside try blocks *)
  mutable try_depth: int;             (* Number of enclosing FIB_TRY blocks; return must pop this many *)
  mutable try_depth_at_loop: int;     (* try_depth at enclosing loop entry; break/continue pops try_depth - this *)
  (* Function-level GC root tracking for return cleanup *)
  mutable func_gc_root_count: int;    (* Roots pushed by function prologue (params + this); -1 = not in function *)
  (* GCFrame-based root tracking (shadow stack) *)
  mutable gc_frame_name: string;      (* Current frame variable name (e.g., "_gc") *)
  mutable gc_frame_slots: (string * tc_type) list;  (* Accumulated (name, type) pairs for frame slots - in reverse order *)
  mutable gc_frame_rooted_vars: (string, unit) Hashtbl.t;  (* Set of variable names that are in the GC frame *)
  mutable in_gc_frame: bool;          (* True when inside a GCFrame-managed function *)
  (* Closure support *)
  mutable closure_counter: int;       (* Counter for unique closure names *)
  mutable closures: tc_closure list;  (* Closures created during conversion *)
  mutable in_fiber_spawn: bool;       (* True if inside Fiber.spawn context *)
  mutable spawn_counter: int;         (* Counter for unique Fiber.spawn temp variable names *)
  mutable temp_counter: int;          (* Counter for unique temp variable names *)
  (* Fiber-escape analysis *)
  fiber_mature_vars: (int, unit) Hashtbl.t;  (* var_ids needing mature allocation *)
  (* Stack allocation escape analysis *)
  stack_alloc_vars: (int, tclass) Hashtbl.t;  (* var_ids eligible for stack allocation *)
  (* Method thunks for FClosure (method-as-value) *)
  method_thunks: (string, tc_method_thunk) Hashtbl.t;  (* thunk_name -> thunk info *)
  (* Variable C-type overrides (e.g. map iterators: TAnon -> TCRaw "FibXxxIterator*") *)
  var_type_overrides: (int, tc_type) Hashtbl.t;  (* v_id -> actual C type *)
  (* Debug/codegen options *)
  debug_level: int;                   (* 0=none, 1=function, 2=line *)
  mutable last_line: int;             (* Last emitted FIBLINE number (for dedup) *)
  has_stack_frame: bool;              (* True if function has FIB_STACKFRAME — FIBLINE requires it *)
}

(* Create an empty conversion context *)
let empty_ctx = {
  current_class = None;
  current_class_name = None;
  vtable_ctx = None;
  current_ret_type = None;
  gc_local_count = 0;
  loop_depth = 0;
  try_depth = 0;
  try_depth_at_loop = 0;
  func_gc_root_count = -1;
  gc_frame_name = "_gc";
  gc_frame_slots = [];
  gc_frame_rooted_vars = Hashtbl.create 0;
  in_gc_frame = false;
  closure_counter = 0;
  closures = [];
  in_fiber_spawn = false;
  spawn_counter = 0;
  temp_counter = 0;
  fiber_mature_vars = Hashtbl.create 0;
  stack_alloc_vars = Hashtbl.create 0;
  method_thunks = Hashtbl.create 0;
  var_type_overrides = Hashtbl.create 0;
  debug_level = 0;
  last_line = 0;
  has_stack_frame = false;
}

(* Create context with current class *)
let ctx_with_class c = {
  empty_ctx with
  current_class = Some c;
  current_class_name = Some (flat_path c.cl_path);
}

(* Create a context copy for nested scope *)
let ctx_for_scope ctx = {
  ctx with
  gc_local_count = ctx.gc_local_count;
}

(* Generate N fib_exc_pop() calls for cleaning up exception handler stack
 * when return/break/continue exits through enclosing try blocks. *)
let exc_pop_stmts n =
  List.init n (fun _ -> TCSRaw "fib_exc_pop();")

(* Global counters - simple and avoids all context propagation issues *)
let global_closure_counter = ref 0
let global_spawn_counter = ref 0
let global_cb_arg_counter = ref 0

(* ============================================================================
 * Callback Trampoline Generation
 *
 * When an extern method takes a function-typed parameter (callback), the
 * codegen generates a static C trampoline function + a global FibCallbackCtx*
 * variable. At the call site, the Haxe closure is wrapped in a FibCallbackCtx
 * and stored in the global; the trampoline function pointer is passed to C.
 *
 * The trampoline exits the GC-free zone, marshals C args to FibDynamic,
 * invokes the Haxe closure via fib_callback_invoke, then re-enters the zone.
 * ============================================================================ *)

(* Generated trampoline: a raw C code string emitted at file scope *)
type callback_trampoline = {
  cb_global_decl: string;     (* e.g. "static FibCallbackCtx* _cb_init_0 = NULL;" *)
  cb_trampoline_code: string; (* Full trampoline function definition *)
  cb_trampoline_name: string; (* Name for referencing at call site *)
  cb_global_name: string;     (* Name of the global FibCallbackCtx* *)
}

(* Global table: trampoline_name -> trampoline definition. Prevents duplicates. *)
let global_callback_trampolines : (string, callback_trampoline) Hashtbl.t = Hashtbl.create 16

(* Map a Haxe tc_type to the C type used in callback trampoline parameters.
   This differs from normal tc_type_to_string because strings come as const char*
   from native C code, not FibString*. *)
let cb_param_c_type tc =
  match tc with
  | TCFibString -> "const char*"
  | TCFibClosure -> "void*"  (* unlikely but safe *)
  | TCFibDynamic -> "void*"  (* shouldn't happen in extern callbacks *)
  | _ -> tc_type_to_string tc

(* Map a Haxe tc_type to the C type used for callback trampoline return values. *)
let cb_ret_c_type tc =
  match tc with
  | TCFibString -> "const char*"
  | _ -> tc_type_to_string tc

(* Generate the fib_extern_from_* marshalling expression to convert a C param
   to FibDynamic for callback invocation. *)
let cb_marshal_to_dynamic param_name tc =
  match tc with
  | TCBool -> Printf.sprintf "fib_extern_from_bool(%s)" param_name
  | TCInt8 | TCInt16 | TCInt32 | TCUInt8 | TCUInt16 -> Printf.sprintf "fib_extern_from_int(%s)" param_name
  | TCInt64 | TCUInt32 | TCUInt64 -> Printf.sprintf "fib_extern_from_int64(%s)" param_name
  | TCSizeT -> Printf.sprintf "fib_extern_from_int64((int64_t)%s)" param_name
  | TCFloat64 -> Printf.sprintf "fib_extern_from_float(%s)" param_name
  | TCFloat32 -> Printf.sprintf "fib_extern_from_float((double)%s)" param_name
  | TCFibString -> Printf.sprintf "fib_extern_from_string(%s)" param_name
  | TCPointer _ | TCRaw _ | TCFibClass _ | TCFibObject _ ->
    Printf.sprintf "fib_extern_from_ptr(%s)" param_name
  | TCConstPointer _ ->
    Printf.sprintf "fib_extern_from_ptr((void*)%s)" param_name
  | _ -> Printf.sprintf "fib_extern_from_ptr((void*)%s)" param_name

(* Generate a callback trampoline for an extern method's function-typed parameter.
   native_name: the C function name (from @:native)
   param_idx: which parameter is the callback
   param_types: the Haxe function type's parameter types (tc_type list)
   ret_type: the Haxe function type's return type (tc_type) *)
let gen_callback_trampoline native_name param_idx param_types ret_type =
  let trampoline_name = Printf.sprintf "_trampoline_%s_%d" native_name param_idx in
  let global_name = Printf.sprintf "_cb_%s_%d" native_name param_idx in
  (* Check if already generated *)
  if Hashtbl.mem global_callback_trampolines trampoline_name then
    Hashtbl.find global_callback_trampolines trampoline_name
  else begin
    let n_params = List.length param_types in
    (* Generate parameter list for the trampoline signature *)
    let param_decls = List.mapi (fun i tc ->
      Printf.sprintf "%s _p%d" (cb_param_c_type tc) i
    ) param_types in
    let param_list = String.concat ", " (if param_decls = [] then ["void"] else param_decls) in
    let ret_c = cb_ret_c_type ret_type in
    let is_void = ret_type = TCVoid in
    (* Generate marshalling lines *)
    let marshal_lines = List.mapi (fun i tc ->
      Printf.sprintf "    _args[%d] = %s;" i (cb_marshal_to_dynamic (Printf.sprintf "_p%d" i) tc)
    ) param_types in
    (* Build the trampoline function body *)
    let body_lines = [
      Printf.sprintf "static %s %s(%s) {" ret_c trampoline_name param_list;
    ] @ (if n_params > 0 then [
      Printf.sprintf "    FibDynamic _args[%d];" n_params;
    ] else []) @ marshal_lines @ [
      (if is_void then
        Printf.sprintf "    fib_callback_invoke(%s, %s, %d);"
          global_name (if n_params > 0 then "_args" else "NULL") n_params
      else
        Printf.sprintf "    FibDynamic _result = fib_callback_invoke(%s, %s, %d);"
          global_name (if n_params > 0 then "_args" else "NULL") n_params);
    ] @ (if not is_void then [
      (* Marshal return value back to C type *)
      (match ret_type with
       | TCBool -> "    return fib_extern_to_bool(_result);"
       | TCInt8 | TCInt16 | TCInt32 | TCUInt8 | TCUInt16 -> "    return fib_extern_to_int(_result);"
       | TCInt64 | TCUInt32 | TCUInt64 -> "    return fib_extern_to_int64(_result);"
       | TCFloat64 | TCFloat32 -> "    return (float)fib_extern_to_float(_result);"
       | TCFibString -> "    return fib_extern_to_cstring(_result);"
       | _ -> "    return fib_extern_to_ptr(_result);")
    ] else []) @ [
      "}";
    ] in
    let trampoline_code = String.concat "\n" body_lines in
    let global_decl = Printf.sprintf "static FibCallbackCtx* %s = NULL;" global_name in
    let trampoline = {
      cb_global_decl = global_decl;
      cb_trampoline_code = trampoline_code;
      cb_global_name = global_name;
      cb_trampoline_name = trampoline_name;
    } in
    Hashtbl.replace global_callback_trampolines trampoline_name trampoline;
    trampoline
  end

(* Get all generated trampolines as a raw C string for emission *)
let get_callback_trampolines_code () =
  let trampolines = Hashtbl.fold (fun _name t acc -> t :: acc) global_callback_trampolines [] in
  if trampolines = [] then ""
  else begin
    let buf = Buffer.create 1024 in
    Buffer.add_string buf "\n/* ===== Callback trampolines (generated) ===== */\n";
    List.iter (fun t ->
      Buffer.add_string buf t.cb_global_decl;
      Buffer.add_char buf '\n';
      Buffer.add_string buf t.cb_trampoline_code;
      Buffer.add_char buf '\n';
      Buffer.add_char buf '\n';
    ) trampolines;
    Buffer.contents buf
  end

(* Clear trampolines (called per class/file) *)
let clear_callback_trampolines () =
  Hashtbl.clear global_callback_trampolines

(* Reset counters at start of each class/file *)
let reset_counters () =
  global_closure_counter := 0;
  global_spawn_counter := 0

(* Generate a fresh closure name using global counter *)
let fresh_closure_name _ctx =
  let id = !global_closure_counter in
  incr global_closure_counter;
  Printf.sprintf "_closure_%d" id

(* Generate fresh spawn temp variable names to avoid redefinition errors *)
(* Returns (fc_name, fib_name, id) so callers can use the id for related vars *)
let fresh_spawn_vars _ctx =
  let id = !global_spawn_counter in
  incr global_spawn_counter;
  (Printf.sprintf "_fc%d" id, Printf.sprintf "_fib%d" id, id)

(* Get all closures registered during conversion *)
let get_closures ctx = List.rev ctx.closures

(* Get all method thunks registered during conversion *)
let get_method_thunks ctx =
  Hashtbl.fold (fun _name thunk acc -> thunk :: acc) ctx.method_thunks []

(* Render a tc_expr to its C source string via FiberusSourceWriter *)
let render_expr (cexpr : tc_expr) : string =
  let w = FiberusSourceWriter.create () in
  FiberusSourceWriter.write_expr w cexpr;
  FiberusSourceWriter.contents w

(* ============================================================================
 * GCFrame Helpers
 * ============================================================================ *)

(* Register a variable as a GC frame slot. Returns the slot name used in the frame. *)
let gc_frame_add_slot ctx var_name var_type =
  if not (Hashtbl.mem ctx.gc_frame_rooted_vars var_name) then begin
    ctx.gc_frame_slots <- (var_name, var_type) :: ctx.gc_frame_slots;
    Hashtbl.replace ctx.gc_frame_rooted_vars var_name ()
  end

(* Check if a variable is in the current GC frame *)
let gc_frame_has_var ctx var_name =
  Hashtbl.mem ctx.gc_frame_rooted_vars var_name

(* Create a reference to a variable through the GC frame: _gc.varname *)
let gc_frame_ref ctx var_name var_type =
  mk_expr (TCEDot (mk_expr (TCELocal ctx.gc_frame_name) TCVoid, var_name)) var_type

(* Build the gc_frame_info from accumulated slots (reverses to get declaration order) *)
let gc_frame_build_info ctx =
  let slots = List.rev ctx.gc_frame_slots in
  {
    gfi_name = ctx.gc_frame_name;
    gfi_slots = List.map (fun (name, typ) ->
      { gfs_name = name; gfs_type = typ; gfs_init = None }
    ) slots;
  }

(* Build gc_frame_info with initial values for params (first N slots get values) *)
let gc_frame_build_info_with_inits ctx param_inits =
  let slots = List.rev ctx.gc_frame_slots in
  let param_set = Hashtbl.create (List.length param_inits) in
  List.iter (fun (name, init_expr) -> Hashtbl.replace param_set name init_expr) param_inits;
  {
    gfi_name = ctx.gc_frame_name;
    gfi_slots = List.map (fun (name, typ) ->
      let init = try Some (Hashtbl.find param_set name) with Not_found -> None in
      { gfs_name = name; gfs_type = typ; gfs_init = init }
    ) slots;
  }

(* ============================================================================
 * GC-Aware Conversion Helpers
 * ============================================================================ *)

(* Check if a tc_type needs GC root registration when stored in a local variable *)
let needs_gc_root_tc = FiberusTypeUtils.needs_gc_root

(* Generate GC push statement if type needs it.
 * In GCFrame mode: registers a slot in the frame and emits assignment.
 * In legacy mode: emits TCSGCPush. *)
let gc_push_if_needed ctx var_name var_type =
  if needs_gc_root_tc var_type then begin
    if ctx.in_gc_frame then begin
      (* GCFrame mode: register slot and emit assignment into frame *)
      gc_frame_add_slot ctx var_name var_type;
      [TCSGCFrameAssign (ctx.gc_frame_name, var_name, mk_expr (TCELocal var_name) var_type)]
    end else begin
      ctx.gc_local_count <- ctx.gc_local_count + 1;
      [TCSGCPush (mk_expr (TCELocal var_name) var_type)]
    end
  end else
    []

(* Generate GC pop statement for n roots, decrementing gc_local_count.
 * In GCFrame mode: no-op (frame handles all cleanup at once). *)
let gc_pop_roots ctx n =
  if ctx.in_gc_frame then
    []  (* Frame-based: no individual pop needed *)
  else if n > 0 then begin
    ctx.gc_local_count <- ctx.gc_local_count - n;
    [TCSGCPop n]
  end else
    []

(* Calculate how many roots to pop to return to saved count *)
let gc_roots_to_pop ctx saved_count =
  ctx.gc_local_count - saved_count

(* Get the C element type for a specialized array kind *)
let element_type_of_array_kind = function
  | TCArrInt -> TCInt32
  | TCArrFloat -> TCFloat64
  | TCArrInt64 -> TCInt64
  | TCArrUInt64 -> TCUInt64
  | TCArrFloat32 -> TCFloat32
  | TCArrBool -> TCBool
  | TCArrUInt8 -> TCUInt8
  | TCArrGeneric -> TCFibDynamic

(* Save current gc_local_count for later restoration *)
let gc_save_count ctx = ctx.gc_local_count

(* Mark non-GC-type variable declarations as volatile when a sibling statement
 * is a TCSTry. This is necessary because FIB_TRY expands to setjmp, and the
 * C standard says local variables modified between setjmp and longjmp have
 * indeterminate values unless declared volatile. GC-type variables are exempt
 * because they are accessed through the GCFrame struct (_gc.varname), which
 * forces memory access and prevents register caching. *)
let mark_volatile_for_try (stmts : tc_stmt list) : tc_stmt list =
  let has_try = List.exists (function TCSTry _ -> true | _ -> false) stmts in
  if not has_try then stmts
  else
    List.map (function
      | TCSVar vd when not (needs_gc_root vd.vd_type) && not vd.vd_volatile ->
          TCSVar { vd with vd_volatile = true }
      | other -> other
    ) stmts

(* Coerce an expression to a target type (boxing/unboxing as needed).
 * IMPORTANT: Propagates pending_stmts from the inner expression so that
 * GC-rooted temp variable assignments are not silently dropped. *)
let coerce_to_type expr target_tc =
  if expr.ctype = target_tc then expr
  else
    let result =
      if target_tc = TCFibDynamic && expr.ctype <> TCFibDynamic then
        (* Box to FibDynamic *)
        mk_expr (TCEBox (expr, box_kind_of_type expr.ctype)) TCFibDynamic
      else if expr.ctype = TCFibDynamic && target_tc <> TCFibDynamic then begin
        (* Unbox from FibDynamic.
           For arrays: fib_dynamic_to_array always returns FibArray* (generic).
           Downgrade specialized targets to generic to prevent type-punning
           (e.g. reading FibDynamic elements as int32_t). The var-declaration
           path registers a type override so subsequent accesses use generic. *)
        let actual_target = match target_tc with
          | TCFibArray _ -> TCFibArray TCArrGeneric
          | _ -> target_tc
        in
        mk_expr (TCEUnbox (expr, actual_target)) actual_target
      end
      else if (expr.ctype = TCInt32 || expr.ctype = TCInt64) && (target_tc = TCFloat64 || target_tc = TCFloat32) then
        (* Numeric promotion: Int -> Float *)
        mk_expr (TCECast (target_tc, expr)) target_tc
      else if (expr.ctype = TCFloat64 || expr.ctype = TCFloat32) && (target_tc = TCInt32 || target_tc = TCInt64) then
        (* Numeric truncation: Float -> Int *)
        mk_expr (TCECast (target_tc, expr)) target_tc
	  else match expr.ctype, target_tc with
	  | TCFibClass src_name, TCFibClass tgt_name when src_name <> tgt_name ->
		(* Class/interface pointer cast (e.g., concrete class to interface) *)
		mk_expr (TCECast (target_tc, expr)) target_tc
	  | (TCFibIntMap | TCFibStringMap | TCFibInt64Map | TCFibObjectMap), TCFibClass _ ->
		(* Map object to interface/class pointer cast (e.g., IntMap to IMap) *)
		mk_expr (TCECast (target_tc, expr)) target_tc
	  | TCFibArray src_kind, TCFibArray tgt_kind when src_kind <> tgt_kind ->
        if src_kind = TCArrGeneric && tgt_kind <> TCArrGeneric then
          (* Generic -> Specialized: must convert elements (FibDynamic -> typed).
             This happens when generic functions like Lambda.array return FibArray
             but the Haxe type says Array<Int> etc. *)
          let func_name = match tgt_kind with
            | TCArrInt -> "fib_array_to_int_array"
            | _ -> "" (* Other specializations not yet supported -- fall back to cast *)
          in
          if func_name <> "" then
            mk_expr (TCECall (TCTFunc func_name, [expr])) target_tc
          else
            mk_expr (TCECast (target_tc, expr)) target_tc
        else
          (* Specialized -> Generic or different specializations:
             pointer cast suffices (header is layout-compatible). *)
          mk_expr (TCECast (target_tc, expr)) target_tc
      | _ ->
        (* Other type conversions - just return as-is for now *)
        expr
    in
    (* Propagate pending_stmts from inner expression *)
    if expr.pending_stmts <> [] && result.pending_stmts = [] then
      { result with pending_stmts = expr.pending_stmts; gc_roots = expr.gc_roots + result.gc_roots }
    else
      result

(* Box all arguments to FibDynamic for use in _fib_dyn_call_N *)
let box_args_for_dynamic_call args =
  List.map (fun arg ->
    if arg.ctype = TCFibDynamic then arg
    else
      let result = mk_expr (TCEBox (arg, box_kind_of_type arg.ctype)) TCFibDynamic in
      if arg.pending_stmts <> [] then
        { result with pending_stmts = arg.pending_stmts; gc_roots = arg.gc_roots }
      else result
  ) args

(* Wrap a TCEDynamicCall result with TCEUnbox if the expected return type is not Dynamic/Void *)
let unwrap_dynamic_result dyn_call result_tc =
  if result_tc = TCFibDynamic || result_tc = TCVoid then dyn_call
  else begin
    (* For arrays: always unbox to generic FibArray since fib_dynamic_to_array
       returns FibArray* regardless of runtime specialization. Casting to e.g.
       FibIntArray* would misinterpret FibDynamic[] data as int32_t[] data. *)
    let actual_tc = match result_tc with
      | TCFibArray _ -> TCFibArray TCArrGeneric
      | _ -> result_tc
    in
    { (mk_expr (TCEUnbox (dyn_call, actual_tc)) actual_tc) with cpos = dyn_call.cpos; pending_stmts = dyn_call.pending_stmts }
  end

(* ============================================================================
 * GC Safety for Nested Allocating Expressions
 * ============================================================================
 * 
 * Problem: When we have nested allocating calls like:
 *   fib_string_concat(fib_string_concat(a, b), c)
 * 
 * The inner call returns a GC pointer that's passed as an argument to the outer
 * call. If the outer call triggers GC (during its allocation), the inner result
 * may be in a CPU register that minor GC doesn't scan, causing use-after-free.
 *
 * Solution: Extract nested allocating expressions to temp variables with proper
 * GC rooting before passing them as arguments:
 *   FibString* _tmp0 = fib_string_concat(a, b);
 *   gc_push_temp_root(&_tmp0);
 *   FibString* result = fib_string_concat(_tmp0, c);
 *   gc_pop_temp_roots(1);
 *)

(* Counter for generating unique temp variable names *)
let gc_temp_counter = ref 0

(* Generate a unique temp variable name *)
let gen_gc_temp_name () =
  let n = !gc_temp_counter in
  gc_temp_counter := n + 1;
  Printf.sprintf "_gc_tmp%d" n

(* Check if a tc_expr has side effects (calls, assignments, inc/dec).
 * Expressions with side effects must not be emitted twice in C code,
 * as they would execute the side effect multiple times. *)
let rec tc_has_side_effects (e : tc_expr) : bool =
  match e.cexpr with
  (* Calls always have potential side effects *)
  | TCECall _ | TCEDynamicCall _ | TCEClosureCall _ | TCEVtableCall _ -> true
  (* Assignments and compound assignments *)
  | TCEAssign _ | TCEAssignOp _ -> true
  (* Increment/decrement *)
  | TCEUnop ((TCUPreInc | TCUPreDec | TCUPostInc | TCUPostDec), _) -> true
  (* Locals, literals, field access on pure expressions are pure *)
  | TCELocal _ | TCEInt _ | TCEInt64 _ | TCEFloat _ | TCEBool _ | TCENull | TCEString _ -> false
  (* Recurse into sub-expressions *)
  | TCEDot (sub, _) | TCEArrow (sub, _) -> tc_has_side_effects sub
  | TCEDeref sub | TCEAddrOf sub -> tc_has_side_effects sub
  | TCECast (_, sub) | TCEUnbox (sub, _) | TCEBox (sub, _) -> tc_has_side_effects sub
  | TCEUnop (_, sub) -> tc_has_side_effects sub
  | TCEBinop (_, a, b) -> tc_has_side_effects a || tc_has_side_effects b
  | TCETernary (c, t, f) -> tc_has_side_effects c || tc_has_side_effects t || tc_has_side_effects f
  | TCEArrayGet { arr; idx; _ } -> tc_has_side_effects arr || tc_has_side_effects idx
  (* Everything else: conservatively assume side effects *)
  | _ -> true

(* Extract a tc_expr to a temporary variable if it has side effects.
 * Returns (expr_to_use, pending_stmts_for_temp).
 * If the expression is pure, returns it unchanged with no pending stmts.
 * IMPORTANT: Returns e.pending_stmts as part of the pending list, so callers
 * must NOT separately include e.pending_stmts when using the cached version. *)
let cache_if_side_effects (e : tc_expr) : tc_expr * tc_stmt list =
  if tc_has_side_effects e then
    let stripped = { e with pending_stmts = [] } in
    let tmp_name = gen_gc_temp_name () in
    let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = e.ctype; vd_init = Some stripped;
      vd_static = false; vd_const = false; vd_volatile = false } in
    let tmp_ref = mk_expr (TCELocal tmp_name) e.ctype in
    (tmp_ref, e.pending_stmts @ [tmp_decl])
  else
    (e, e.pending_stmts)

(* Check if a tc_expr can potentially allocate GC memory.
 * These expressions need special handling when used as arguments to other
 * allocating expressions, because they return GC pointers that may be held
 * only in registers during the outer call. *)
let rec is_allocating_expr (e : tc_expr) : bool =
  match e.cexpr with
  (* String operations allocate *)
  | TCEStringConcat _ -> true
  | TCECall (TCTFunc "fib_string_new", _) -> true
  | TCECall (TCTFunc "fib_string_new_len", _) -> true
  | TCECall (TCTFunc "fib_string_from_int", _) -> true
  | TCECall (TCTFunc "fib_string_from_float", _) -> true
  | TCECall (TCTFunc "fib_string_from_int64", _) -> true
  | TCECall (TCTFunc "fib_string_format", _) -> true
  | TCECall (TCTFunc "fib_string_substring", _) -> true
  | TCECall (TCTFunc "fib_string_substr", _) -> true
  | TCECall (TCTFunc "fib_string_from_char_code", _) -> true
  | TCECall (TCTFunc "fib_dynamic_to_string", _) -> true
  | TCECall (TCTFunc "fib_dynamic_extract_string", _) -> true
  
  (* Object/array/closure allocations *)
  | TCENew _ -> true
  | TCECall (TCTFunc "fib_array_new", _) -> true
  | TCECall (TCTFunc "fib_anon_new", _) -> true
  | TCEAnonObject _ -> true
  | TCEArrayDecl _ -> true
  | TCEClosureCreate _ -> true
  
  (* Method calls that may allocate (conservatively assume they do if returning GC type).
     All call types must be included to prevent double-evaluation in write barriers. *)
  | TCECall _ when needs_gc_root_tc e.ctype -> true
  | TCEVtableCall _ when needs_gc_root_tc e.ctype -> true
  (* Dynamic/closure calls have side effects - must extract to avoid double-eval
     in write barrier pattern. The write barrier itself does NOT trigger GC (it only
     checks nursery flags and sets REMEMBERED bit), so _wb_N temps are safe. *)
  | TCEDynamicCall _ -> true
  | TCEClosureCall _ -> true
  
  (* Boxing itself does not heap-allocate; it wraps a value in a stack FibDynamic.
     But the inner expression may allocate, so recurse. *)
  | TCEBox (sub, _) -> is_allocating_expr sub
  
  (* Ternary - allocates if either branch allocates *)
  | TCETernary (_, t, f) -> is_allocating_expr t || is_allocating_expr f
  
  (* Block - check the result expression *)
  | TCEBlock (_, Some result) -> is_allocating_expr result
  
  (* String literals allocate via fib_string_new *)
  | TCEString _ -> true
  
  (* These don't allocate *)
  | TCELocal _ | TCEInt _ | TCEInt64 _ | TCEFloat _ | TCEBool _ | TCENull -> false
  | TCEUnop _ | TCEBinop _ -> false
  | TCEEnumIndex _ | TCEEnumParam _ | TCEEnumConst _ -> false
  | TCEStringEq _ | TCEStringCompare _ | TCEStringLength _ -> false
  | TCEInstanceOf _ -> false
  
  (* Field/array access and casts don't allocate themselves, but may contain
   * allocating sub-expressions that need extraction. Check recursively. *)
  | TCEDot (sub, _) | TCEArrow (sub, _) -> is_allocating_expr sub
  | TCEArrayGet { arr; idx; _ } -> is_allocating_expr arr || is_allocating_expr idx
  | TCECast (_, sub) | TCEUnbox (sub, _) -> is_allocating_expr sub
  
  | _ -> false

(* Check if an expression yields a GC pointer from a "volatile" source that
 * could become invalid if GC runs. This is used to determine if we need to
 * extract the expression to a rooted temp variable before dereferencing it.
 * 
 * Key cases:
 * - Array element access returning an object - the object pointer in FibDynamic
 *   is not rooted and can become stale if GC evacuates the object
 * - Method/function calls returning objects - result may be in a register
 * - Casts/unboxes of the above - propagate the volatility
 * - Field access on volatile objects - the object itself may move
 *)
let rec needs_extraction_before_deref (e : tc_expr) : bool =
  if not (needs_gc_root_tc e.ctype) then false
  else match e.cexpr with
  (* Local variables are already rooted on the stack *)
  | TCELocal _ -> false
  (* Static fields are in global memory, stable *)
  | TCEStatic _ -> false
  (* 'this' pointer is rooted *)
  | TCEThis -> false
  (* Literals don't need rooting *)
  | TCENull -> false
  
  (* Array element access returning GC type - VOLATILE! The object pointer
   * extracted from FibDynamic.data.objectVal is not rooted. *)
  | TCEArrayGet _ -> true
  
  (* Calls returning GC type - result may be in register only *)
  | TCECall _ | TCEVtableCall _ | TCEClosureCall _ | TCEDynamicCall _ -> true
  
  (* New allocations are volatile until rooted *)
  | TCENew _ -> true
  | TCEClosureCreate _ -> true
  
  (* Casts/unboxes propagate volatility from their inner expression *)
  | TCECast (_, sub) | TCEUnbox (sub, _) -> needs_extraction_before_deref sub
  
  (* Field access on volatile object - the object may move *)
  | TCEDot (sub, _) | TCEArrow (sub, _) -> needs_extraction_before_deref sub
  
  (* Ternary - volatile if either branch is volatile *)
  | TCETernary (_, t, f) -> needs_extraction_before_deref t || needs_extraction_before_deref f
  
  (* Block - check the result expression *)
  | TCEBlock (_, Some result) -> needs_extraction_before_deref result
  | TCEBlock (_, None) -> false
  
  (* Everything else - conservatively say not volatile *)
  | _ -> false

(* Extract an allocating sub-expression to a temp variable with GC rooting.
 * Returns (new_expr, stmts) where:
 *   - new_expr is either the original expr (if not allocating) or a reference to a temp var
 *   - stmts are the statements needed to set up the temp var with GC rooting
 * 
 * The caller is responsible for generating the gc_pop_temp_roots at the end.
 *
 * We extract in two cases:
 * 1. The expression is allocating AND is a GC type - need to root the result
 * 2. The expression has gc_roots > 0 - need to clean up those roots
 * Case 2 handles nested blocks that leave roots on the stack even if their
 * final result is a simple local variable. *)
(* extract_if_allocating: Internal version that takes a context for frame-aware extraction.
 * When ctx is Some and in_gc_frame is true, uses frame slots instead of push/pop. *)
let extract_if_allocating_ctx (ctx : conv_ctx option) (e : tc_expr) : tc_expr * tc_stmt list * int =
  let in_frame = match ctx with Some c -> c.in_gc_frame | None -> false in
  let needs_extraction = 
    (is_allocating_expr e && needs_gc_root_tc e.ctype) || e.gc_roots > 0
  in
  if not needs_extraction then
    (* No extraction needed - expression is simple and leaves no roots *)
    (e, [], 0)
  else if not (needs_gc_root_tc e.ctype) && e.gc_roots > 0 then begin
    (* Special case: expression has gc_roots but result doesn't need rooting.
     * We just need to clean up the gc_roots, not create a rooted temp var.
     * In frame mode: gc_roots from sub-expressions are 0 (frame handles all). *)
    if in_frame then
      (e, [], 0)
    else begin
      let cleanup = TCSGCPop e.gc_roots in
      (e, [cleanup], 0)
    end
   end else begin
     (* Generate temp variable *)
     let tmp_name = gen_gc_temp_name () in
     let tmp_type = e.ctype in
     (* Strip pending_stmts from e before storing in vd_init — the writer
        emits vd_init.pending_stmts when processing TCSVar, so we must keep
        them only in the returned stmts list to avoid double emission. *)
     let e_for_init = { e with pending_stmts = [] } in
     
     if in_frame then begin
       let c = match ctx with Some c -> c | None -> assert false in
       (* GCFrame mode: register slot, declare local, assign to frame *)
       gc_frame_add_slot c tmp_name tmp_type;
       (* Declare local variable *)
       let var_decl = TCSVar {
         vd_name = tmp_name;
         vd_type = tmp_type;
         vd_init = Some e_for_init;
         vd_static = false;
         vd_const = false; vd_volatile = false;
       } in
       (* Assign to frame slot for GC visibility *)
       let frame_assign = TCSGCFrameAssign (c.gc_frame_name, tmp_name, mk_expr (TCELocal tmp_name) tmp_type) in
       (* Reference through frame slot so GC updates are visible *)
       let tmp_ref = gc_frame_ref c tmp_name tmp_type in
       (* No gc_roots left on legacy stack — frame handles it *)
       (tmp_ref, e.pending_stmts @ [var_decl; frame_assign], 0)
     end else begin
       (* Legacy mode: push/pop *)
       let var_decl = TCSVar {
         vd_name = tmp_name;
         vd_type = tmp_type;
         vd_init = Some e_for_init;
         vd_static = false;
         vd_const = false; vd_volatile = false;
       } in
       let cleanup_stmts = 
         if e.gc_roots > 0 then [TCSGCPop e.gc_roots]
         else []
       in
       let gc_push = TCSGCPush (mk_expr (TCELocal tmp_name) tmp_type) in
       let tmp_ref = mk_expr (TCELocal tmp_name) tmp_type in
       (tmp_ref, e.pending_stmts @ [var_decl] @ cleanup_stmts @ [gc_push], 1)
     end
   end

(* Backward-compatible wrapper: extracts without frame context *)
let extract_if_allocating (e : tc_expr) : tc_expr * tc_stmt list * int =
  extract_if_allocating_ctx None e

(* Wrap an expression with GC-safe extraction of allocating sub-expressions.
 * This is used for binary operations like string concat where both operands
 * might be allocating expressions.
 * 
 * If any extraction is needed, wraps the final expression in a TCEBlock
 * that includes the temp var setup, the expression, GC cleanup, and returns
 * the result via another temp variable.
 * 
 * CRITICAL: The result itself must be rooted before we pop the input roots,
 * because the block's return value may be passed to another allocating function
 * which could trigger GC. Without rooting the result, it would be corrupted.
 * 
 * The sequence is:
 *   1. Push roots for extracted input arguments
 *   2. Compute the final expression, store in result temp
 *   3. Push root for result temp (so it survives any subsequent GC)
 *   4. Pop roots for input arguments (they're no longer needed)
 *   5. Return result (still rooted)
 * 
 * The returned expression has gc_roots=1 to indicate one unpaired root remains.
 * The caller (genfiberus.ml) will pop this root at statement boundaries.
 *)
(* wrap_with_gc_extraction: frame-aware version that takes optional context *)
let wrap_with_gc_extraction_ctx (ctx : conv_ctx option) (make_final : tc_expr -> tc_expr -> tc_expr) (e1 : tc_expr) (e2 : tc_expr) : tc_expr =
  let in_frame = match ctx with Some c -> c.in_gc_frame | None -> false in
  let (e1', stmts1, roots1) = extract_if_allocating_ctx ctx e1 in
  let (e2', stmts2, roots2) = extract_if_allocating_ctx ctx e2 in
  let total_input_roots = roots1 + roots2 in
  
  (* Collect pending_stmts from non-extracted sub-expressions.
   * When extract_if_allocating_ctx extracts, pending_stmts are preserved inside
   * the TCSVar's init expression. But when no extraction occurs, the sub-expression's
   * pending_stmts must be explicitly included, since make_final won't propagate them. *)
  let e1_pending = if stmts1 = [] then e1.pending_stmts else [] in
  let e2_pending = if stmts2 = [] then e2.pending_stmts else [] in
  
   if in_frame then begin
     (* GCFrame mode: all roots are in the frame, no push/pop bookkeeping needed.
      * If extraction happened, temps are already in frame slots. *)
     if stmts1 = [] && stmts2 = [] then begin
       (* Strip pending_stmts before passing to make_final — make_final may collect
          them again via mk_expr_inherit, causing duplication. We keep them only in
          the outer pending_stmts list. *)
       let e1_clean = { e1 with pending_stmts = [] } in
       let e2_clean = { e2 with pending_stmts = [] } in
       let final = make_final e1_clean e2_clean in
       { final with 
         pending_stmts = e1.pending_stmts @ e2.pending_stmts @ final.pending_stmts }
     end else begin
       let final_expr = make_final e1' e2' in
       let final_for_init = { final_expr with pending_stmts = [] } in
       let result_type = final_expr.ctype in
       let result_needs_gc = needs_gc_root_tc result_type in
       let result_name = gen_gc_temp_name () in
       let result_var = TCSVar {
         vd_name = result_name;
         vd_type = result_type;
         vd_init = Some final_for_init;
         vd_static = false;
         vd_const = false; vd_volatile = false;
       } in
       let c = match ctx with Some c -> c | None -> assert false in
       let frame_stmts = if result_needs_gc then begin
         gc_frame_add_slot c result_name result_type;
         [result_var; TCSGCFrameAssign (c.gc_frame_name, result_name, mk_expr (TCELocal result_name) result_type)]
       end else
         [result_var]
       in
       let pending = e1_pending @ e2_pending @ stmts1 @ stmts2 @ final_expr.pending_stmts @ frame_stmts in
       mk_expr_lifted_gc (TCELocal result_name) result_type pending 0
     end
   end else begin
      (* Legacy mode: push/pop *)
      if total_input_roots = 0 then begin
        let e1_clean = { e1 with pending_stmts = [] } in
        let e2_clean = { e2 with pending_stmts = [] } in
        let final = make_final e1_clean e2_clean in
        { final with 
          gc_roots = e1.gc_roots + e2.gc_roots;
          pending_stmts = e1.pending_stmts @ e2.pending_stmts @ final.pending_stmts }
      end else begin
       let final_expr = make_final e1' e2' in
       let final_for_init = { final_expr with pending_stmts = [] } in
       let result_type = final_expr.ctype in
       let result_needs_gc = needs_gc_root_tc result_type in
       let result_name = gen_gc_temp_name () in
       let result_var = TCSVar {
         vd_name = result_name;
         vd_type = result_type;
         vd_init = Some final_for_init;
         vd_static = false;
         vd_const = false; vd_volatile = false;
       } in
       let gc_pop = TCSGCPop total_input_roots in
       let pending = 
         if result_needs_gc then
           let result_gc_push = TCSGCPush (mk_expr (TCELocal result_name) result_type) in
           e1_pending @ e2_pending @ stmts1 @ stmts2 @ final_expr.pending_stmts @ [result_var; gc_pop; result_gc_push]
         else
           e1_pending @ e2_pending @ stmts1 @ stmts2 @ final_expr.pending_stmts @ [result_var; gc_pop]
       in
      let result_roots = if result_needs_gc then 1 else 0 in
      mk_expr_lifted_gc (TCELocal result_name) result_type pending result_roots
    end
  end

(* Backward-compatible wrapper *)
let wrap_with_gc_extraction (make_final : tc_expr -> tc_expr -> tc_expr) (e1 : tc_expr) (e2 : tc_expr) : tc_expr =
  wrap_with_gc_extraction_ctx None make_final e1 e2

(* Similar to wrap_with_gc_extraction but for call arguments.
 * Extracts all allocating arguments to temp variables.
 * 
 * Like wrap_with_gc_extraction, the result is rooted and gc_roots is set
 * so that the caller can pop at statement boundaries.
 *)
(* wrap_call_with_gc_extraction: frame-aware version *)
let wrap_call_with_gc_extraction_ctx (ctx : conv_ctx option) (make_call : tc_expr list -> tc_expr) (args : tc_expr list) : tc_expr =
  let in_frame = match ctx with Some c -> c.in_gc_frame | None -> false in
  let extracted = List.map (extract_if_allocating_ctx ctx) args in
  let args' = List.map (fun (e, _, _) -> e) extracted in
  let all_stmts = List.concat (List.map (fun (_, stmts, _) -> stmts) extracted) in
  let total_roots = List.fold_left (fun acc (_, _, n) -> acc + n) 0 extracted in
  
  (* Collect pending_stmts from args that were NOT extracted.
   * When extraction happens, pending_stmts are preserved inside the TCSVar's init.
   * But non-extracted args keep their pending_stmts which must be explicitly included. *)
  let non_extracted_pending = List.concat_map (fun ((_, stmts, _), orig_arg) ->
    if stmts = [] then orig_arg.pending_stmts else []
  ) (List.combine extracted args) in
  
   if in_frame then begin
     (* GCFrame mode: all roots in frame, no push/pop bookkeeping *)
     if all_stmts = [] then begin
       let args_clean = List.map (fun a -> { a with pending_stmts = [] }) args in
       let final = make_call args_clean in
       { final with 
         pending_stmts = collect_pending args @ final.pending_stmts }
     end else begin
       let final_expr = make_call args' in
       let result_type = final_expr.ctype in
       (* Void results cannot be stored in variables — emit as statement *)
       if result_type = TCVoid then begin
         let call_stmt = TCSExpr { final_expr with pending_stmts = [] } in
         let pending = non_extracted_pending @ all_stmts @ final_expr.pending_stmts @ [call_stmt] in
         mk_expr_lifted_gc (TCERaw "(void)0") TCVoid pending 0
       end else begin
         let final_for_init = { final_expr with pending_stmts = [] } in
         let result_needs_gc = needs_gc_root_tc result_type in
         let result_name = gen_gc_temp_name () in
         let result_var = TCSVar {
           vd_name = result_name;
           vd_type = result_type;
           vd_init = Some final_for_init;
           vd_static = false;
           vd_const = false; vd_volatile = false;
         } in
         let c = match ctx with Some c -> c | None -> assert false in
         let frame_stmts = if result_needs_gc then begin
           gc_frame_add_slot c result_name result_type;
           [result_var; TCSGCFrameAssign (c.gc_frame_name, result_name, mk_expr (TCELocal result_name) result_type)]
         end else
           [result_var]
         in
         let pending = non_extracted_pending @ all_stmts @ final_expr.pending_stmts @ frame_stmts in
         mk_expr_lifted_gc (TCELocal result_name) result_type pending 0
       end
      end
    end else begin
      (* Legacy mode *)
      if total_roots = 0 then begin
        let args_clean = List.map (fun a -> { a with pending_stmts = [] }) args in
        let final = make_call args_clean in
        { final with 
          gc_roots = sum_gc_roots args;
          pending_stmts = collect_pending args @ final.pending_stmts }
      end else begin
       let final_expr = make_call args' in
       let result_type = final_expr.ctype in
       let gc_pop = TCSGCPop total_roots in
       (* Void results cannot be stored in variables — emit as statement *)
       if result_type = TCVoid then begin
         let call_stmt = TCSExpr { final_expr with pending_stmts = [] } in
         let pending = non_extracted_pending @ all_stmts @ final_expr.pending_stmts @ [call_stmt; gc_pop] in
         mk_expr_lifted_gc (TCERaw "(void)0") TCVoid pending 0
       end else begin
         let final_for_init = { final_expr with pending_stmts = [] } in
         let result_needs_gc = needs_gc_root_tc result_type in
         let result_name = gen_gc_temp_name () in
         let result_var = TCSVar {
           vd_name = result_name;
           vd_type = result_type;
           vd_init = Some final_for_init;
           vd_static = false;
           vd_const = false; vd_volatile = false;
         } in
         let pending = 
           if result_needs_gc then
             let result_gc_push = TCSGCPush (mk_expr (TCELocal result_name) result_type) in
             non_extracted_pending @ all_stmts @ final_expr.pending_stmts @ [result_var; gc_pop; result_gc_push]
           else
             non_extracted_pending @ all_stmts @ final_expr.pending_stmts @ [result_var; gc_pop]
         in
         let result_roots = if result_needs_gc then 1 else 0 in
         mk_expr_lifted_gc (TCELocal result_name) result_type pending result_roots
       end
     end
   end

(* Backward-compatible wrapper *)
let wrap_call_with_gc_extraction (make_call : tc_expr list -> tc_expr) (args : tc_expr list) : tc_expr =
  wrap_call_with_gc_extraction_ctx None make_call args

(* Wrap a single expression with GC-safe extraction if it needs extraction
 * before being dereferenced. This is used when we need to ensure an 
 * intermediate pointer is rooted before being dereferenced (e.g., field 
 * access on array element).
 * 
 * If the expression needs extraction (is volatile/allocating and returns a 
 * GC type), it's extracted to a temp variable which is rooted. The make_final 
 * function is then applied to the temp variable reference.
 * 
 * The returned expression has gc_roots set appropriately so callers can
 * clean up at statement boundaries.
 *)
(* Frame-aware single extraction *)
let rec wrap_single_gc_extraction_ctx (ctx : conv_ctx option) (make_final : tc_expr -> tc_expr) (e : tc_expr) : tc_expr =
  let in_frame = match ctx with Some c -> c.in_gc_frame | None -> false in
  if in_frame then begin
    (* GCFrame mode: if we need to extract, put it in a frame slot *)
     let needs_extract = needs_extraction_before_deref e in
     if not needs_extract then begin
       let e_clean = { e with pending_stmts = [] } in
       let final = make_final e_clean in
       { final with 
         pending_stmts = e.pending_stmts @ final.pending_stmts }
      end else begin
       let c = match ctx with Some c -> c | None -> assert false in
       let tmp_name = gen_gc_temp_name () in
       let tmp_type = e.ctype in
       gc_frame_add_slot c tmp_name tmp_type;
       let e_for_init = { e with pending_stmts = [] } in
       let var_decl = TCSVar {
         vd_name = tmp_name;
         vd_type = tmp_type;
         vd_init = Some e_for_init;
         vd_static = false;
         vd_const = false; vd_volatile = false;
       } in
       let frame_assign = TCSGCFrameAssign (c.gc_frame_name, tmp_name, mk_expr (TCELocal tmp_name) tmp_type) in
       (* Reference through frame slot so GC updates are visible *)
       let tmp_ref = gc_frame_ref c tmp_name tmp_type in
       let final_expr = make_final tmp_ref in
       let final_for_init = { final_expr with pending_stmts = [] } in
       let result_type = final_expr.ctype in
       let result_needs_gc = needs_gc_root_tc result_type in
       if result_type = TCVoid then begin
         (* Void results cannot be stored in variables — emit as statement *)
         let call_stmt = TCSExpr final_for_init in
         let pending = e.pending_stmts @ [var_decl; frame_assign] @ final_expr.pending_stmts @ [call_stmt] in
         mk_expr_lifted_gc (TCERaw "(void)0") TCVoid pending 0
       end else if not result_needs_gc then begin
         let result_name = gen_gc_temp_name () in
         let result_var = TCSVar {
           vd_name = result_name;
           vd_type = result_type;
           vd_init = Some final_for_init;
           vd_static = false;
           vd_const = false; vd_volatile = false;
         } in
         let pending = e.pending_stmts @ [var_decl; frame_assign] @ final_expr.pending_stmts @ [result_var] in
         mk_expr_lifted_gc (TCELocal result_name) result_type pending 0
       end else begin
         let result_name = gen_gc_temp_name () in
         gc_frame_add_slot c result_name result_type;
         let result_var = TCSVar {
           vd_name = result_name;
           vd_type = result_type;
           vd_init = Some final_for_init;
           vd_static = false;
           vd_const = false; vd_volatile = false;
         } in
         let result_frame_assign = TCSGCFrameAssign (c.gc_frame_name, result_name, mk_expr (TCELocal result_name) result_type) in
         let pending = e.pending_stmts @ [var_decl; frame_assign] @ final_expr.pending_stmts @ [result_var; result_frame_assign] in
         mk_expr_lifted_gc (TCELocal result_name) result_type pending 0
       end
    end
  end else
    (* Legacy mode: delegate to original *)
    wrap_single_gc_extraction_legacy make_final e

and wrap_single_gc_extraction_legacy (make_final : tc_expr -> tc_expr) (e : tc_expr) : tc_expr =
  (* Use needs_extraction_before_deref to check if we need to root the object
   * before accessing its fields. This catches cases like:
   * - Array element access returning an object (volatile! not rooted)
   * - Method calls returning objects  
   * - Casts/unboxes of the above
   * 
   * NOTE: This is different from is_allocating_expr. An expression like
   * data[i] doesn't allocate, but the resulting pointer IS volatile because
   * it's extracted from FibDynamic and not rooted. If GC runs before we use
   * it, the object could be evacuated and the pointer becomes stale.
   *)
  let needs_extract = needs_extraction_before_deref e in
  
   if not needs_extract then begin
     (* No extraction needed - just apply make_final directly.
      * Strip pending_stmts before passing to make_final to prevent duplication. *)
     let e_clean = { e with pending_stmts = [] } in
     let final = make_final e_clean in
     { final with 
       pending_stmts = e.pending_stmts @ final.pending_stmts;
       gc_roots = e.gc_roots }
   end else begin
     (* Expression yields a volatile GC pointer that must be rooted before use.
      * We directly create a rooted temp variable, bypassing extract_if_allocating
      * which would check is_allocating_expr (wrong check for this case). *)
     let tmp_name = gen_gc_temp_name () in
     let tmp_type = e.ctype in
     let e_for_init = { e with pending_stmts = [] } in
     
     (* Create variable declaration to capture the volatile expression *)
     let var_decl = TCSVar {
       vd_name = tmp_name;
       vd_type = tmp_type;
       vd_init = Some e_for_init;
       vd_static = false;
       vd_const = false; vd_volatile = false;
     } in
     
     (* Handle any existing gc_roots from nested expressions *)
     let cleanup_stmts = 
       if e.gc_roots > 0 then [TCSGCPop e.gc_roots]
       else []
     in
     
     (* Push the temp variable as a GC root *)
     let gc_push = TCSGCPush (mk_expr (TCELocal tmp_name) tmp_type) in
     
     (* Now apply make_final to the safe (rooted) reference *)
     let tmp_ref = mk_expr (TCELocal tmp_name) tmp_type in
     let final_expr = make_final tmp_ref in
     let final_for_init = { final_expr with pending_stmts = [] } in
     let result_type = final_expr.ctype in
     
     (* Check if result also needs rooting *)
     let result_needs_gc = needs_gc_root_tc result_type in
     
     if result_type = TCVoid then begin
       (* Void results cannot be stored in variables — emit as statement *)
       let call_stmt = TCSExpr final_for_init in
       let gc_pop = TCSGCPop 1 in
       let pending = e.pending_stmts @ [var_decl] @ cleanup_stmts @ [gc_push] @ final_expr.pending_stmts @ [call_stmt; gc_pop] in
       mk_expr_lifted_gc (TCERaw "(void)0") TCVoid pending 0
     end else if not result_needs_gc then begin
       (* Result is not a GC type - compute result, then pop input root *)
       let result_name = gen_gc_temp_name () in
       let result_var = TCSVar {
         vd_name = result_name;
         vd_type = result_type;
         vd_init = Some final_for_init;
         vd_static = false;
         vd_const = false; vd_volatile = false;
       } in
       let gc_pop = TCSGCPop 1 in  (* Pop the one root we pushed *)
       let pending = e.pending_stmts @ [var_decl] @ cleanup_stmts @ [gc_push] @ final_expr.pending_stmts @ [result_var; gc_pop] in
       mk_expr_lifted_gc (TCELocal result_name) result_type pending 0
     end else begin
       (* Result is GC type - save to temp and push result root.
        * IMPORTANT: We keep BOTH the input and result rooted until the caller
        * finishes using the result. The caller is responsible for popping all
        * roots at the statement boundary.
        *
        * The sequence is:
        *   1. Push input root (e)
        *   2. Save result (derived from input) to temp
        *   3. Push result root
        *   4. Caller uses result
        *   5. Caller pops gc_roots (which we set to 2 = input + result)
        *)
       let result_name = gen_gc_temp_name () in
       let result_var = TCSVar {
         vd_name = result_name;
         vd_type = result_type;
         vd_init = Some final_for_init;
         vd_static = false;
         vd_const = false; vd_volatile = false;
       } in
       
       (* Push result root, keep input root - caller pops both *)
       let result_gc_push = TCSGCPush (mk_expr (TCELocal result_name) result_type) in
       
       let pending = e.pending_stmts @ [var_decl] @ cleanup_stmts @ [gc_push] @ final_expr.pending_stmts @ [result_var; result_gc_push] in
       
       (* Return gc_roots = 2: one for input, one for result *)
       mk_expr_lifted_gc (TCELocal result_name) result_type pending 2
     end
   end

(* Backward-compatible wrapper for wrap_single_gc_extraction *)
let wrap_single_gc_extraction (make_final : tc_expr -> tc_expr) (e : tc_expr) : tc_expr =
  wrap_single_gc_extraction_ctx None make_final e

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
      (* Strip Haxe numeric separators (underscores) which are not valid in C *)
      let s = String.concat "" (String.split_on_char '_' s) in
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
  | TConst TThis when ctx.in_gc_frame && gc_frame_has_var ctx "this" ->
      (* In GCFrame mode, 'this' is accessed through the frame *)
      let this_type = match ctx.current_class_name with
        | Some cn -> TCFibClass cn
        | None -> TCPointer TCVoid
      in
      mk_expr_pos (TCEDot (mk_expr (TCELocal ctx.gc_frame_name) TCVoid, "this")) this_type pos
  | TConst TSuper when ctx.in_gc_frame && gc_frame_has_var ctx "this" ->
      let this_type = match ctx.current_class_name with
        | Some cn -> TCFibClass cn
        | None -> TCPointer TCVoid
      in
      mk_expr_pos (TCEDot (mk_expr (TCELocal ctx.gc_frame_name) TCVoid, "this")) this_type pos
  | TConst c ->
      convert_constant_typed pos tc c
  
  (* Local variable reference *)
  | TLocal v ->
      let name = ident v.v_name in
      (* Check for C-type overrides (e.g. map iterators declared with concrete types) *)
      let vtype = match Hashtbl.find_opt ctx.var_type_overrides v.v_id with
        | Some override_type -> override_type
        | None -> tc_type_of v.v_type
      in
      (* In GCFrame mode, GC-rooted variables are accessed through the frame *)
      if ctx.in_gc_frame && gc_frame_has_var ctx name then
        mk_expr_pos (TCEDot (mk_expr (TCELocal ctx.gc_frame_name) TCVoid, name)) vtype pos
      else
        mk_expr_pos (TCELocal name) vtype pos
  
  (* Parentheses - just unwrap *)
  | TParenthesis inner ->
      convert_expr ctx inner
  
  (* Meta annotations - just unwrap *)
  | TMeta (_, inner) ->
      convert_expr ctx inner
  
  (* Checked type cast: cast(expr, TargetType) - emit runtime instanceof check *)
  | TCast (inner, Some mt) ->
      let inner_expr = convert_expr ctx inner in
      (* Cache inner_expr if it has side effects, since we need it twice
         (once for the check, once for the cast result).
         cache_if_side_effects returns (safe_expr, pending_stmts_including_originals),
         so safe_inner is stripped of pending_stmts -- do not re-include them separately. *)
      let (safe_inner_raw, cache_stmts) = cache_if_side_effects inner_expr in
      (* Strip pending_stmts from safe_inner since they are already in cache_stmts *)
      let safe_inner = { safe_inner_raw with pending_stmts = [] } in
      (* Build the instanceof check statements based on target module_type.
         We emit: if (val != null && !instanceof(val, Target)) throw "Class cast error".
         Only for non-extern classes and interfaces -- other targets fall through. *)
      let check_stmts = match mt with
        | TClassDecl c when not (has_class_flag c CExtern) ->
            let target_class = flat_path c.cl_path in
            (* Build the instanceof check expression based on the value's C type *)
            let instanceof_check = match safe_inner.ctype with
              | TCFibDynamic ->
                  (* Dynamic value: use fib_instanceof_dynamic which handles all type cases.
                     The type argument is a FibDynamic{FIB_TYPE_CLASS, .ptrVal=&Target_class}. *)
                  mk_expr (TCECall (TCTFunc "fib_instanceof_dynamic",
                    [safe_inner;
                     mk_expr (TCERaw (Printf.sprintf
                       "(FibDynamic){.type = FIB_TYPE_CLASS, .data.ptrVal = &%s_class}"
                       target_class)) TCFibDynamic])) TCBool
              | TCFibString | TCInt32 | TCInt64 | TCFloat64 | TCFloat32 | TCBool
              | TCFibClosure | TCFibArray _ | TCVoid ->
                  (* Primitive types can never be instances of a class -- always false *)
                  mk_expr (TCEBool false) TCBool
              | _ ->
                  (* Typed object pointer: cast to FibObject and check class hierarchy *)
                  let cast_obj = mk_expr (TCECast (TCFibObject, safe_inner)) TCFibObject in
                  let class_ptr = mk_expr (TCEAddrOf (mk_expr (TCELocal (target_class ^ "_class")) TCVoid)) (TCPointer TCVoid) in
                  mk_expr (TCECall (TCTFunc "fib_object_instanceof", [cast_obj; class_ptr])) TCBool
            in
            (* Build the "should throw" condition:
               throw when: value is non-null AND does not pass instanceof check.
               Null values are allowed through (cast(null, T) returns null). *)
            let not_instanceof = mk_expr (TCEUnop (TCUNot, instanceof_check)) TCBool in
            let should_throw = match safe_inner.ctype with
              | TCFibDynamic ->
                  (* fib_instanceof_dynamic returns false for null Dynamic values, so
                     !instanceof_dynamic = true for null. We need to exclude that case.
                     Condition: not fib_dynamic_is_null(val) && !instanceof *)
                  let not_null = mk_expr (TCEUnop (TCUNot,
                    mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [safe_inner])) TCBool))
                    TCBool in
                  mk_expr (TCEBinop (TCOpBoolAnd, not_null, not_instanceof)) TCBool
              | _ ->
                  (* For typed object pointers, NULL pointer = null -- pass through *)
                  let is_null = mk_expr (TCEBinop (TCOpEq,
                    mk_expr (TCECast (TCPointer TCVoid, safe_inner)) (TCPointer TCVoid),
                    mk_expr (TCERaw "NULL") (TCPointer TCVoid))) TCBool in
                  let not_null = mk_expr (TCEUnop (TCUNot, is_null)) TCBool in
                  mk_expr (TCEBinop (TCOpBoolAnd, not_null, not_instanceof)) TCBool
            in
            (* Throw expression: "Class cast error" as FibDynamic string *)
            let throw_msg = mk_expr
              (TCECall (TCTFunc "fib_dynamic_string",
                [mk_expr (TCECall (TCTFunc "fib_string_new",
                  [mk_raw_string "Class cast error"])) TCFibString]))
              TCFibDynamic in
            [TCSIf (should_throw, [TCSThrow throw_msg], None)]
        | TAbstractDecl a when Meta.has Meta.RuntimeValue a.a_meta ->
            (* Checked cast to primitive abstract (Int, Float, Bool, Dynamic).
               cast("foo", Int) should throw because String is not an Int.
               Numeric casts between compatible primitives are allowed (Float->Int etc.). *)
            let target_tc = tc_type_of (TAbstract (a, [])) in
            let throw_msg = mk_expr
              (TCECall (TCTFunc "fib_dynamic_string",
                [mk_expr (TCECall (TCTFunc "fib_string_new",
                  [mk_raw_string "Class cast error"])) TCFibString]))
              TCFibDynamic in
            let is_numeric tc = match tc with
              | TCInt32 | TCInt64 | TCFloat64 | TCFloat32 | TCBool | TCChar
              | TCInt8 | TCInt16 | TCUInt8 | TCUInt16 | TCUInt32 | TCUInt64 -> true
              | _ -> false
            in
            (match safe_inner.ctype with
            | TCFibDynamic ->
                (* Dynamic source: check that the dynamic value's type matches the target *)
                let check_fn = match target_tc with
                  | TCInt32 -> "fib_dynamic_is_int"
                  | TCFloat64 | TCFloat32 -> "fib_dynamic_is_float"
                  | TCBool -> "fib_dynamic_is_bool"
                  | _ -> ""  (* Dynamic target: always succeeds *)
                in
                if check_fn = "" then []
                else
                  let is_match = mk_expr (TCECall (TCTFunc check_fn, [safe_inner])) TCBool in
                  let is_null = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [safe_inner])) TCBool in
                  let passes = mk_expr (TCEBinop (TCOpBoolOr, is_null, is_match)) TCBool in
                  let should_throw = mk_expr (TCEUnop (TCUNot, passes)) TCBool in
                  [TCSIf (should_throw, [TCSThrow throw_msg], None)]
            | from_tc when from_tc = target_tc || (is_numeric from_tc && is_numeric target_tc) ->
                (* Source matches target type, or both are numeric (Int->Float etc): no check needed *)
                []
            | _ ->
                (* Source type statically incompatible with target: always throw *)
                [TCSThrow throw_msg])
        | _ ->
            (* Enum casts, extern class casts, TTypeDecl: no runtime check *)
            []
      in
      (* Now apply the normal cast/unbox/box logic to the safe_inner expression *)
      let from_tc = safe_inner.ctype in
      let cast_result =
        if from_tc = tc then
          safe_inner
        else begin
          let result =
            if from_tc = TCFibDynamic then
              mk_expr_pos (TCEUnbox (safe_inner, tc)) tc pos
            else if tc = TCFibDynamic then
              let box_kind = box_kind_of_type from_tc in
              mk_expr_pos (TCEBox (safe_inner, box_kind)) tc pos
            else
              mk_expr_pos (TCECast (tc, safe_inner)) tc pos
          in
          result
        end
      in
      (* Combine: cache stmts + check stmts go into pending_stmts before the value *)
      { cast_result with pending_stmts = cache_stmts @ check_stmts @ cast_result.pending_stmts }

  (* Unchecked type cast: cast expr - no runtime check, just type coercion *)
  | TCast (inner, None) ->
      let inner_expr = convert_expr ctx inner in
      let from_tc = inner_expr.ctype in
      if from_tc = tc then
        inner_expr
      else begin
        let result =
          if from_tc = TCFibDynamic then begin
            (* Unbox from FibDynamic to target type.
               For arrays, fib_dynamic_to_array always returns a generic FibArray*,
               so downgrade specialized targets to generic -- same as coerce_to_type.
               The var-declaration path will register a type override so subsequent
               accesses use the generic path. *)
            let actual_tc = match tc with
              | TCFibArray _ -> TCFibArray TCArrGeneric
              | _ -> tc
            in
            mk_expr_pos (TCEUnbox (inner_expr, actual_tc)) actual_tc pos
          end
          else if tc = TCFibDynamic then
            (* Box to FibDynamic *)
            let box_kind = box_kind_of_type from_tc in
            mk_expr_pos (TCEBox (inner_expr, box_kind)) tc pos
          else
            (* Regular cast *)
            mk_expr_pos (TCECast (tc, inner_expr)) tc pos
        in
        (* Propagate pending_stmts from inner expression *)
        if inner_expr.pending_stmts <> [] then
          { result with pending_stmts = inner_expr.pending_stmts @ result.pending_stmts;
                        gc_roots = inner_expr.gc_roots + result.gc_roots }
        else
          result
      end
  
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
      (* new String(s) is identity — String is immutable in fiberus *)
      else if c.cl_path = ([], "String") then begin
        match args with
        | [arg] ->
            let arg_expr = convert_expr ctx arg in
            coerce_to_type arg_expr TCFibString
        | _ ->
            mk_expr_pos (TCEString "") TCFibString pos
      end
      else begin
        let class_name = flat_path c.cl_path in
        let arg_exprs = List.map (convert_expr ctx) args in
        (* Coerce arguments to constructor parameter types (e.g. Null<Int>/FibDynamic -> Int/int32_t)
           Also substitute default parameter values when null is passed for optional params *)
        let param_types = match c.cl_constructor with
          | Some cf -> get_param_types cf.cf_type
          | None -> []
        in
        let defaults = match c.cl_constructor with
          | Some cf -> begin match cf.cf_expr with
              | Some { Type.eexpr = Type.TFunction f } ->
                  List.map (fun (_, default_opt) -> default_opt) f.tf_args
              | _ -> []
            end
          | None -> []
        in
        let is_null_tc_expr e =
          match e.cexpr with
          | TCENull -> true
          | TCECall (TCTFunc "fib_dynamic_null", []) -> true
          | TCECall (TCTFunc "fib_dynamic_to_int", [{ cexpr = TCECall (TCTFunc "fib_dynamic_null", []) }]) -> true
          | TCECall (TCTFunc "fib_dynamic_to_float", [{ cexpr = TCECall (TCTFunc "fib_dynamic_null", []) }]) -> true
          | TCECall (TCTFunc "fib_dynamic_to_bool", [{ cexpr = TCECall (TCTFunc "fib_dynamic_null", []) }]) -> true
          | _ -> false
        in
        let apply_default a target_tc default_opt =
          if is_null_tc_expr a && target_tc <> TCFibDynamic then
            match default_opt with
            | Some { Type.eexpr = Type.TConst c } -> begin match c with
                | Type.TInt i -> Some (mk_int i)
                | Type.TFloat s -> Some (mk_expr (TCEFloat s) target_tc)
                | Type.TBool b -> Some (mk_expr (TCEBool b) TCBool)
                | Type.TString s -> Some (mk_expr (TCEString s) TCFibString)
                | _ -> None
              end
            | _ -> None
          else None
        in
        let rec coerce_ctor_args aexprs ptypes defs = match aexprs, ptypes, defs with
          | [], _, _ -> []
          | a :: rest_a, pt :: rest_pt, d :: rest_d ->
              let target_tc = tc_type_of pt in
              let coerced = match apply_default a target_tc d with
                | Some default_val -> default_val
                | None -> coerce_to_type a target_tc
              in
              coerced :: coerce_ctor_args rest_a rest_pt rest_d
          | a :: rest_a, pt :: rest_pt, [] ->
              coerce_to_type a (tc_type_of pt) :: coerce_ctor_args rest_a rest_pt []
          | a :: rest_a, [], _ ->
              a :: coerce_ctor_args rest_a [] []
        in
        let coerced_args = coerce_ctor_args arg_exprs param_types defaults in
        let sub_pending = collect_pending coerced_args in
        let sub_gc_roots = sum_gc_roots coerced_args in
        let result = mk_expr_pos (TCENew (class_name, coerced_args)) (TCFibClass class_name) pos in
        if sub_pending <> [] then
          { result with pending_stmts = sub_pending; gc_roots = sub_gc_roots + result.gc_roots }
        else
          result
      end
  
  (* If expression (ternary) *)
  | TIf (cond, ethen, Some eelse) when not (is_void tc) ->
      let cond_expr_raw = convert_expr ctx cond in
      (* Extract bool from FibDynamic condition *)
      let cond_expr = 
        if cond_expr_raw.ctype = TCFibDynamic then
          mk_expr (TCECall (TCTFunc "fib_dynamic_to_bool", [cond_expr_raw])) TCBool
        else
          cond_expr_raw
      in
      let then_expr_raw = convert_expr ctx ethen in
      let else_expr_raw = convert_expr ctx eelse in
      let then_tc = then_expr_raw.ctype in
      let else_tc = else_expr_raw.ctype in
      (* Coerce branches to same type if one is FibDynamic *)
      let then_expr, else_expr, result_tc = 
        if then_tc = TCFibDynamic && else_tc <> TCFibDynamic then
          (then_expr_raw, mk_expr (TCEBox (else_expr_raw, box_kind_of_type else_tc)) TCFibDynamic, TCFibDynamic)
        else if else_tc = TCFibDynamic && then_tc <> TCFibDynamic then
          (mk_expr (TCEBox (then_expr_raw, box_kind_of_type then_tc)) TCFibDynamic, else_expr_raw, TCFibDynamic)
        else
          (then_expr_raw, else_expr_raw, tc)
      in
      (* If either branch has pending_stmts, we CANNOT use a C ternary because
       * hoisting those stmts above the condition breaks short-circuit evaluation.
       * Instead, lower to: { ResultType _tmp; if (cond) _tmp = then; else _tmp = else; }
       * and use _tmp as the expression result. *)
      if then_expr.pending_stmts <> [] || else_expr.pending_stmts <> [] then begin
        let tmp = ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let tmp_name = Printf.sprintf "_gc_tmp%d" tmp in
        let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = result_tc; vd_init = None; vd_static = false; vd_const = false; vd_volatile = false } in
        let then_assign = TCSExpr (mk_expr (TCEAssign (mk_expr (TCELocal tmp_name) result_tc, { then_expr with pending_stmts = [] })) result_tc) in
        let else_assign = TCSExpr (mk_expr (TCEAssign (mk_expr (TCELocal tmp_name) result_tc, { else_expr with pending_stmts = [] })) result_tc) in
        let then_stmts = then_expr.pending_stmts @ [then_assign] in
        let else_stmts = else_expr.pending_stmts @ [else_assign] in
        let cond_clean = { cond_expr with pending_stmts = [] } in
        let if_stmt = TCSIf (cond_clean, then_stmts, Some else_stmts) in
        let all_stmts = cond_expr_raw.pending_stmts @ [tmp_decl; if_stmt] in
        let gc_roots = max then_expr_raw.gc_roots else_expr_raw.gc_roots in
        { (mk_expr_pos_gc (TCELocal tmp_name) result_tc pos gc_roots) with
          pending_stmts = all_stmts;
          gc_roots = cond_expr_raw.gc_roots + gc_roots }
      end else begin
        (* Simple case: no pending_stmts in branches, safe to use C ternary *)
        let gc_roots = max then_expr_raw.gc_roots else_expr_raw.gc_roots in
        let then_expr_clean = { then_expr with pending_stmts = [] } in
        let else_expr_clean = { else_expr with pending_stmts = [] } in
        let result = mk_expr_pos_gc (TCETernary (cond_expr, then_expr_clean, else_expr_clean)) result_tc pos gc_roots in
        { result with 
          pending_stmts = cond_expr_raw.pending_stmts @ result.pending_stmts;
          gc_roots = cond_expr_raw.gc_roots + gc_roots }
      end
  
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
      (* If inner is FibDynamic (Dynamic variable, anon field, etc.), use helper function
         since FibDynamic has no .index field *)
      if inner_expr.ctype = TCFibDynamic then
        mk_expr_pos (TCECall (TCTFunc "fib_enum_index", [inner_expr])) TCInt32 pos
      else
        mk_expr_pos (TCEEnumIndex inner_expr) TCInt32 pos
  
  (* Enum parameter access *)
  | TEnumParameter (inner, _, idx) ->
      let inner_expr = convert_expr ctx inner in
      let param_access = mk_expr_pos (TCEEnumParam (inner_expr, idx)) TCFibDynamic pos in
      let param_access =
        if inner_expr.pending_stmts <> [] then
          { param_access with pending_stmts = inner_expr.pending_stmts; gc_roots = inner_expr.gc_roots }
        else param_access
      in
      (* Unbox from FibDynamic if target type isn't FibDynamic *)
      if tc = TCFibDynamic then
        param_access
      else begin
        let result = mk_expr_pos (TCEUnbox (param_access, tc)) tc pos in
        if param_access.pending_stmts <> [] then
          { result with pending_stmts = param_access.pending_stmts; gc_roots = param_access.gc_roots + result.gc_roots }
        else result
      end
  
  (* Raw identifier (used for __fiberus__ and similar) *)
  | TIdent s ->
      mk_expr_pos (TCELocal (ident s)) tc pos
  
  (* Type expression - emit as type descriptor reference.
     When target type is FibDynamic (e.g. Type.typeof / Type.getEnum comparisons),
     wrap in a FibDynamic struct with FIB_TYPE_CLASS pointing to the descriptor:
     - For enums: points to &name_meta (FibEnumMeta)
     - For classes: points to &name_class (FibClassDescriptor)
     Otherwise emit as a bare identifier for static field access etc. *)
  | TTypeExpr mt ->
      let path = Type.t_path mt in
      let name = flat_path path in
      if tc = TCFibDynamic then
        (match mt with
        | TEnumDecl _ ->
          mk_expr_pos (TCERaw (Printf.sprintf "(FibDynamic){ .type = FIB_TYPE_CLASS, .data = { .ptrVal = (void*)&%s_meta } }" name)) TCFibDynamic pos
        | _ ->
          mk_expr_pos (TCERaw (Printf.sprintf "(FibDynamic){ .type = FIB_TYPE_CLASS, .data = { .ptrVal = &%s_class } }" name)) TCFibDynamic pos)
      else
        mk_expr_pos (TCELocal name) tc pos
  
  (* Function expression - create a closure *)
  | TFunction f ->
      (* Find free variables that need to be captured *)
      let free_vars = FiberusClosure.find_free_vars f in
      let closure_name = fresh_closure_name ctx in
      let impl_name = closure_name ^ "_impl" in
      let arg_count = List.length f.tf_args in
      
      (* Convert captured variables to (capture_expr, var_name, type) triples.
         capture_expr: the C expression to read the value at closure creation
         site — uses _gc.name if the variable is in the enclosing GC frame.
         var_name: the bare name used inside the closure body for extraction. *)
      let captures = List.map (fun v ->
        let name = ident v.v_name in
        let capture_expr =
          if ctx.in_gc_frame && gc_frame_has_var ctx name then
            Printf.sprintf "%s.%s" ctx.gc_frame_name name
          else name
        in
        (capture_expr, name, tc_type_of v.v_type)
      ) free_vars in
      (* If the closure body references 'this', add it as a capture.
         'this' is not a TLocal so find_free_vars doesn't detect it. *)
      let captures_this = FiberusClosure.uses_this f in
      let this_tc = match ctx.current_class_name with
        | Some cn -> TCFibClass cn
        | None -> TCFibObject
      in
      let this_capture_expr = if ctx.in_gc_frame && gc_frame_has_var ctx "this" then
        Printf.sprintf "%s.this" ctx.gc_frame_name
      else "this" in
      let captures = if captures_this then
        (this_capture_expr, "this", this_tc) :: captures
      else
        captures
      in
      
      (* Convert the function body to C-AST with GCFrame tracking.
       * Closure bodies get their own GCFrame containing _closure, GC-typed
       * params, and GC-typed captures. The frame declaration, capture extraction,
       * and cleanup are included in cl_body so write_closure_impl just emits them. *)
      let ret_type = tc_type_of f.tf_type in
      (* Derive parameter types from the function expression's unified type (e.etype)
         rather than individual v.v_type. The expression type reflects unification with
         call sites (e.g., var f = function(x) ...; r.map(s, f) unifies x's type with EReg),
         while v.v_type may remain as a structural TAnon -> TCFibDynamic.
         Fall back to v.v_type when e.etype is unavailable or mismatched. *)
      let unified_param_types = match Type.follow e.etype with
        | Type.TFun (params, _) ->
          let types = List.map (fun (_, _, t) -> tc_type_of t) params in
          if List.length types = List.length f.tf_args then Some types else None
        | _ -> None
      in
      let args_with_defaults = List.mapi (fun i (v, default_opt) ->
        let fa_type = match unified_param_types with
          | Some types -> List.nth types i
          | None -> tc_type_of v.v_type
        in
        ({ fa_name = ident v.v_name; fa_type }, default_opt)
      ) f.tf_args in
      let args = List.map fst args_with_defaults in
      let cl_captures_list = List.mapi (fun i (_, name, typ) ->
        { cap_var = name; cap_type = typ; cap_index = i }
      ) captures in
      let frame_name = "_gc" in
      let frame_rooted_vars = Hashtbl.create 16 in
      let param_inits = ref [] in
      let initial_slots = ref [] in
      (* Always root _closure *)
      initial_slots := ("_closure", TCFibClosure) :: !initial_slots;
      Hashtbl.replace frame_rooted_vars "_closure" ();
      param_inits := ("_closure", mk_expr (TCELocal "_closure") TCFibClosure) :: !param_inits;
      (* GC-typed parameters.
         For optional parameters with non-null defaults, substitute the default
         when the param is null at runtime (mirrors class method path at line ~5920).
         Handles both FibDynamic params (boxed defaults) and enum params (index sentinel). *)
      List.iter (fun (arg, default_opt) ->
        if needs_gc_root arg.fa_type then begin
          initial_slots := (arg.fa_name, arg.fa_type) :: !initial_slots;
          Hashtbl.replace frame_rooted_vars arg.fa_name ();
          let init_expr = mk_expr (TCELocal arg.fa_name) arg.fa_type in
          let init_expr = match arg.fa_type, default_opt with
          | TCFibDynamic, Some { Type.eexpr = Type.TConst c } when c <> Type.TNull ->
              let boxed_default = match c with
                | Type.TInt i -> mk_expr (TCEBox (mk_expr (TCEInt i) TCInt32, TCBoxInt)) TCFibDynamic
                | Type.TFloat s -> mk_expr (TCEBox (mk_expr (TCEFloat s) TCFloat64, TCBoxFloat)) TCFibDynamic
                | Type.TBool b -> mk_expr (TCEBox (mk_expr (TCEBool b) TCBool, TCBoxBool)) TCFibDynamic
                | Type.TString s -> mk_expr (TCEBox (mk_expr (TCEString s) TCFibString, TCBoxString)) TCFibDynamic
                | _ -> init_expr
              in
              if boxed_default != init_expr then
                let null_check = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [init_expr])) TCBool in
                mk_expr (TCETernary (null_check, boxed_default, init_expr)) TCFibDynamic
              else init_expr
          | TCFibDynamic, Some default_e when (match default_e.Type.eexpr with Type.TConst Type.TNull -> false | _ -> true) ->
              (* Non-constant default for FibDynamic param: convert and box *)
              let converted = convert_expr ctx default_e in
              let boxed = coerce_to_type converted TCFibDynamic in
              let null_check = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [init_expr])) TCBool in
              mk_expr (TCETernary (null_check, boxed, init_expr)) TCFibDynamic
          | TCFibEnum _, Some default_e when (match default_e.Type.eexpr with Type.TConst Type.TNull -> false | _ -> true) ->
              (* Enum param with non-null default: check for null sentinel (index == -1) *)
              let converted = convert_expr ctx default_e in
              let index_field = mk_expr (TCERaw (arg.fa_name ^ ".index")) TCInt32 in
              let null_check = mk_expr (TCEBinop (TCOpEq, index_field, mk_expr (TCEUnop (TCUNeg, mk_expr (TCEInt 1l) TCInt32)) TCInt32)) TCBool in
              mk_expr (TCETernary (null_check, converted, init_expr)) arg.fa_type
          | _ -> init_expr
          in
          param_inits := (arg.fa_name, init_expr) :: !param_inits
        end
      ) args_with_defaults;
      (* GC-typed captures — registered as slots, initialized to NULL (assigned after extraction) *)
      List.iter (fun cap ->
        if needs_gc_root cap.cap_type then begin
          initial_slots := (cap.cap_var, cap.cap_type) :: !initial_slots;
          Hashtbl.replace frame_rooted_vars cap.cap_var ()
        end
      ) cl_captures_list;
      let body_ctx = { (ctx_for_scope ctx) with 
        current_ret_type = Some ret_type;
        closures = [];
        in_gc_frame = true;
        gc_frame_name = frame_name;
        gc_frame_slots = List.rev !initial_slots;
        gc_frame_rooted_vars = frame_rooted_vars;
        func_gc_root_count = 0;
        gc_local_count = 0;  (* Reset: closure has its own temp root scope *)
      } in
      let body_stmts = convert_stmt body_ctx f.tf_expr in
      let body_stmts = mark_volatile_for_try body_stmts in
      (* For non-GC enum params with defaults, emit null-sentinel substitution.
         These are value-type params not tracked in the GC frame but need
         their default applied when the caller passes the null sentinel. *)
      let enum_default_stmts = List.filter_map (fun (arg, default_opt) ->
        match arg.fa_type, default_opt with
        | TCFibEnum _, Some default_e when (match default_e.Type.eexpr with Type.TConst Type.TNull -> false | _ -> true) ->
            let converted = convert_expr ctx default_e in
            let index_field = mk_expr (TCERaw (arg.fa_name ^ ".index")) TCInt32 in
            let null_check = mk_expr (TCEBinop (TCOpEq, index_field, mk_expr (TCEUnop (TCUNeg, mk_expr (TCEInt 1l) TCInt32)) TCInt32)) TCBool in
            let assign = TCSExpr (mk_expr (TCEAssign (mk_expr (TCELocal arg.fa_name) arg.fa_type, converted)) arg.fa_type) in
            Some (TCSIf (null_check, [assign], None))
        | _ -> None
      ) args_with_defaults in
      let body_stmts = enum_default_stmts @ body_stmts in
      (* Build prologue: FIB_GC_CTX + GCFrame + capture extraction *)
      let prologue = ref [TCSGCCtx] in
      (* Suppress -Wunused-parameter for scalar (non-GC) closure args *)
      List.iter (fun arg ->
        if not (Hashtbl.mem frame_rooted_vars arg.fa_name) then
          prologue := !prologue @ [TCSExpr (mk_expr (TCECast (TCVoid, mk_expr (TCELocal arg.fa_name) arg.fa_type)) TCVoid)]
      ) args;
      let frame_info = gc_frame_build_info_with_inits body_ctx !param_inits in
      let has_gc_slots = frame_info.gfi_slots <> [] in
      if has_gc_slots then
        prologue := !prologue @ [TCSGCFrameDecl frame_info];
      if captures = [] then
        prologue := !prologue @ [TCSRaw "(void)_closure;"];
      (* Extract captured variables into locals, assign to frame if GC-typed *)
      List.iter (fun cap ->
        let extract_str = FiberusSourceWriter.capture_extract_expr cap in
        prologue := !prologue @ [TCSVar {
          vd_name = cap.cap_var; vd_type = cap.cap_type;
          vd_init = Some (mk_expr (TCERaw extract_str) cap.cap_type);
          vd_static = false; vd_const = false; vd_volatile = false;
        }];
        if needs_gc_root cap.cap_type then
          prologue := !prologue @ [TCSGCFrameAssign (frame_name, cap.cap_var, mk_expr (TCELocal cap.cap_var) cap.cap_type)]
      ) cl_captures_list;
      (* Epilogue: pop any legacy temp roots (from stack-alloc fields) + GC_FRAME_POP for fall-through *)
      let epilogue = if ret_type = TCVoid && not (ends_with_return f.tf_expr) then begin
        let temp_pop = if body_ctx.gc_local_count > 0 then [TCSGCPop body_ctx.gc_local_count] else [] in
        let frame_pop = if has_gc_slots then [TCSGCFramePop frame_name] else [] in
        temp_pop @ frame_pop
      end else [] in
      let full_body = !prologue @ body_stmts @ epilogue in
      (* Sync any nested closures from body back to outer context *)
      ctx.closures <- body_ctx.closures @ ctx.closures;
      
      (* Register the closure for later implementation generation *)
      (* Build default expressions for the wrapper function.
         For primitive-typed args (int32_t, float, bool), the wrapper must check
         if the FibDynamic arg is null and substitute the default value, because
         the _impl function receives the already-unboxed typed value. *)
      let defaults = List.map (fun (arg, default_opt) ->
        match arg.fa_type, default_opt with
        | (TCInt32 | TCFloat64 | TCFloat32 | TCBool | TCInt64 | TCUInt8 | TCUInt16 | TCUInt32 | TCUInt64 | TCInt8 | TCInt16 | TCChar | TCSizeT), Some default_e
            when (match default_e.Type.eexpr with Type.TConst Type.TNull -> false | _ -> true) ->
            Some (convert_expr ctx default_e)
        | _ -> None
      ) args_with_defaults in
      let closure_def = {
        cl_id = ctx.closure_counter - 1;  (* ID was incremented by fresh_closure_name *)
        cl_name = closure_name;
        cl_impl_name = impl_name;
        cl_args = args;
        cl_ret = ret_type;
        cl_captures = cl_captures_list;
        cl_body = full_body;
        cl_defaults = defaults;
      } in
      ctx.closures <- closure_def :: ctx.closures;
      
      (* Return the closure creation expression *)
      mk_expr_pos (TCEClosureCreate {
        cc_name = closure_name;
        cc_impl_name = impl_name;
        cc_captures = captures;
        cc_arg_count = arg_count;
        cc_for_fiber = ctx.in_fiber_spawn;
      }) TCFibClosure pos
  
  (* For remaining unhandled cases, emit raw placeholder *)
  | TVar _ | TWhile _ | TSwitch _ | TTry _ | TBreak | TContinue | TThrow _ ->
      (* These are statements, not value expressions - shouldn't reach here in value context *)
      mk_expr_pos (TCERaw (Printf.sprintf "/* stmt in expr context: %s */" (Type.s_expr_kind e))) tc pos
  
  | TObjectDecl fl ->
      (* Anonymous object declaration *)
      if fl = [] then
        mk_expr_pos (TCECall (TCTFunc "fib_anon_new", [])) TCFibDynamic pos
      else begin
        (* Build list of field assignments for TCEAnonObject *)
        let fields_with_pending = List.map (fun ((name, _, _), field_e) ->
          let field_expr = convert_expr ctx field_e in
          (* Box to FibDynamic based on type *)
          let box_kind = box_kind_of_type field_expr.ctype in
          let boxed = match box_kind with
            | TCBoxDynamic -> field_expr  (* Already FibDynamic *)
            | TCBoxString ->
              let b = mk_expr (TCECall (TCTFunc "fib_string_to_dynamic", [field_expr])) TCFibDynamic in
              if field_expr.pending_stmts <> [] then
                { b with pending_stmts = field_expr.pending_stmts; gc_roots = field_expr.gc_roots }
              else b
            | _ ->
              let b = mk_expr (TCEBox (field_expr, box_kind)) TCFibDynamic in
              if field_expr.pending_stmts <> [] then
                { b with pending_stmts = field_expr.pending_stmts; gc_roots = field_expr.gc_roots }
              else b
          in
          (* Extract allocating field values to rooted temps so they survive GC
             triggered by subsequent field evaluations or the anon alloc itself.
             FIB_ANON_HEAP_N evaluates all field args inline in a single C expression,
             so intermediate GC-allocated values are not rooted between allocations.
             Note: extract_if_allocating_ctx already includes boxed.pending_stmts in
             the returned extra_stmts, so we use extra_stmts directly (not prepending
             boxed.pending_stmts again). *)
          let (boxed', extra_stmts, extra_roots) = extract_if_allocating_ctx (Some ctx) boxed in
          let boxed' = if extra_stmts <> [] then
            { boxed' with pending_stmts = extra_stmts; gc_roots = extra_roots }
          else boxed in
          (name, boxed')
        ) fl in
        (* Collect pending_stmts from all field values — they must be emitted before
           the FIB_ANON_HEAP macro call since macro args are evaluated as a single expression *)
        let all_pending = List.concat_map (fun (_, boxed) -> boxed.pending_stmts) fields_with_pending in
        let all_gc_roots = List.fold_left (fun acc (_, boxed) -> acc + boxed.gc_roots) 0 fields_with_pending in
        let fields = List.map (fun (name, boxed) -> (name, { boxed with pending_stmts = []; gc_roots = 0 })) fields_with_pending in
        (* Always heap-allocate: stack-alloc anon objects become dangling when
           stored in arrays, fields, or any location outliving the current expression *)
        let result = mk_expr_pos (TCEAnonObject (fields, true)) TCFibDynamic pos in
        { result with pending_stmts = all_pending; gc_roots = all_gc_roots }
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
      (* else_expr has no gc_roots, so just use then_expr's gc_roots *)
      mk_expr_pos_gc (TCETernary (cond_expr, then_expr, else_expr)) TCFibDynamic pos then_expr.gc_roots
  
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
  
  (* Array.length assignment -> resize call *)
  | OpAssign when (match e1.Type.eexpr with
      | Type.TField (obj, Type.FInstance (_, _, cf)) ->
          cf.cf_name = "length" && FiberusBuiltins.is_array_type obj.Type.etype
      | _ -> false) ->
      let obj = (match e1.Type.eexpr with Type.TField (obj, _) -> obj | _ -> assert false) in
      let arr_kind = get_array_kind obj.Type.etype in
      let prefix = array_kind_prefix arr_kind in
      let arr_expr = convert_expr ctx obj in
      let val_expr = convert_expr ctx e2 in
      mk_expr_inherit (TCECall (TCTFunc (prefix ^ "resize"), [arr_expr; val_expr])) TCVoid [arr_expr; val_expr]
  
  (* Field assignment - may need write barrier *)
  | OpAssign when (match e1.Type.eexpr with Type.TField (_, Type.FInstance _) -> true | _ -> false) ->
      convert_field_assign ctx e1 e2 pos
  
  (* Stack-allocated variable reassignment: reinitialize struct in-place via compound literal *)
  | OpAssign when (match e1.Type.eexpr with
      | Type.TLocal v -> Hashtbl.mem ctx.stack_alloc_vars v.v_id
      | _ -> false) ->
      let v = (match e1.Type.eexpr with Type.TLocal v -> v | _ -> assert false) in
      let name = ident v.v_name in
      let c = Hashtbl.find ctx.stack_alloc_vars v.v_id in
      let class_name = flat_path c.cl_path in
      let result_type = TCFibClass class_name in
      (match e2.Type.eexpr with
      | Type.TNew (tc, _, args) ->
          (* Reset struct via compound literal, then call _init to run full constructor logic.
           * Previous approach tried to inline field assignments from constructor into the
           * compound literal, but that misses any constructor logic beyond simple field
           * assignments (e.g. StringBuf's this.b = fib_strbuf_new()). *)
          let compound_lit = Printf.sprintf "_stack_%s = (%s){ ._obj.clazz = &%s_class }"
            name class_name class_name in
          (* Build init call with constructor arguments, matching convert_tvar_stmt logic *)
          let init_args, args_pending = if List.length args > 0 then begin
            let arg_exprs = List.map (convert_expr ctx) args in
            let pending = collect_pending arg_exprs in
            let param_types = match tc.cl_constructor with
              | Some cf -> get_param_types cf.cf_type
              | None -> []
            in
            let rec coerce_args aexprs ptypes = match aexprs, ptypes with
              | [], _ -> []
              | a :: rest_a, pt :: rest_pt ->
                  coerce_to_type { a with pending_stmts = [] } (tc_type_of pt) :: coerce_args rest_a rest_pt
              | a :: rest_a, [] ->
                  { a with pending_stmts = [] } :: coerce_args rest_a []
            in
            (coerce_args arg_exprs param_types, pending)
          end else ([], []) in
          let this_arg = mk_expr (TCELocal name) (TCFibClass class_name) in
          let init_call = TCSExpr (mk_expr (TCECall (TCTFunc (class_name ^ "_init"), this_arg :: init_args)) TCVoid) in
          let reset_stmt = TCSRaw (compound_lit ^ ";") in
          { (mk_expr_pos (TCELocal name) result_type pos) with
            pending_stmts = args_pending @ [reset_stmt; init_call] }
      | _ ->
          (* Fallback: regular assignment (shouldn't normally happen for stack-alloc vars) *)
          let e1_expr = convert_expr ctx e1 in
          let e2_expr = convert_expr ctx e2 in
          let assign = mk_expr_pos (TCEAssign (e1_expr, e2_expr)) e1_expr.ctype pos in
          { assign with
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_expr.gc_roots })
  
  (* Anonymous/dynamic field assignment: obj.field = value -> fib_anon_set *)
  | OpAssign when (match e1.Type.eexpr with
      | Type.TField (_, (Type.FAnon _ | Type.FDynamic _)) -> true
      | _ -> false) ->
      convert_anon_field_assign ctx e1 e2 pos

  (* Regular assignment with FibDynamic boxing if needed *)
  | OpAssign ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let rhs = box_if_needed e1_expr.ctype e2_expr in
      (* Static field assignment: if a Dynamic array is assigned to an Array<Int>
         static field, convert generic elements to preserve correct reads. *)
      let rhs = match e1.Type.eexpr, e1_expr.ctype, rhs.ctype with
        | Type.TField (_, Type.FStatic _), TCFibArray TCArrInt, TCFibArray TCArrGeneric ->
            let conv = mk_expr (TCECall (TCTFunc "fib_array_to_int_array", [rhs])) e1_expr.ctype in
            if rhs.pending_stmts <> [] then
              { conv with pending_stmts = rhs.pending_stmts; gc_roots = rhs.gc_roots + conv.gc_roots }
            else conv
        | _ -> rhs
      in
      (* Check if RHS is an assignment that may modify the same lvalue.
         In C, (x = (x += 1)) is undefined behavior — sequence via temporary. *)
      let rhs_is_assign = match e2.Type.eexpr with
        | Type.TBinop (Ast.OpAssignOp _, _, _) | Type.TBinop (Ast.OpAssign, _, _) -> true
        | _ -> false
      in
      if rhs_is_assign then begin
        let tmp_name = Printf.sprintf "_seq_%d" ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let tmp_var = TCSVar { vd_name = tmp_name; vd_type = rhs.ctype; vd_init = Some rhs;
          vd_static = false; vd_const = false; vd_volatile = false } in
        let tmp_ref = mk_expr (TCELocal tmp_name) rhs.ctype in
        let assign = mk_expr_pos (TCEAssign (e1_expr, tmp_ref)) e1_expr.ctype pos in
        { assign with
          pending_stmts = e1_expr.pending_stmts @ rhs.pending_stmts @ [tmp_var];
          gc_roots = e1_expr.gc_roots + rhs.gc_roots }
      end else begin
        (* Propagate pending_stmts from both sides *)
        let assign = mk_expr_pos (TCEAssign (e1_expr, rhs)) e1_expr.ctype pos in
        { assign with 
          pending_stmts = e1_expr.pending_stmts @ rhs.pending_stmts @ assign.pending_stmts;
          gc_roots = e1_expr.gc_roots + rhs.gc_roots }
      end
  
  (* Unsigned right shift assignment *)
  | OpAssignOp OpUShr ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let is_int64 = e1_expr.ctype = TCInt64 in
      let target_signed = if is_int64 then TCInt64 else TCInt32 in
      let target_unsigned = if is_int64 then TCUInt64 else TCUInt32 in
      let e1_ex = extract_fib_dynamic e1_expr target_signed in
      let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
      (* Mask shift amount to avoid C undefined behavior: & 63 for 64-bit, & 31 for 32-bit *)
      let mask_bits = if is_int64 then 63 else 31 in
      let e2_masked = mk_expr (TCEBinop (TCOpAnd, e2_ex, mk_int (Int32.of_int mask_bits))) TCInt32 in
      let unsigned = mk_expr (TCECast (target_unsigned, e1_ex)) target_unsigned in
      let shifted = mk_expr (TCEBinop (TCOpShr, unsigned, e2_masked)) target_unsigned in
      let result = mk_expr (TCECast (target_signed, shifted)) target_signed in
      let final_result = 
        if e1_expr.ctype = TCFibDynamic then begin
          let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [result])) TCFibDynamic in
          mk_expr_pos (TCEAssign (e1_expr, boxed)) TCFibDynamic pos
        end else
          mk_expr_pos (TCEAssign (e1_expr, result)) target_signed pos
      in
      (* Propagate pending_stmts from both operands *)
      { final_result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ final_result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
  
  (* Array compound assignment: arr[i] op= value *)
  | OpAssignOp inner_op when (match e1.Type.eexpr with Type.TArray _ -> true | _ -> false) ->
      convert_array_compound_assign ctx inner_op e1 e2 pos
  
  (* String compound assignment: s += "str" - with GC safety *)
  | OpAssignOp OpAdd when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = ensure_string ctx e1 e1_expr in
      let s2 = ensure_string ctx e2 e2_expr in
      (* Use GC-safe wrapper for the concat, then assign.
       * IMPORTANT: The concat expression may have pending_stmts from GC extraction
       * that must be propagated to the final assignment expression. *)
      let concat = wrap_with_gc_extraction_ctx (Some ctx)
        (fun a b -> mk_expr (TCEStringConcat (a, b)) TCFibString)
        s1 s2 in
      (* Propagate pending_stmts from concat to the assign expression *)
      let assign = mk_expr_pos (TCEAssign (e1_expr, concat)) TCFibString pos in
      { assign with 
        pending_stmts = concat.pending_stmts @ assign.pending_stmts;
        gc_roots = concat.gc_roots }
  
  (* FibDynamic compound assignment: dyn op= value *)
  | OpAssignOp inner_op when (tc_type_of e1.Type.etype) = TCFibDynamic
      && (match e1.Type.eexpr with Type.TField (_, (Type.FAnon _ | Type.FDynamic _)) -> false | _ -> true) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      (* For OpAdd, use fib_dynamic_add which handles string concat at runtime *)
      if inner_op = Ast.OpAdd then begin
        let e2_dyn = coerce_to_type e2_expr TCFibDynamic in
        (* Check for nested compound assignment — must save LHS before inner modifies it *)
        let is_nested_assign = match e2.Type.eexpr with
          | Type.TBinop (Ast.OpAssignOp _, _, _) | Type.TBinop (Ast.OpAssign, _, _) -> true
          | _ -> false
        in
        if is_nested_assign then begin
          let save_name = Printf.sprintf "_cmpd_%d" ctx.temp_counter in
          ctx.temp_counter <- ctx.temp_counter + 1;
          let save_var = TCSVar { vd_name = save_name; vd_type = TCFibDynamic; vd_init = Some e1_expr; vd_static = false; vd_const = false; vd_volatile = false } in
          let save_ref = mk_expr (TCELocal save_name) TCFibDynamic in
          let result = mk_expr (TCECall (TCTFunc "fib_dynamic_add", [save_ref; e2_dyn])) TCFibDynamic in
          let assign = mk_expr_pos (TCEAssign (e1_expr, result)) TCFibDynamic pos in
          { assign with 
            pending_stmts = e1_expr.pending_stmts @ [save_var] @ e2_dyn.pending_stmts @ assign.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_dyn.gc_roots }
        end else begin
          let result = mk_expr (TCECall (TCTFunc "fib_dynamic_add", [e1_expr; e2_dyn])) TCFibDynamic in
          let assign = mk_expr_pos (TCEAssign (e1_expr, result)) TCFibDynamic pos in
          { assign with 
            pending_stmts = e1_expr.pending_stmts @ e2_dyn.pending_stmts @ assign.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_dyn.gc_roots }
        end
      end else begin
        let e1_ex = extract_fib_dynamic e1_expr TCInt32 in
        let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
        let c_op = convert_binop inner_op in
        (* Check for nested compound assignment — same UB issue as regular case *)
        let is_nested_assign = match e2.Type.eexpr with
          | Type.TBinop (Ast.OpAssignOp _, _, _) | Type.TBinop (Ast.OpAssign, _, _) -> true
          | _ -> false
        in
        if is_nested_assign then begin
          (* Save outer LHS extracted value before inner assignment *)
          let save_name = Printf.sprintf "_cmpd_%d" ctx.temp_counter in
          ctx.temp_counter <- ctx.temp_counter + 1;
          let save_var = TCSVar { vd_name = save_name; vd_type = TCInt32; vd_init = Some e1_ex; vd_static = false; vd_const = false; vd_volatile = false } in
          let save_ref = mk_expr (TCELocal save_name) TCInt32 in
          (* Evaluate inner and save its result *)
          let rhs_name = Printf.sprintf "_cmpd_%d" ctx.temp_counter in
          ctx.temp_counter <- ctx.temp_counter + 1;
          let rhs_var = TCSVar { vd_name = rhs_name; vd_type = TCInt32; vd_init = Some e2_ex; vd_static = false; vd_const = false; vd_volatile = false } in
          let rhs_ref = mk_expr (TCELocal rhs_name) TCInt32 in
          (* Compute outer: lhs = box(saved op rhs_result) *)
          let result = mk_expr (TCEBinop (c_op, save_ref, rhs_ref)) TCInt32 in
          let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [result])) TCFibDynamic in
          let assign = mk_expr_pos (TCEAssign (e1_expr, boxed)) TCFibDynamic pos in
          { assign with
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ e1_ex.pending_stmts @ e2_ex.pending_stmts @ [save_var; rhs_var] }
        end else begin
          let result = mk_expr (TCEBinop (c_op, e1_ex, e2_ex)) TCInt32 in
          let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [result])) TCFibDynamic in
          let assign = mk_expr_pos (TCEAssign (e1_expr, boxed)) TCFibDynamic pos in
          (* Propagate pending_stmts from both operands *)
          { assign with 
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ assign.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
        end
      end
  
  (* Anonymous/dynamic field compound assignment: obj.field op= value -> fib_anon_set *)
  | OpAssignOp inner_op when (match e1.Type.eexpr with
      | Type.TField (_, (Type.FAnon _ | Type.FDynamic _)) -> true
      | _ -> false) ->
      convert_anon_field_compound_assign ctx inner_op e1 e2 pos

  (* Compound assignment on generically-stored field: field stored as FibDynamic but
     accessed as concrete type. The unboxed result is an rvalue, so use read-modify-write.
     Cache obj_expr if it has side effects since field_expr is used in both read and write. *)
  | OpAssignOp inner_op when (match e1.Type.eexpr with
      | Type.TField (_, Type.FInstance (_, _, cf)) ->
          let storage_tc = tc_type_of cf.cf_type in
          storage_tc = TCFibDynamic && tc_type_of e1.Type.etype <> TCFibDynamic
      | _ -> false) ->
      let obj_expr_raw, obj_pre_pending, cf_name = match e1.Type.eexpr with
        | Type.TField (obj, Type.FInstance (c, _, cf)) ->
            let obj_expr = convert_expr ctx obj in
            let class_name = flat_path c.cl_path in
            if obj_expr.ctype <> TCFibClass class_name then
              let cast = mk_expr (TCECast (TCFibClass class_name, { obj_expr with pending_stmts = [] })) (TCFibClass class_name) in
              (cast, obj_expr.pending_stmts, ident cf.cf_name)
            else
              (obj_expr, [], ident cf.cf_name)
        | _ -> assert false
      in
      (* cache_if_side_effects includes obj_expr_raw.pending_stmts in obj_cache *)
      let obj_safe, obj_cache = cache_if_side_effects obj_expr_raw in
      let field_expr = mk_expr (TCEArrow (obj_safe, cf_name)) TCFibDynamic in
      let elem_tc = tc_type_of e1.Type.etype in
      let extract_func = match elem_tc with TCFloat64 -> "fib_dynamic_to_float" | _ -> "fib_dynamic_to_int" in
      let extract = mk_expr (TCECall (TCTFunc extract_func, [field_expr])) elem_tc in
      let e2_expr = convert_expr ctx e2 in
      let c_op = convert_binop inner_op in
      let computed = mk_expr (TCEBinop (c_op, extract, e2_expr)) elem_tc in
      (* Store computed value in temp, assign to field, return temp *)
      let tmp_name = gen_gc_temp_name () in
      let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = elem_tc; vd_init = Some computed;
        vd_static = false; vd_const = false; vd_volatile = false } in
      let tmp_ref = mk_expr (TCELocal tmp_name) elem_tc in
      let box_func = match elem_tc with TCFloat64 -> "fib_dynamic_float" | _ -> "fib_dynamic_int" in
      let boxed = mk_expr (TCECall (TCTFunc box_func, [tmp_ref])) TCFibDynamic in
      let assign = TCSExpr (mk_expr (TCEAssign (field_expr, boxed)) TCFibDynamic) in
      { (mk_expr_pos (TCELocal tmp_name) elem_tc pos) with
        pending_stmts = obj_pre_pending @ obj_cache @ e2_expr.pending_stmts @ [tmp_decl; assign] }

  (* Regular compound assignment *)
  | OpAssignOp inner_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let e2_ex = extract_fib_dynamic e2_expr e1_expr.ctype in
      let c_op = convert_binop inner_op in
      (* For shift operations, mask the RHS to avoid C undefined behavior *)
      let is_shift = (inner_op = Ast.OpShl || inner_op = Ast.OpShr) in
      let mask_shift_amount e2_val =
        if is_shift then
          let is_int64 = (e1_expr.ctype = TCInt64) in
          let mask_bits = if is_int64 then 63 else 31 in
          mk_expr (TCEBinop (TCOpAnd, e2_val, mk_int (Int32.of_int mask_bits))) TCInt32
        else e2_val
      in
      (* Check if RHS is itself an assignment (nested compound assign).
         In C, (x += (x += 1)) is undefined behavior because x is read and
         written without a sequence point. We must sequence via temporaries. *)
      let is_nested_assign = match e2.Type.eexpr with
        | Type.TBinop (Ast.OpAssignOp _, _, _) | Type.TBinop (Ast.OpAssign, _, _) -> true
        | _ -> false
      in
      if is_nested_assign then begin
        (* Save outer LHS value before inner assignment modifies it *)
        let save_name = Printf.sprintf "_cmpd_%d" ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let save_var = TCSVar { vd_name = save_name; vd_type = e1_expr.ctype; vd_init = Some e1_expr; vd_static = false; vd_const = false; vd_volatile = false } in
        let save_ref = mk_expr (TCELocal save_name) e1_expr.ctype in
        (* Evaluate inner compound assign and save its result *)
        let rhs_name = Printf.sprintf "_cmpd_%d" ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let rhs_var = TCSVar { vd_name = rhs_name; vd_type = e2_ex.ctype; vd_init = Some e2_ex; vd_static = false; vd_const = false; vd_volatile = false } in
        let rhs_ref = mk_expr (TCELocal rhs_name) e2_ex.ctype in
        (* Compute outer: lhs = saved_lhs op rhs_result *)
        let sum = mk_expr (TCEBinop (c_op, save_ref, mask_shift_amount rhs_ref)) e1_expr.ctype in
        let assign = mk_expr_pos (TCEAssign (e1_expr, sum)) e1_expr.ctype pos in
        { assign with
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ e2_ex.pending_stmts @ [save_var; rhs_var] }
      end else if inner_op = Ast.OpMod && (e1_expr.ctype = TCFloat64 || e1_expr.ctype = TCFloat32) then begin
        (* Float %= needs fmod: x = fmod(x, y) since C % doesn't work on doubles *)
        let fmod_call = mk_expr (TCECall (TCTFunc "fmod", [e1_expr; e2_ex])) TCFloat64 in
        let result = mk_expr_pos (TCEAssign (e1_expr, fmod_call)) e1_expr.ctype pos in
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end else begin
        let e2_final = mask_shift_amount e2_ex in
        let result = mk_expr_pos (TCEAssignOp (c_op, e1_expr, e2_final)) e1_expr.ctype pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end
  
  (* === NULL COMPARISONS === *)
  
  (* Enum null check: enum == null -> enum.index == -1 *)
  | OpEq when is_null_compare && (is_enum_struct_expr e1 || is_enum_struct_expr e2) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let enum_expr = if is_null_const e1 then e2_expr else e1_expr in
      let index = mk_expr (TCEDot (enum_expr, "index")) TCInt32 in
      let neg_one = mk_int (-1l) in
      let result = mk_expr_pos (TCEBinop (TCOpEq, index, neg_one)) TCBool pos in
      (* Propagate pending_stmts from both operands *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
  
  | OpNotEq when is_null_compare && (is_enum_struct_expr e1 || is_enum_struct_expr e2) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let enum_expr = if is_null_const e1 then e2_expr else e1_expr in
      let index = mk_expr (TCEDot (enum_expr, "index")) TCInt32 in
      let neg_one = mk_int (-1l) in
      let result = mk_expr_pos (TCEBinop (TCOpNeq, index, neg_one)) TCBool pos in
      (* Propagate pending_stmts from both operands *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
  
   (* Null comparison: handles FibDynamic, enums, value types, and pointer types *)
   | OpEq when is_null_compare ->
       let e1_expr = convert_expr ctx e1 in
       let e2_expr = convert_expr ctx e2 in
       let is_enum_type = function TCFibEnum _ -> true | _ -> false in
       let non_null_expr = if is_null_const e1 then e2_expr else e1_expr in
       let is_non_nullable_value_type = function
         | TCInt32 | TCFloat64 | TCBool | TCInt64 | TCUInt64 | TCFloat32
         | TCUInt8 | TCInt8 | TCInt16 | TCUInt16 | TCUInt32 | TCChar
         | TCSizeT | TCAtomicInt -> true
         | _ -> false
       in
       let propagate result =
         { result with
           pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
           gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
       in
       if is_non_nullable_value_type non_null_expr.ctype then
         (* Value types are never null - constant false *)
         propagate (mk_expr_pos (TCEBool false) TCBool pos)
       else if non_null_expr.ctype = TCFibDynamic then
         propagate (mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_null", [non_null_expr])) TCBool pos)
       else if is_enum_type non_null_expr.ctype then begin
         let index = mk_expr_inherit (TCEDot (non_null_expr, "index")) TCInt32 [non_null_expr] in
         let neg_one = mk_int (-1l) in
         propagate (mk_expr_pos (TCEBinop (TCOpEq, index, neg_one)) TCBool pos)
       end else
         (* Pointer/object types: expr == NULL *)
         let null_expr = mk_expr_pos TCENull non_null_expr.ctype pos in
         propagate (mk_expr_pos (TCEBinop (TCOpEq, non_null_expr, null_expr)) TCBool pos)
   
   | OpNotEq when is_null_compare ->
       let e1_expr = convert_expr ctx e1 in
       let e2_expr = convert_expr ctx e2 in
       let is_enum_type = function TCFibEnum _ -> true | _ -> false in
       let non_null_expr = if is_null_const e1 then e2_expr else e1_expr in
       let is_non_nullable_value_type = function
         | TCInt32 | TCFloat64 | TCBool | TCInt64 | TCUInt64 | TCFloat32
         | TCUInt8 | TCInt8 | TCInt16 | TCUInt16 | TCUInt32 | TCChar
         | TCSizeT | TCAtomicInt -> true
         | _ -> false
       in
       let propagate result =
         { result with
           pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
           gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
       in
       if is_non_nullable_value_type non_null_expr.ctype then
         (* Value types are never null - constant true *)
         propagate (mk_expr_pos (TCEBool true) TCBool pos)
       else if non_null_expr.ctype = TCFibDynamic then begin
         let is_null = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [non_null_expr])) TCBool in
         propagate (mk_expr_pos (TCEUnop (TCUNot, is_null)) TCBool pos)
       end else if is_enum_type non_null_expr.ctype then begin
         let index = mk_expr_inherit (TCEDot (non_null_expr, "index")) TCInt32 [non_null_expr] in
         let neg_one = mk_int (-1l) in
         propagate (mk_expr_pos (TCEBinop (TCOpNeq, index, neg_one)) TCBool pos)
       end else
         (* Pointer/object types: expr != NULL *)
         let null_expr = mk_expr_pos TCENull non_null_expr.ctype pos in
         propagate (mk_expr_pos (TCEBinop (TCOpNeq, non_null_expr, null_expr)) TCBool pos)
  
  (* === ENUM COMPARISONS === *)
  
  (* Enum struct comparison: enum1 == enum2 -> enum1.index == enum2.index *)
  | OpEq when is_enum_struct_expr e1 && is_enum_struct_expr e2 ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let idx1 = mk_expr (TCEDot (e1_expr, "index")) TCInt32 in
      let idx2 = mk_expr (TCEDot (e2_expr, "index")) TCInt32 in
      let result = mk_expr_pos (TCEBinop (TCOpEq, idx1, idx2)) TCBool pos in
      (* Propagate pending_stmts from both operands *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
  
  | OpNotEq when is_enum_struct_expr e1 && is_enum_struct_expr e2 ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let idx1 = mk_expr (TCEDot (e1_expr, "index")) TCInt32 in
      let idx2 = mk_expr (TCEDot (e2_expr, "index")) TCInt32 in
      let result = mk_expr_pos (TCEBinop (TCOpNeq, idx1, idx2)) TCBool pos in
      (* Propagate pending_stmts from both operands *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
  
  (* === STRING OPERATIONS === *)
  
  (* String concatenation - with GC safety for nested allocating expressions.
   * When we have nested concat like: concat(concat(a, b), c), the inner concat
   * result may be in a register when the outer concat allocates and triggers GC.
   * We extract allocating sub-expressions to rooted temp variables. *)
  | OpAdd when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = ensure_string ctx e1 e1_expr in
      let s2 = ensure_string ctx e2 e2_expr in
      (* Use GC-safe wrapper to extract nested allocating expressions *)
      wrap_with_gc_extraction_ctx (Some ctx)
        (fun a b -> mk_expr_pos (TCEStringConcat (a, b)) TCFibString pos)
        s1 s2
  
  (* String equality *)
  | OpEq when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = if e1_expr.ctype = TCFibDynamic 
               then mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [e1_expr])) TCFibString 
               else e1_expr in
      let s2 = if e2_expr.ctype = TCFibDynamic 
               then mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [e2_expr])) TCFibString 
               else e2_expr in
      let result = mk_expr_pos (TCEStringEq (s1, s2)) TCBool pos in
      (* Propagate pending_stmts from both operands *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
  
  (* String inequality *)
  | OpNotEq when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = if e1_expr.ctype = TCFibDynamic 
               then mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [e1_expr])) TCFibString 
               else e1_expr in
      let s2 = if e2_expr.ctype = TCFibDynamic 
               then mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [e2_expr])) TCFibString 
               else e2_expr in
      let eq = mk_expr (TCEStringEq (s1, s2)) TCBool in
      let result = mk_expr_pos (TCEUnop (TCUNot, eq)) TCBool pos in
      (* Propagate pending_stmts from both operands *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
  
  (* === UNSIGNED RIGHT SHIFT === *)
  
  | OpUShr ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let is_int64 = e1_expr.ctype = TCInt64 in
      let target_signed = if is_int64 then TCInt64 else TCInt32 in
      let target_unsigned = if is_int64 then TCUInt64 else TCUInt32 in
      let e1_ex = extract_fib_dynamic e1_expr target_signed in
      let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
      (* Mask shift amount to avoid C undefined behavior: & 63 for 64-bit, & 31 for 32-bit *)
      let mask_bits = if is_int64 then 63 else 31 in
      let e2_masked = mk_expr (TCEBinop (TCOpAnd, e2_ex, mk_int (Int32.of_int mask_bits))) TCInt32 in
      let unsigned = mk_expr_pos (TCECast (target_unsigned, e1_ex)) target_unsigned pos in
      let shift = mk_expr_pos (TCEBinop (TCOpShr, unsigned, e2_masked)) target_unsigned pos in
      let result = mk_expr_pos (TCECast (target_signed, shift)) target_signed pos in
      (* Propagate pending_stmts from both operands *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
  
  (* === FIBDYNAMIC ARITHMETIC === *)
  
  (* Arithmetic operations - extract FibDynamic operands *)
  | (OpAdd | OpSub | OpMult | OpDiv | OpMod) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        (* Dynamic + Dynamic: use fib_dynamic_add for runtime string check.
           Either operand might be a string at runtime, so we cannot just extract to int. *)
        if op = Ast.OpAdd && e1_expr.ctype = TCFibDynamic && e2_expr.ctype = TCFibDynamic then begin
          let result = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_add", [e1_expr; e2_expr])) TCFibDynamic pos in
          { result with
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
        end else begin
        (* For modulo on Dynamic, use fmod with float extraction since C % doesn't work on doubles *)
        let target_tc = if result_tc = TCFibDynamic then
          (match op with OpMod | OpDiv -> TCFloat64 | _ -> TCInt32)
        else result_tc in
        let e1_ex = extract_fib_dynamic e1_expr target_tc in
        let e2_ex = extract_fib_dynamic e2_expr target_tc in
        let c_op = convert_binop op in
        let result = if op = Ast.OpMod && (target_tc = TCFloat64 || target_tc = TCFloat32) then
          mk_expr_pos (TCECall (TCTFunc "fmod", [e1_ex; e2_ex])) TCFloat64 pos
        else
          mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) target_tc pos
        in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
        end
      end else begin
        let result = match op with
          | OpMod when result_tc = TCFloat64 || result_tc = TCFloat32 ||
                       e1_expr.ctype = TCFloat64 || e2_expr.ctype = TCFloat64 ->
            (* C % only works on integers; use fmod() for float modulo *)
            mk_expr_pos (TCECall (TCTFunc "fmod", [e1_expr; e2_expr])) TCFloat64 pos
          | OpDiv when e1_expr.ctype <> TCFloat64 && e1_expr.ctype <> TCFloat32 &&
                       e2_expr.ctype <> TCFloat64 && e2_expr.ctype <> TCFloat32 &&
                       e1_expr.ctype <> TCInt64 && e2_expr.ctype <> TCInt64 ->
            (* Haxe Int/Int always returns Float; cast LHS to double so C performs
               float division. This applies regardless of result_tc — even in Dynamic
               context, the division must use floating-point semantics.
               Int64 division stays as integer division -- no float cast. *)
            let e1_float = mk_expr (TCECast (TCFloat64, e1_expr)) TCFloat64 in
            let c_op = convert_binop op in
            mk_expr_pos (TCEBinop (c_op, e1_float, e2_expr)) TCFloat64 pos
          | _ ->
            let c_op = convert_binop op in
            (* When both operands are concrete C types, use the operand type as the
               result type — not the Haxe result_tc which may be Dynamic/Null<T>.
               This prevents spurious fib_dynamic_to_int wrappers around e.g.
               map_get_int(...) + 1 where Haxe type is Dynamic but C type is int32_t. *)
            let actual_tc =
              if e1_expr.ctype <> TCFibDynamic && e2_expr.ctype <> TCFibDynamic &&
                 result_tc = TCFibDynamic then
                e1_expr.ctype
              else result_tc
            in
            mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) actual_tc pos
        in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end
  
  (* String comparison - use fib_string_compare for lexicographic ordering *)
  | (OpLt | OpLte | OpGt | OpGte) when is_string_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let s1 = if e1_expr.ctype = TCFibDynamic
               then mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [e1_expr])) TCFibString
               else e1_expr in
      let s2 = if e2_expr.ctype = TCFibDynamic
               then mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [e2_expr])) TCFibString
               else e2_expr in
      let cmp = mk_expr (TCEStringCompare (s1, s2)) TCInt32 in
      let zero = mk_expr (TCEInt 0l) TCInt32 in
      let c_op = convert_binop op in
      let result = mk_expr_pos (TCEBinop (c_op, cmp, zero)) TCBool pos in
      { result with
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }

  (* Comparison operations - extract FibDynamic operands.
     Null semantics for ordering comparisons in Haxe:
     - null < anything  -> false     - null > anything  -> false
     - anything < null  -> false     - anything > null  -> false
     - null <= null     -> true      - null >= null     -> true
     - null <= nonNull  -> false     - null >= nonNull  -> false
     - nonNull <= null  -> false     - nonNull >= null  -> false
     So for < and >: false if either operand is null.
     For <= and >=: true if both null, false if exactly one null, otherwise compare. *)
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
        let cmp = mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCBool pos in
        let null_type = mk_expr_pos (TCERaw "FIB_TYPE_NULL") TCInt32 pos in
        let e1_is_dyn = e1_expr.ctype = TCFibDynamic in
        let e2_is_dyn = e2_expr.ctype = TCFibDynamic in
        let result =
          if (op = OpLte || op = OpGte) && e1_is_dyn && e2_is_dyn then begin
            (* Both dynamic, <= or >=: (both_null) || (neither_null && cmp) *)
            let e1_type = mk_expr_pos (TCEDot (e1_expr, "type")) TCInt32 pos in
            let e2_type = mk_expr_pos (TCEDot (e2_expr, "type")) TCInt32 pos in
            let e1_null = mk_expr_pos (TCEBinop (TCOpEq, e1_type, null_type)) TCBool pos in
            let e2_null = mk_expr_pos (TCEBinop (TCOpEq, e2_type, null_type)) TCBool pos in
            let both_null = mk_expr_pos (TCEBinop (TCOpBoolAnd, e1_null, e2_null)) TCBool pos in
            let e1_not_null = mk_expr_pos (TCEBinop (TCOpNeq, e1_type, null_type)) TCBool pos in
            let e2_not_null = mk_expr_pos (TCEBinop (TCOpNeq, e2_type, null_type)) TCBool pos in
            let neither_null = mk_expr_pos (TCEBinop (TCOpBoolAnd, e1_not_null, e2_not_null)) TCBool pos in
            let normal_cmp = mk_expr_pos (TCEBinop (TCOpBoolAnd, neither_null, cmp)) TCBool pos in
            mk_expr_pos (TCEBinop (TCOpBoolOr, both_null, normal_cmp)) TCBool pos
          end else begin
            (* For < and >, or when only one side is dynamic: false if any dynamic is null *)
            let guarded = cmp in
            let guarded = if e2_is_dyn then
              let t2 = mk_expr_pos (TCEDot (e2_expr, "type")) TCInt32 pos in
              let nn2 = mk_expr_pos (TCEBinop (TCOpNeq, t2, null_type)) TCBool pos in
              mk_expr_pos (TCEBinop (TCOpBoolAnd, nn2, guarded)) TCBool pos
            else guarded in
            let guarded = if e1_is_dyn then
              let t1 = mk_expr_pos (TCEDot (e1_expr, "type")) TCInt32 pos in
              let nn1 = mk_expr_pos (TCEBinop (TCOpNeq, t1, null_type)) TCBool pos in
              mk_expr_pos (TCEBinop (TCOpBoolAnd, nn1, guarded)) TCBool pos
            else guarded in
            guarded
          end
        in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end else begin
        let c_op = convert_binop op in
        let result = mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) TCBool pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end
  
  (* Equality with FibDynamic - extract to primitive for comparison, or use
     fib_dynamic_equals when both sides are Dynamic (e.g. Type.typeof comparisons) *)
  | (OpEq | OpNotEq) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let target_tc = if e1_expr.ctype <> TCFibDynamic then e1_expr.ctype
                        else if e2_expr.ctype <> TCFibDynamic then e2_expr.ctype
                        else TCFibDynamic in
        if target_tc = TCFibDynamic then begin
          (* Both sides are FibDynamic — use fib_dynamic_equals for proper type-aware comparison *)
          let eq_call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_equals", [e1_expr; e2_expr])) TCBool pos in
          let result = if op = OpNotEq then
            mk_expr_pos (TCEUnop (TCUNot, eq_call)) TCBool pos
          else eq_call in
          { result with
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
        end else if target_tc = TCFibClosure then begin
          (* Dynamic vs Closure: extract dynamic to closure, then use structural equality *)
          let dyn_expr = if e1_expr.ctype = TCFibDynamic then e1_expr else e2_expr in
          let e1_ex = extract_fib_dynamic e1_expr target_tc in
          let e2_ex = extract_fib_dynamic e2_expr target_tc in
          let eq_call = mk_expr_pos (TCECall (TCTFunc "fib_closure_equals", [e1_ex; e2_ex])) TCBool pos in
          let null_type = mk_expr_pos (TCERaw "FIB_TYPE_NULL") TCInt32 pos in
          let type_field = mk_expr_pos (TCEDot (dyn_expr, "type")) TCInt32 pos in
          let result = if op = OpEq then
            let not_null = mk_expr_pos (TCEBinop (TCOpNeq, type_field, null_type)) TCBool pos in
            mk_expr_pos (TCEBinop (TCOpBoolAnd, not_null, eq_call)) TCBool pos
          else
            let is_null = mk_expr_pos (TCEBinop (TCOpEq, type_field, null_type)) TCBool pos in
            let not_eq = mk_expr_pos (TCEUnop (TCUNot, eq_call)) TCBool pos in
            mk_expr_pos (TCEBinop (TCOpBoolOr, is_null, not_eq)) TCBool pos
          in
          { result with 
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
        end else begin
          (* One side is Dynamic, other is concrete. *)
          let is_extractable_primitive = match target_tc with
            | TCInt32 | TCInt64 | TCFloat64 | TCBool -> true
            | _ -> false
          in
          if is_extractable_primitive then begin
            (* Primitive target: extract Dynamic to primitive and compare with null guard.
               OpEq:    (dyn.type != FIB_TYPE_NULL && extract(dyn) == other)
               OpNotEq: (dyn.type == FIB_TYPE_NULL || extract(dyn) != other) *)
            let dyn_expr = if e1_expr.ctype = TCFibDynamic then e1_expr else e2_expr in
            let e1_ex = extract_fib_dynamic e1_expr target_tc in
            let e2_ex = extract_fib_dynamic e2_expr target_tc in
            let c_op = convert_binop op in
            let cmp = mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCBool pos in
            let null_type = mk_expr_pos (TCERaw "FIB_TYPE_NULL") TCInt32 pos in
            let type_field = mk_expr_pos (TCEDot (dyn_expr, "type")) TCInt32 pos in
            let result = if op = OpEq then
              let not_null = mk_expr_pos (TCEBinop (TCOpNeq, type_field, null_type)) TCBool pos in
              mk_expr_pos (TCEBinop (TCOpBoolAnd, not_null, cmp)) TCBool pos
            else
              let is_null = mk_expr_pos (TCEBinop (TCOpEq, type_field, null_type)) TCBool pos in
              mk_expr_pos (TCEBinop (TCOpBoolOr, is_null, cmp)) TCBool pos
            in
            { result with 
              pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
              gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
          end else begin
            (* Object/string/array/map/etc target: box the concrete side to
               FibDynamic and use fib_dynamic_equals for proper type-aware comparison. *)
            let e1_dyn = if e1_expr.ctype = TCFibDynamic then e1_expr
              else mk_expr (TCEBox (e1_expr, box_kind_of_type e1_expr.ctype)) TCFibDynamic in
            let e2_dyn = if e2_expr.ctype = TCFibDynamic then e2_expr
              else mk_expr (TCEBox (e2_expr, box_kind_of_type e2_expr.ctype)) TCFibDynamic in
            let eq_call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_equals", [e1_dyn; e2_dyn])) TCBool pos in
            let result = if op = OpNotEq then
              mk_expr_pos (TCEUnop (TCUNot, eq_call)) TCBool pos
            else eq_call in
            { result with
              pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
              gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
          end
        end
      end else begin
        (* Check if either operand is an enum struct - C structs can't use ==/!= directly *)
        let is_enum_type = function TCFibEnum _ -> true | _ -> false in
        let is_null_expr e = match e.cexpr with TCENull -> true | _ -> false in
        if is_enum_type e1_expr.ctype || is_enum_type e2_expr.ctype then begin
          if is_null_expr e1_expr || is_null_expr e2_expr then begin
            (* Enum null check: compare .index against -1 *)
            let enum_expr = if is_null_expr e1_expr then e2_expr else e1_expr in
            let index = mk_expr_inherit (TCEDot (enum_expr, "index")) TCInt32 [enum_expr] in
            let neg_one = mk_int (-1l) in
            let c_op = convert_binop op in
            let result = mk_expr_pos (TCEBinop (c_op, index, neg_one)) TCBool pos in
            { result with 
              pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
              gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
          end else begin
            (* Compare enum structs by .index field *)
            let idx1 = mk_expr_inherit (TCEDot (e1_expr, "index")) TCInt32 [e1_expr] in
            let idx2 = mk_expr_inherit (TCEDot (e2_expr, "index")) TCInt32 [e2_expr] in
            let c_op = convert_binop op in
            let result = mk_expr_pos (TCEBinop (c_op, idx1, idx2)) TCBool pos in
            { result with 
              pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
              gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
          end
        end else if e1_expr.ctype = TCFibClosure || e2_expr.ctype = TCFibClosure then begin
          (* Closure equality: use structural comparison (same fn + same captures) *)
          let eq_call = mk_expr_pos (TCECall (TCTFunc "fib_closure_equals", [e1_expr; e2_expr])) TCBool pos in
          let result = if op = OpNotEq then
            mk_expr_pos (TCEUnop (TCUNot, eq_call)) TCBool pos
          else eq_call in
          { result with
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
        end else begin
          let c_op = convert_binop op in
          let result = mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) TCBool pos in
          (* Propagate pending_stmts from both operands *)
          { result with 
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
        end
      end
  
  (* Bitwise operations - extract FibDynamic to int *)
  | (OpAnd | OpOr | OpXor | OpShl | OpShr) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let is_shift = (op = OpShl || op = OpShr) in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        (* Use result type to determine extraction target (Int32 vs Int64) *)
        let target_tc = if result_tc = TCInt64 then TCInt64 else TCInt32 in
        let e1_ex = extract_fib_dynamic e1_expr target_tc in
        let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
        (* Mask shift amount to avoid C undefined behavior: & 63 for 64-bit, & 31 for 32-bit *)
        let e2_final = if is_shift then
          let mask_bits = if target_tc = TCInt64 then 63 else 31 in
          mk_expr (TCEBinop (TCOpAnd, e2_ex, mk_int (Int32.of_int mask_bits))) TCInt32
        else e2_ex in
        let c_op = convert_binop op in
        let result = mk_expr_pos (TCEBinop (c_op, e1_ex, e2_final)) target_tc pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end else begin
        let c_op = convert_binop op in
        (* Mask shift amount to avoid C undefined behavior: & 63 for 64-bit, & 31 for 32-bit *)
        let e2_final = if is_shift then
          let is_int64 = (e1_expr.ctype = TCInt64 || result_tc = TCInt64) in
          let mask_bits = if is_int64 then 63 else 31 in
          mk_expr (TCEBinop (TCOpAnd, e2_expr, mk_int (Int32.of_int mask_bits))) TCInt32
        else e2_expr in
        let result = mk_expr_pos (TCEBinop (c_op, e1_expr, e2_final)) result_tc pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end
  
  (* Boolean operations - extract FibDynamic to bool.
   *
   * When the RHS has pending_stmts (temp var declarations from field access
   * chains, etc.), we CANNOT hoist them before the expression because that
   * breaks short-circuit evaluation. For example:
   *
   *   if (info.schema != null && info.schema.hide == true) ...
   *
   * Naively hoisting both sides produces:
   *   tmp1 = fib_field_get(info, "schema");
   *   tmp2 = fib_field_get(tmp1, "hide");  // NPE when schema is null!
   *   if (!is_null(tmp1) && to_bool(tmp2)) ...
   *
   * Instead, when e2 has pending_stmts, we lower to:
   *   bool _tmp = false;        (or true for OpBoolOr)
   *   <e1 pending_stmts>
   *   if (e1) {                 (or if (!e1) for OpBoolOr)
   *       <e2 pending_stmts>
   *       _tmp = e2;
   *   }
   *   // use _tmp
   *
   * This follows the same pattern as the ternary lowering (see TIf above). *)
  | (OpBoolAnd | OpBoolOr) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      (* Prepare bool-coerced versions for the expression value *)
      let e1_bool = if e1_expr.ctype = TCFibDynamic then extract_fib_dynamic e1_expr TCBool else e1_expr in
      let e2_bool = if e2_expr.ctype = TCFibDynamic then extract_fib_dynamic e2_expr TCBool else e2_expr in
      if e2_expr.pending_stmts <> [] then begin
        (* RHS has pending_stmts -- must lower to if-statement form *)
        let tmp = ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let tmp_name = Printf.sprintf "_gc_tmp%d" tmp in
        (* Default value: false for &&, true for || *)
        let default_val = match op with OpBoolAnd -> false | _ -> true in
        let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = TCBool; vd_init = Some (mk_expr (TCEBool default_val) TCBool); vd_static = false; vd_const = false; vd_volatile = false } in
        (* Condition: e1 for &&, !e1 for || *)
        let cond = match op with
          | OpBoolAnd -> { e1_bool with pending_stmts = [] }
          | _ -> mk_expr (TCEUnop (TCUNot, { e1_bool with pending_stmts = [] })) TCBool
        in
        (* Assignment inside the branch: _tmp = e2 *)
        let assign = TCSExpr (mk_expr (TCEAssign (mk_expr (TCELocal tmp_name) TCBool, { e2_bool with pending_stmts = [] })) TCBool) in
        let branch_stmts = e2_expr.pending_stmts @ [assign] in
        let if_stmt = TCSIf (cond, branch_stmts, None) in
        let all_stmts = e1_expr.pending_stmts @ [tmp_decl; if_stmt] in
        { (mk_expr_pos (TCELocal tmp_name) TCBool pos) with
          pending_stmts = all_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end else begin
        (* Simple case: no pending_stmts on RHS, safe to use C &&/|| directly *)
        let c_op = convert_binop op in
        let result = mk_expr_pos (TCEBinop (c_op, e1_bool, e2_bool)) TCBool pos in
        { result with 
          pending_stmts = e1_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end
  
  (* Remaining operators *)
  | _ ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let c_op = convert_binop op in
      let result = mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) result_tc pos in
      (* Propagate pending_stmts from both operands *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }

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

(* Coerce RHS to match LHS type: box to FibDynamic, cast class pointers, etc.
   NOTE: This must NOT do unboxing or numeric coercion — only boxing and class pointer casts.
   For full coercion, use coerce_to_type directly. *)
and box_if_needed lhs_tc rhs_expr =
   if lhs_tc = TCFibDynamic && rhs_expr.ctype <> TCFibDynamic then
     let result = mk_expr (TCEBox (rhs_expr, box_kind_of_type rhs_expr.ctype)) TCFibDynamic in
     if rhs_expr.pending_stmts <> [] then
       { result with pending_stmts = rhs_expr.pending_stmts; gc_roots = rhs_expr.gc_roots }
     else
       result
   else if lhs_tc <> TCFibDynamic && rhs_expr.ctype = TCFibDynamic then
     (* Unbox: assigning Dynamic to a concrete type *)
     coerce_to_type rhs_expr lhs_tc
   else match rhs_expr.ctype, lhs_tc with
   | TCFibClass src, TCFibClass tgt when src <> tgt ->
     let result = mk_expr (TCECast (lhs_tc, rhs_expr)) lhs_tc in
     if rhs_expr.pending_stmts <> [] then
       { result with pending_stmts = rhs_expr.pending_stmts; gc_roots = rhs_expr.gc_roots }
     else result
   | _ -> rhs_expr

(* Convert array element assignment: arr[i] = value *)
and convert_array_assign ctx e1 e2 pos =
  match e1.Type.eexpr with
  | Type.TArray (arr, idx) ->
      let arr_expr = convert_expr ctx arr in
      let idx_expr = convert_expr ctx idx in
      let val_expr = convert_expr ctx e2 in
      let sub_gc_roots = arr_expr.gc_roots + idx_expr.gc_roots + val_expr.gc_roots in
      let arr_kind = match arr_expr.ctype with TCFibArray k -> k | _ -> TCArrGeneric in
      let elem_tc = FiberusTypeUtils.array_kind_elem_tc arr_kind in
      let coerced_val = if arr_kind <> TCArrGeneric then coerce_to_type val_expr elem_tc else val_expr in
      let result =
        if arr_kind <> TCArrGeneric then begin
          (* Specialized array: fib_*_array_set(arr, idx, value)
           * ArraySet returns bool in C; to support assignment-as-expression (Haxe
           * evaluates arr[i]=v to v), we use comma: (set(arr,idx,v), v).
           * Cache value in temp if it has side effects to avoid double evaluation.
           * val_cache includes coerced_val.pending_stmts. *)
          let val_safe, val_cache = cache_if_side_effects coerced_val in
          let access = { arr = arr_expr; idx = idx_expr; arr_kind; elem_type = val_safe.ctype } in
          let set_expr = mk_expr (TCEArraySet (access, val_safe)) TCBool in
          { (mk_expr_pos (TCEComma [set_expr; val_safe]) val_safe.ctype pos) with
            pending_stmts = arr_expr.pending_stmts @ idx_expr.pending_stmts @ val_cache }
        end else begin
          (* Generic array: box value to FibDynamic.
             Strip val_expr pending and include separately since TCEBox doesn't propagate them.
             Always cache the boxed value in a temp to avoid double-evaluation when the
             assigned value reads from the same array (Issue9746). *)
          let val_pre_pending, boxed =
            if val_expr.ctype = TCFibDynamic then
              ([], val_expr)
            else
              (val_expr.pending_stmts,
               mk_expr (TCEBox ({ val_expr with pending_stmts = [] }, box_kind_of_type val_expr.ctype)) TCFibDynamic)
          in
          let tmp_name = gen_gc_temp_name () in
          let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = TCFibDynamic; vd_init = Some boxed; vd_static = false; vd_const = false; vd_volatile = false } in
          let tmp_ref = mk_expr (TCELocal tmp_name) TCFibDynamic in
          let access = { arr = arr_expr; idx = idx_expr; arr_kind; elem_type = tmp_ref.ctype } in
          let set_expr = mk_expr (TCEArraySet (access, tmp_ref)) TCBool in
          { (mk_expr_pos (TCEComma [set_expr; tmp_ref]) TCFibDynamic pos) with
            pending_stmts = arr_expr.pending_stmts @ idx_expr.pending_stmts @ val_pre_pending @ [tmp_decl] }
        end
      in
      { result with gc_roots = sub_gc_roots + result.gc_roots }
  | _ -> 
      (* Fallback - shouldn't happen *)
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let result = mk_expr_pos (TCEAssign (e1_expr, e2_expr)) e1_expr.ctype pos in
      { result with pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
                    gc_roots = e1_expr.gc_roots + e2_expr.gc_roots + result.gc_roots }

(* Mark anonymous object as heap-allocated if stored in a field/variable.
   Compound-literal (stack) anon objects become dangling pointers when stored
   in fields that outlive the current scope. *)
and mark_anon_heap_alloc (e : tc_expr) : tc_expr =
  match e.cexpr with
  | TCEAnonObject (fields, false) -> { e with cexpr = TCEAnonObject (fields, true) }
  | _ -> e

(* Convert field assignment - may need write barrier *)
and convert_field_assign ctx e1 e2 pos =
  match e1.Type.eexpr with
  | Type.TField (obj, fa) ->
      (* Interface field assignment: use fib_reflect_set_field to dispatch through
         the actual class's field descriptor, avoiding type reinterpretation mismatches
         (e.g. I.v:Float vs C.v:Int both at same struct offset).
         Check this BEFORE converting obj/e2 to avoid redundant convert_expr calls. *)
      let is_interface_field = match fa with
        | Type.FInstance (c, _, _) -> FiberusVtable.is_interface c
        | _ -> false
      in
      if is_interface_field then begin
        (* Interface field assign: box the interface pointer to FibDynamic, then use
           fib_reflect_set_field so the write goes through the real class's field descriptor.
           We cannot use convert_anon_field_assign because obj is a typed interface pointer
           (e.g. IFoo_obj ptr), not a FibDynamic. *)
        let cf = match fa with Type.FInstance (_, _, cf) -> cf | _ -> assert false in
        let field_name_str = cf.cf_name in
        let val_tc = tc_type_of e1.Type.etype in
        let obj_expr = convert_expr ctx obj in
        let val_expr = convert_expr ctx e2 in
        (* Box value to FibDynamic *)
        let boxed_val = coerce_to_type val_expr TCFibDynamic in
        let field_name = mk_raw_string field_name_str in
        (* Box obj to FibDynamic via fib_dynamic_object( (FibObject-ptr) obj ) *)
        let cast_obj = mk_expr (TCECast (TCFibObject, obj_expr)) TCFibObject in
        let obj_as_dyn = mk_expr (TCECall (TCTFunc "fib_dynamic_object", [cast_obj])) TCFibDynamic in
        (* Store FibDynamic in a temp so we can take &temp *)
        let tmp_name = gen_gc_temp_name () in
        let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = TCFibDynamic; vd_init = Some obj_as_dyn; vd_static = false; vd_const = false; vd_volatile = false } in
        let tmp_ref = mk_expr (TCELocal tmp_name) TCFibDynamic in
        let obj_ptr = mk_expr (TCEAddrOf tmp_ref) (TCPointer TCFibDynamic) in
        (* Cache boxed_val if it has side effects *)
        let boxed_safe, boxed_cache = cache_if_side_effects boxed_val in
        let set_call = mk_expr_pos (TCECall (TCTFunc "fib_reflect_set_field", [obj_ptr; field_name; boxed_safe])) TCVoid pos in
        let result = coerce_to_type boxed_safe val_tc in
        { result with
          pending_stmts = obj_expr.pending_stmts @ [tmp_decl] @ val_expr.pending_stmts @ boxed_cache @ [TCSExpr set_call];
          gc_roots = obj_expr.gc_roots + val_expr.gc_roots }
      end else
      let obj_expr = convert_expr ctx obj in
      let val_expr = mark_anon_heap_alloc (convert_expr ctx e2) in
      let lhs_tc = tc_type_of e1.Type.etype in
      let rhs_tc = val_expr.ctype in
      (* Check if this is an instance field (has an object to barrier) *)
      let is_instance_field = match fa with
        | Type.FInstance _ | Type.FAnon _ | Type.FDynamic _ -> true
        | Type.FClosure (Some _, _) -> true
        | Type.FStatic _ | Type.FEnum _ | Type.FClosure (None, _) -> false
      in
      (* Convert the LHS field expression.
         For instance fields with different storage type (e.g. FibDynamic storage for
         a generic field with concrete Haxe type), we must produce an lvalue at the
         storage type rather than unboxing to the Haxe type. *)
      let lhs_expr, effective_lhs_tc = match fa with
        | Type.FInstance (c, _, cf) ->
            let field_storage_tc = tc_type_of cf.cf_type in
            if field_storage_tc <> lhs_tc then begin
              (* Generate raw field access at storage type, without unboxing.
                 This mirrors convert_expr's FInstance path but stops before coerce_to_type. *)
              let needs_cast = match Type.follow obj.Type.etype with
                | Type.TInst (obj_class, _) -> obj_class.cl_path <> c.cl_path
                | _ -> false
              in
              let raw_lhs = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
                let safe_obj =
                  if safe_obj.ctype = TCFibDynamic then
                    let class_tc = TCFibClass (flat_path c.cl_path) in
                    let obj_ptr = mk_expr (TCECall (TCTFunc "fib_dynamic_to_object", [safe_obj])) TCFibObject in
                    mk_expr (TCECast (class_tc, obj_ptr)) class_tc
                  else safe_obj
                in
                if needs_cast then begin
                  let class_name = flat_path c.cl_path in
                  let cast_expr = mk_expr (TCECast (TCFibClass class_name, safe_obj)) (TCFibClass class_name) in
                  mk_expr_pos (TCEArrow (cast_expr, ident cf.cf_name)) field_storage_tc pos
                end else
                  mk_expr_pos (TCEArrow (safe_obj, ident cf.cf_name)) field_storage_tc pos
              ) obj_expr in
              raw_lhs, field_storage_tc
            end else
              convert_expr ctx e1, lhs_tc
        | _ ->
            convert_expr ctx e1, lhs_tc
      in
      let rhs = box_if_needed effective_lhs_tc val_expr in
      (* If assigning a generic FibArray (often from Dynamic) into a specialized
         Array<Int> field, convert elements to preserve correct reads. *)
      let rhs = match effective_lhs_tc, rhs.ctype with
        | TCFibArray TCArrInt, TCFibArray TCArrGeneric ->
            let conv = mk_expr (TCECall (TCTFunc "fib_array_to_int_array", [rhs])) effective_lhs_tc in
            if rhs.pending_stmts <> [] then
              { conv with pending_stmts = rhs.pending_stmts; gc_roots = rhs.gc_roots + conv.gc_roots }
            else conv
        | _ -> rhs
      in
      (* If RHS is itself an assignment/compound assignment, sequence via a
         temporary to avoid undefined behavior (e.g., x = x += 1). *)
      let rhs_is_assign = match e2.Type.eexpr with
        | Type.TBinop (Ast.OpAssignOp _, _, _) | Type.TBinop (Ast.OpAssign, _, _) -> true
        | _ -> false
      in
      let rhs, seq_stmts = if rhs_is_assign then begin
        let tmp_name = Printf.sprintf "_seq_%d" ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let tmp_var = TCSVar { vd_name = tmp_name; vd_type = rhs.ctype; vd_init = Some rhs;
          vd_static = false; vd_const = false; vd_volatile = false } in
        mk_expr (TCELocal tmp_name) rhs.ctype, [tmp_var]
      end else
        rhs, []
      in
      (* Check if write barrier needed - object pointers need barriers.
         When the effective storage type is FibDynamic (e.g. generic field), skip the
         barrier: FibDynamic is a value type copied into the field, and the GC traces
         it by scanning object memory rather than relying on write barriers. *)
      let needs_barrier = is_instance_field && needs_write_barrier_tc rhs_tc
        && effective_lhs_tc <> TCFibDynamic in
      if needs_barrier then begin
        (* Emit: (FIBRIX_WRITE_BARRIER(obj, rhs), obj->field = rhs)
         * For expressions with side effects (calls, allocations), extract rhs
         * into a temp variable first to avoid double-evaluation. *)
        let rhs, seq_stmts =
          if is_allocating_expr rhs then begin
            let tmp_name = Printf.sprintf "_wb_%d" ctx.temp_counter in
            ctx.temp_counter <- ctx.temp_counter + 1;
            let tmp_var = TCSVar { vd_name = tmp_name; vd_type = rhs.ctype; vd_init = Some rhs;
              vd_static = false; vd_const = false; vd_volatile = false } in
            mk_expr (TCELocal tmp_name) rhs.ctype, seq_stmts @ [tmp_var]
          end else
            rhs, seq_stmts
        in
        let barrier = mk_expr (TCECall (TCTMacro "FIBRIX_WRITE_BARRIER", [obj_expr; rhs])) TCVoid in
        let assign = mk_expr (TCEAssign (lhs_expr, rhs)) effective_lhs_tc in
        let result = mk_expr_pos (TCEComma [barrier; assign]) effective_lhs_tc pos in
        (* Propagate pending_stmts from all sub-expressions *)
        { result with 
          pending_stmts = obj_expr.pending_stmts @ lhs_expr.pending_stmts @ rhs.pending_stmts @ seq_stmts @ result.pending_stmts;
          gc_roots = obj_expr.gc_roots + lhs_expr.gc_roots + rhs.gc_roots }
      end else begin
        let result = mk_expr_pos (TCEAssign (lhs_expr, rhs)) effective_lhs_tc pos in
        (* Propagate pending_stmts from sub-expressions *)
        { result with 
          pending_stmts = lhs_expr.pending_stmts @ rhs.pending_stmts @ seq_stmts @ result.pending_stmts;
          gc_roots = lhs_expr.gc_roots + rhs.gc_roots }
      end
  | _ ->
      (* Fallback - regular assignment *)
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let rhs = box_if_needed e1_expr.ctype e2_expr in
      let result = mk_expr_pos (TCEAssign (e1_expr, rhs)) e1_expr.ctype pos in
      (* Propagate pending_stmts from sub-expressions *)
      { result with 
        pending_stmts = e1_expr.pending_stmts @ rhs.pending_stmts @ result.pending_stmts;
        gc_roots = e1_expr.gc_roots + rhs.gc_roots }

(* Convert anonymous/dynamic field assignment: obj.field = value
   Uses fib_anon_set for FAnon or fib_reflect_set_field for FDynamic.
   Both take (FibDynamic* obj_ptr, const char* name, FibDynamic value). *)
and convert_anon_field_assign ctx e1 e2 pos =
  match e1.Type.eexpr with
  | Type.TField (obj, fa) ->
      let field_name_str = (match fa with Type.FAnon cf -> cf.cf_name | Type.FDynamic n -> n | _ -> assert false) in
      (* Use fib_reflect_set_field for both FAnon and FDynamic: the runtime value
         may be FIB_TYPE_OBJECT (e.g. @:nativeGen class through structural type),
         and fib_anon_set silently skips non-anon objects. fib_reflect_set_field
         handles both FIB_TYPE_ANON and FIB_TYPE_OBJECT correctly. *)
      let _is_fdynamic = (match fa with Type.FDynamic _ -> true | _ -> false) in
      let set_func = "fib_reflect_set_field" in
      let obj_expr = convert_expr ctx obj in
      let val_expr = convert_expr ctx e2 in
      let val_tc = tc_type_of e1.Type.etype in
      (* Box value to FibDynamic for the set call *)
      let boxed_val = coerce_to_type val_expr TCFibDynamic in
      let field_name = mk_raw_string field_name_str in
      (* Get address of the FibDynamic object for mutation.
         If obj_expr is an lvalue (local variable, GC field access), we can take &obj_expr directly.
         If obj_expr is an rvalue (function call like fib_field_get), we must extract to a
         temp variable first, then take & of the temp. *)
      let obj_ptr, extra_pending =
        (match obj_expr.cexpr with
        | TCELocal _ | TCEField _ | TCEArrow _ | TCEDot _ | TCEDeref _ ->
          (* Already an lvalue, safe to take address *)
          (mk_expr (TCEAddrOf obj_expr) (TCPointer TCFibDynamic), [])
        | _ ->
          (* Rvalue: extract to temp, take address of temp *)
          let tmp_name = gen_gc_temp_name () in
          let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = TCFibDynamic; vd_init = Some obj_expr; vd_static = false; vd_const = false; vd_volatile = false } in
          let tmp_ref = mk_expr (TCELocal tmp_name) TCFibDynamic in
          (mk_expr (TCEAddrOf tmp_ref) (TCPointer TCFibDynamic), [tmp_decl]))
      in
      (* Cache boxed_val in a temp if it has side effects, since it appears in both
         the set call and the result expression.
         boxed_cache includes boxed_val.pending_stmts, so don't include them separately. *)
      let boxed_safe, boxed_cache = cache_if_side_effects boxed_val in
      let set_call = mk_expr_pos (TCECall (TCTFunc set_func, [obj_ptr; field_name; boxed_safe])) TCVoid pos in
      let result = coerce_to_type boxed_safe val_tc in
      { result with
        pending_stmts = obj_expr.pending_stmts @ extra_pending @ boxed_cache @ [TCSExpr set_call];
        gc_roots = obj_expr.gc_roots + val_expr.gc_roots }
  | _ ->
      (* Should not reach here; fallback to generic assignment *)
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      mk_expr_pos (TCEAssign (e1_expr, e2_expr)) e1_expr.ctype pos

(* Convert anonymous/dynamic field compound assignment: obj.field op= value
   Reads old value, computes new, writes back via fib_anon_set/fib_reflect_set_field. *)
and convert_anon_field_compound_assign ctx inner_op e1 e2 pos =
  match e1.Type.eexpr with
  | Type.TField (obj, _fa) ->
      let field_name_str = (match _fa with Type.FAnon cf -> cf.cf_name | Type.FDynamic n -> n | _ -> assert false) in
      let _is_fdynamic = (match _fa with Type.FDynamic _ -> true | _ -> false) in
      let set_func = "fib_reflect_set_field" in
      let val_tc = tc_type_of e1.Type.etype in
      let obj_expr = convert_expr ctx obj in
      (* Cache obj_expr if it has side effects — used in both get and set *)
      let obj_safe, obj_cache_stmts = cache_if_side_effects obj_expr in
      let val_expr = convert_expr ctx e2 in
      let field_name = mk_raw_string field_name_str in
      (* Read old value *)
      let old_dyn = mk_expr (TCECall (TCTFunc "fib_field_get", [obj_safe; field_name])) TCFibDynamic in
      (* When the field type is Dynamic, determine compute type from RHS so we
         can unbox old value, compute at concrete type, then box back.
         e.g. expected.line += lineShift where .line is Dynamic but lineShift is Int *)
      let compute_tc = if val_tc = TCFibDynamic && val_expr.ctype <> TCFibDynamic then
        val_expr.ctype
      else
        val_tc
      in
      let old_typed = if compute_tc <> TCFibDynamic then coerce_to_type old_dyn compute_tc else old_dyn in
      (* Extract RHS to matching type *)
      let rhs_typed = extract_fib_dynamic val_expr compute_tc in
      (* Check for nested assignment -- sequence via temps to avoid UB *)
      let rhs_is_assign = match e2.Type.eexpr with
        | Type.TBinop (Ast.OpAssignOp _, _, _) | Type.TBinop (Ast.OpAssign, _, _) -> true
        | _ -> false
      in
      let old_pending, old_ref, rhs_pending, rhs_ref =
        if rhs_is_assign then begin
          let old_name = Printf.sprintf "_cmpd_%d" ctx.temp_counter in
          ctx.temp_counter <- ctx.temp_counter + 1;
          let old_var = TCSVar { vd_name = old_name; vd_type = compute_tc; vd_init = Some old_typed;
            vd_static = false; vd_const = false; vd_volatile = false } in
          let rhs_name = Printf.sprintf "_cmpd_%d" ctx.temp_counter in
          ctx.temp_counter <- ctx.temp_counter + 1;
          let rhs_var = TCSVar { vd_name = rhs_name; vd_type = compute_tc; vd_init = Some rhs_typed;
            vd_static = false; vd_const = false; vd_volatile = false } in
          ([old_var], mk_expr (TCELocal old_name) compute_tc, [rhs_var], mk_expr (TCELocal rhs_name) compute_tc)
        end else
          ([], old_typed, [], rhs_typed)
      in
      (* Compute new value: old op rhs, save in temp to avoid double evaluation *)
      let c_op = convert_binop inner_op in
      let new_typed = mk_expr (TCEBinop (c_op, old_ref, rhs_ref)) compute_tc in
      let result_name = gen_gc_temp_name () in
      let result_decl = TCSVar { vd_name = result_name; vd_type = compute_tc; vd_init = Some new_typed;
        vd_static = false; vd_const = false; vd_volatile = false } in
      let result_ref = mk_expr (TCELocal result_name) compute_tc in
      (* Box and write back *)
      let boxed_new = coerce_to_type result_ref TCFibDynamic in
      let obj_ptr, extra_pending =
        (match obj_safe.cexpr with
        | TCELocal _ | TCEField _ | TCEArrow _ | TCEDot _ | TCEDeref _ ->
          (mk_expr (TCEAddrOf obj_safe) (TCPointer TCFibDynamic), [])
        | _ ->
          let tmp_name = gen_gc_temp_name () in
          let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = TCFibDynamic; vd_init = Some obj_safe; vd_static = false; vd_const = false; vd_volatile = false } in
          let tmp_ref = mk_expr (TCELocal tmp_name) TCFibDynamic in
          (mk_expr (TCEAddrOf tmp_ref) (TCPointer TCFibDynamic), [tmp_decl]))
      in
      let set_call = mk_expr_pos (TCECall (TCTFunc set_func, [obj_ptr; field_name; boxed_new])) TCVoid pos in
      (* Result is the temp holding the new value *)
      { result_ref with
        pending_stmts = obj_cache_stmts @ extra_pending @ val_expr.pending_stmts @
                        old_dyn.pending_stmts @ old_typed.pending_stmts @
                        rhs_typed.pending_stmts @
                        old_pending @ rhs_pending @ [result_decl; TCSExpr set_call];
        gc_roots = obj_safe.gc_roots + val_expr.gc_roots }
  | _ -> assert false

(* Convert array compound assignment: arr[i] op= value *)
and convert_array_compound_assign ctx inner_op e1 e2 pos =
  match e1.Type.eexpr with
  | Type.TArray (arr, idx) ->
      let arr_expr_raw = convert_expr ctx arr in
      (* If the array is stored as FibDynamic, unbox to FibArray* *)
      let arr_expr = match arr_expr_raw.ctype with
        | TCFibDynamic ->
            mk_expr (TCECall (TCTFunc "fib_dynamic_to_array", [arr_expr_raw])) (TCFibArray TCArrGeneric)
        | _ -> arr_expr_raw
      in
      let idx_expr = convert_expr ctx idx in
      let val_expr = convert_expr ctx e2 in
      let sub_gc_roots = arr_expr_raw.gc_roots + idx_expr.gc_roots + val_expr.gc_roots in
      (* Cache arr and idx in temporaries if they have side effects,
         since they appear in both the get and set calls. *)
      let arr_safe, arr_cache = cache_if_side_effects arr_expr in
      let idx_safe, idx_cache = cache_if_side_effects idx_expr in
      (* For arr pending: when dynamic (arr_expr <> arr_expr_raw), arr_expr_raw's
         pending_stmts are separate from arr_expr's. Include both.
         When not dynamic, arr_expr = arr_expr_raw, so arr_cache already contains them. *)
      let arr_pre_pending = if arr_expr_raw.ctype = TCFibDynamic then arr_expr_raw.pending_stmts else [] in
      let all_sub_pending = arr_pre_pending @ arr_cache @ idx_cache @ val_expr.pending_stmts in
      let arr_kind = match arr_safe.ctype with TCFibArray k -> k | _ -> TCArrGeneric in
      let prefix = array_kind_prefix arr_kind in
      let elem_tc = match arr_kind with
        | TCArrInt -> TCInt32 | TCArrFloat -> TCFloat64 | TCArrBool -> TCBool
        | TCArrInt64 -> TCInt64 | TCArrUInt64 -> TCUInt64 | TCArrFloat32 -> TCFloat32
        | TCArrUInt8 -> TCUInt8 | TCArrGeneric -> TCFibDynamic
      in
      let result =
        if arr_kind <> TCArrGeneric then begin
          (* Specialized: tmp = get(arr, idx) op value; set(arr, idx, tmp); result = tmp *)
          let get_call = mk_expr (TCECall (TCTFunc (prefix ^ "get"), [arr_safe; idx_safe])) elem_tc in
          let c_op = convert_binop inner_op in
          let new_val = mk_expr (TCEBinop (c_op, get_call, val_expr)) elem_tc in
          let tmp_name = gen_gc_temp_name () in
          let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = elem_tc; vd_init = Some new_val; vd_static = false; vd_const = false; vd_volatile = false } in
          let tmp_ref = mk_expr (TCELocal tmp_name) elem_tc in
          let set_call = mk_expr (TCECall (TCTFunc (prefix ^ "set"), [arr_safe; idx_safe; tmp_ref])) TCBool in
          let set_stmt = TCSExpr set_call in
          { (mk_expr_pos (TCELocal tmp_name) elem_tc pos) with pending_stmts = [tmp_decl; set_stmt] }
        end else begin
          (* Generic array: element type is FibDynamic, must decide operation at codegen time *)
          let get_call = mk_expr (TCECall (TCTFunc "fib_array_get", [arr_safe; idx_safe])) TCFibDynamic in
          let is_string_concat = (inner_op = Ast.OpAdd) && (val_expr.ctype = TCFibString || (tc_type_of e2.Type.etype) = TCFibString) in
          let boxed = if is_string_concat then begin
            (* String concatenation: fib_dynamic_string(fib_string_concat(fib_dynamic_to_string(old), rhs_str)) *)
            let old_str = mk_expr (TCECall (TCTFunc "fib_dynamic_to_string", [get_call])) TCFibString in
            let rhs_str = ensure_string ctx e2 val_expr in
            let concat = mk_expr (TCEStringConcat (old_str, rhs_str)) TCFibString in
            mk_expr (TCECall (TCTFunc "fib_dynamic_string", [concat])) TCFibDynamic
          end else if inner_op = Ast.OpMod then begin
            (* Dynamic modulus: use runtime helper to handle int/float correctly *)
            let rhs_dyn = coerce_to_type val_expr TCFibDynamic in
            mk_expr (TCECall (TCTFunc "fib_dynamic_mod", [get_call; rhs_dyn])) TCFibDynamic
          end else begin
            (* Numeric operation: fib_dynamic_int(fib_dynamic_to_int(old) op rhs) *)
            let extracted = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [get_call])) TCInt32 in
            let val_ex = extract_fib_dynamic val_expr TCInt32 in
            let c_op = convert_binop inner_op in
            let computed = mk_expr (TCEBinop (c_op, extracted, val_ex)) TCInt32 in
            mk_expr (TCECall (TCTFunc "fib_dynamic_int", [computed])) TCFibDynamic
          end in
          let tmp_name = gen_gc_temp_name () in
          let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = TCFibDynamic; vd_init = Some boxed; vd_static = false; vd_const = false; vd_volatile = false } in
          let tmp_ref = mk_expr (TCELocal tmp_name) TCFibDynamic in
          let set_call = mk_expr (TCECall (TCTFunc "fib_array_set", [arr_safe; idx_safe; tmp_ref])) TCBool in
          let set_stmt = TCSExpr set_call in
          { (mk_expr_pos (TCELocal tmp_name) TCFibDynamic pos) with pending_stmts = [tmp_decl; set_stmt] }
        end
      in
      if all_sub_pending <> [] then
        { result with pending_stmts = all_sub_pending @ result.pending_stmts;
                      gc_roots = sub_gc_roots + result.gc_roots }
      else
        result
  | _ ->
      (* Fallback *)
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let c_op = convert_binop inner_op in
      let result = mk_expr_pos (TCEAssignOp (c_op, e1_expr, e2_expr)) e1_expr.ctype pos in
      { result with pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
                    gc_roots = e1_expr.gc_roots + e2_expr.gc_roots + result.gc_roots }

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
  (* Increment/Decrement on array element: arr[i]++ / ++arr[i] *)
  | (Ast.Increment | Ast.Decrement), _ when (match inner.eexpr with TArray _ -> true | _ -> false) ->
      (match inner.eexpr with
      | TArray (arr, idx) ->
          let arr_expr = convert_expr ctx arr in
          let idx_expr = convert_expr ctx idx in
          let arr_kind = match arr_expr.ctype with TCFibArray k -> k | _ -> TCArrGeneric in
          let delta_op = match op with Ast.Increment -> TCOpAdd | _ -> TCOpSub in
          let one = mk_int 1l in
          if arr_kind <> TCArrGeneric then begin
            let prefix = array_kind_prefix arr_kind in
            (* Cache arr and idx if they have side effects.
               cache_if_side_effects returns pending_stmts in the cache list. *)
            let arr_safe, arr_cache = cache_if_side_effects arr_expr in
            let idx_safe, idx_cache = cache_if_side_effects idx_expr in
            let all_cache = arr_cache @ idx_cache in
            let get_call = mk_expr (TCECall (TCTFunc (prefix ^ "get"), [arr_safe; idx_safe])) result_tc in
            if flag = Ast.Prefix then begin
              (* Pre: new_val = old +/- 1; set(arr, idx, new_val); return new_val *)
              let new_val = mk_expr (TCEBinop (delta_op, get_call, one)) result_tc in
              let tmp_name = gen_gc_temp_name () in
              let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = result_tc; vd_init = Some new_val;
                vd_static = false; vd_const = false; vd_volatile = false } in
              let tmp_ref = mk_expr (TCELocal tmp_name) result_tc in
              let set_call = TCSExpr (mk_expr (TCECall (TCTFunc (prefix ^ "set"), [arr_safe; idx_safe; tmp_ref])) TCBool) in
              { (mk_expr_pos (TCELocal tmp_name) result_tc pos) with
                pending_stmts = all_cache @ [tmp_decl; set_call] }
            end else begin
              (* Post: old = get(arr, idx); set(arr, idx, old +/- 1); return old *)
              let old_name = gen_gc_temp_name () in
              let old_decl = TCSVar { vd_name = old_name; vd_type = result_tc; vd_init = Some get_call;
                vd_static = false; vd_const = false; vd_volatile = false } in
              let old_ref = mk_expr (TCELocal old_name) result_tc in
              let new_val = mk_expr (TCEBinop (delta_op, old_ref, one)) result_tc in
              let set_call = TCSExpr (mk_expr (TCECall (TCTFunc (prefix ^ "set"), [arr_safe; idx_safe; new_val])) TCBool) in
              { (mk_expr_pos (TCELocal old_name) result_tc pos) with
                pending_stmts = all_cache @ [old_decl; set_call] }
            end
          end else begin
            (* Generic array - just use standard operator *)
            let c_op = convert_unop op flag in
            mk_expr_pos (TCEUnop (c_op, inner_expr)) inner_tc pos
          end
      | _ -> 
          let c_op = convert_unop op flag in
          mk_expr_pos (TCEUnop (c_op, inner_expr)) inner_tc pos)
  
  (* Increment/Decrement on anonymous/dynamic field *)
  | (Ast.Increment | Ast.Decrement), _ when (match inner.eexpr with
      | TField (_, (FAnon _ | FDynamic _)) -> true | _ -> false) ->
      let delta_op = match op with Ast.Increment -> TCOpAdd | _ -> TCOpSub in
      let one = mk_int 1l in
      (match inner.eexpr with
       | TField (obj, fa) ->
           let field_name_str = (match fa with FAnon cf -> cf.cf_name | FDynamic n -> n | _ -> assert false) in
           let is_fdynamic = (match fa with FDynamic _ -> true | _ -> false) in
      (* Use fib_reflect_set_field for both FAnon and FDynamic: the runtime value
         may be FIB_TYPE_OBJECT (e.g. @:nativeGen class through structural type),
         and fib_anon_set silently skips non-anon objects. fib_reflect_set_field
         handles both FIB_TYPE_ANON and FIB_TYPE_OBJECT correctly. *)
      let set_func = "fib_reflect_set_field" in
           let obj_expr = convert_expr ctx obj in
           (* Cache obj_expr if it has side effects — used in both get and set *)
           let obj_safe, obj_cache_stmts = cache_if_side_effects obj_expr in
           let field_name = mk_raw_string field_name_str in
           let old_dyn = mk_expr (TCECall (TCTFunc "fib_field_get", [obj_safe; field_name])) TCFibDynamic in
           let old_int = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [old_dyn])) TCInt32 in
           let old_name = Printf.sprintf "_old_%d" ctx.temp_counter in
           ctx.temp_counter <- ctx.temp_counter + 1;
           let old_var = TCSVar { vd_name = old_name; vd_type = TCInt32; vd_init = Some old_int;
             vd_static = false; vd_const = false; vd_volatile = false } in
           let old_ref = mk_expr (TCELocal old_name) TCInt32 in
           let new_val = mk_expr (TCEBinop (delta_op, old_ref, one)) TCInt32 in
           let boxed_new = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [new_val])) TCFibDynamic in
           let obj_ptr, extra_pending =
             (match obj_safe.cexpr with
             | TCELocal _ | TCEField _ | TCEArrow _ | TCEDot _ | TCEDeref _ ->
               (mk_expr (TCEAddrOf obj_safe) (TCPointer TCFibDynamic), [])
             | _ ->
               let tmp_name = gen_gc_temp_name () in
               let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = TCFibDynamic; vd_init = Some obj_safe; vd_static = false; vd_const = false; vd_volatile = false } in
               let tmp_ref = mk_expr (TCELocal tmp_name) TCFibDynamic in
               (mk_expr (TCEAddrOf tmp_ref) (TCPointer TCFibDynamic), [tmp_decl]))
           in
           let set_call = TCSExpr (mk_expr (TCECall (TCTFunc set_func, [obj_ptr; field_name; boxed_new])) TCVoid) in
           if flag = Ast.Prefix then
             (* Pre: return new value *)
             { new_val with pending_stmts = obj_cache_stmts @ extra_pending @ [old_var; set_call]; cpos = pos }
           else
             (* Post: return old value *)
             { old_ref with pending_stmts = obj_cache_stmts @ extra_pending @ [old_var; set_call]; cpos = pos }
       | _ -> assert false)

  (* Increment/Decrement on FibDynamic *)
  | (Ast.Increment | Ast.Decrement), _ when inner_tc = TCFibDynamic ->
      let delta_op = match op with Ast.Increment -> TCOpAdd | _ -> TCOpSub in
      let one = mk_int 1l in
      (* Extract int, compute, re-box, assign back *)
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [inner_expr])) TCInt32 in
      if flag = Ast.Prefix then begin
        (* Pre: assign e = fib_dynamic_int(fib_dynamic_to_int(e) +/- 1), then read fib_dynamic_to_int(e) *)
        let new_val = mk_expr (TCEBinop (delta_op, extract, one)) TCInt32 in
        let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [new_val])) TCFibDynamic in
        let assign = TCSExpr (mk_expr (TCEAssign (inner_expr, boxed)) TCFibDynamic) in
        let result = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [inner_expr])) TCInt32 in
        { result with pending_stmts = result.pending_stmts @ [assign]; cpos = pos }
      end else begin
        (* Post: save _old_N = fib_dynamic_to_int(e), assign e = fib_dynamic_int(_old_N +/- 1), return _old_N *)
        let old_name = Printf.sprintf "_old_%d" ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let old_var = TCSVar { vd_name = old_name; vd_type = TCInt32; vd_init = Some extract; vd_static = false; vd_const = false; vd_volatile = false } in
        let old_ref = mk_expr (TCELocal old_name) TCInt32 in
        let new_val = mk_expr (TCEBinop (delta_op, old_ref, one)) TCInt32 in
        let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [new_val])) TCFibDynamic in
        let assign = TCSExpr (mk_expr (TCEAssign (inner_expr, boxed)) TCFibDynamic) in
        { old_ref with pending_stmts = old_ref.pending_stmts @ [old_var; assign]; cpos = pos }
      end
  
  (* Increment/Decrement on generically-stored field (field stored as FibDynamic but
     accessed as a concrete type like Int). inner_expr is an unboxed rvalue, not an lvalue,
     so we need read-modify-write. Cache obj_expr if it has side effects. *)
  | (Ast.Increment | Ast.Decrement), _ when (match inner.eexpr with
      | Type.TField (_, Type.FInstance (_, _, cf)) ->
          let storage_tc = tc_type_of cf.cf_type in
          storage_tc = TCFibDynamic && inner_tc <> TCFibDynamic
      | _ -> false) ->
      let obj_expr_raw, obj_pre_pending, cf_name = match inner.eexpr with
        | Type.TField (obj, Type.FInstance (c, _, cf)) ->
            let obj_expr = convert_expr ctx obj in
            let class_name = flat_path c.cl_path in
            if obj_expr.ctype <> TCFibClass class_name then
              (* Cast needed: obj_expr pending must be extracted separately since
                 the cast expression doesn't carry them *)
              let cast = mk_expr (TCECast (TCFibClass class_name, { obj_expr with pending_stmts = [] })) (TCFibClass class_name) in
              (cast, obj_expr.pending_stmts, ident cf.cf_name)
            else
              (obj_expr, [], ident cf.cf_name)
        | _ -> assert false
      in
      (* Cache obj if it has side effects, since field_expr is used in both read and write.
         obj_cache includes obj_expr_raw.pending_stmts so we don't double-include. *)
      let obj_safe, obj_cache = cache_if_side_effects obj_expr_raw in
      let field_expr = mk_expr (TCEArrow (obj_safe, cf_name)) TCFibDynamic in
      let delta_op = match op with Ast.Increment -> TCOpAdd | _ -> TCOpSub in
      let one = mk_int 1l in
      let all_pre_pending = obj_pre_pending @ obj_cache in
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [field_expr])) TCInt32 in
      if flag = Ast.Prefix then begin
        (* Pre: old = extract(field); new = old +/- 1; field = box(new); return new *)
        let old_name = Printf.sprintf "_old_%d" ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let old_var = TCSVar { vd_name = old_name; vd_type = TCInt32; vd_init = Some extract;
          vd_static = false; vd_const = false; vd_volatile = false } in
        let old_ref = mk_expr (TCELocal old_name) TCInt32 in
        let new_val = mk_expr (TCEBinop (delta_op, old_ref, one)) TCInt32 in
        let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [new_val])) TCFibDynamic in
        let assign = TCSExpr (mk_expr (TCEAssign (field_expr, boxed)) TCFibDynamic) in
        { new_val with pending_stmts = all_pre_pending @ [old_var; assign]; cpos = pos }
      end else begin
        (* Post: old = extract(field); field = box(old +/- 1); return old *)
        let old_name = Printf.sprintf "_old_%d" ctx.temp_counter in
        ctx.temp_counter <- ctx.temp_counter + 1;
        let old_var = TCSVar { vd_name = old_name; vd_type = TCInt32; vd_init = Some extract;
          vd_static = false; vd_const = false; vd_volatile = false } in
        let old_ref = mk_expr (TCELocal old_name) TCInt32 in
        let new_val = mk_expr (TCEBinop (delta_op, old_ref, one)) TCInt32 in
        let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [new_val])) TCFibDynamic in
        let assign = TCSExpr (mk_expr (TCEAssign (field_expr, boxed)) TCFibDynamic) in
        { old_ref with pending_stmts = all_pre_pending @ [old_var; assign]; cpos = pos }
      end

  (* Regular increment/decrement *)
  | (Ast.Increment | Ast.Decrement), _ ->
      let c_op = convert_unop op flag in
      mk_expr_pos (TCEUnop (c_op, inner_expr)) inner_tc pos
  
  (* Not/Neg/NegBits on FibDynamic - need extraction *)
  | Ast.Not, _ when inner_tc = TCFibDynamic ->
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_bool", [inner_expr])) TCBool in
      let result = mk_expr_pos (TCEUnop (TCUNot, extract)) TCBool pos in
      { result with pending_stmts = inner_expr.pending_stmts @ result.pending_stmts;
                    gc_roots = inner_expr.gc_roots + result.gc_roots }
  
  | Ast.Neg, _ when inner_tc = TCFibDynamic ->
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [inner_expr])) TCInt32 in
      let result = mk_expr_pos (TCEUnop (TCUNeg, extract)) TCInt32 pos in
      { result with pending_stmts = inner_expr.pending_stmts @ result.pending_stmts;
                    gc_roots = inner_expr.gc_roots + result.gc_roots }
  
  | Ast.NegBits, _ when inner_tc = TCFibDynamic ->
      let extract = mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [inner_expr])) TCInt32 in
      let result = mk_expr_pos (TCEUnop (TCUBitNot, extract)) TCInt32 pos in
      { result with pending_stmts = inner_expr.pending_stmts @ result.pending_stmts;
                    gc_roots = inner_expr.gc_roots + result.gc_roots }
  
  (* Int64 negation: use unsigned arithmetic to avoid C signed overflow UB.
     Emit (int64_t)(-(uint64_t)x) instead of -x. This ensures -INT64_MIN
     wraps correctly to INT64_MIN via two's complement. *)
  | Ast.Neg, _ when inner_expr.ctype = TCInt64 ->
      let as_uint = mk_expr (TCECast (TCUInt64, inner_expr)) TCUInt64 in
      let negated = mk_expr (TCEUnop (TCUNeg, as_uint)) TCUInt64 in
      let result = mk_expr_pos (TCECast (TCInt64, negated)) TCInt64 pos in
      if inner_expr.pending_stmts <> [] then
        { result with pending_stmts = inner_expr.pending_stmts @ result.pending_stmts;
                      gc_roots = inner_expr.gc_roots + result.gc_roots }
      else result

  (* Standard unary operations *)
  | _ ->
      let c_op = convert_unop op flag in
      (* The unary op in C operates on the inner type. If the Haxe etype says the
         result should be a different type (e.g. Neg on Int returning Float after
         inlining), insert an explicit cast so downstream code sees the correct
         C-level type. Without this, we get "phantom types" where ctype claims
         Float64 but the emitted C code is still int arithmetic. *)
      let inner_result = mk_expr_pos (TCEUnop (c_op, inner_expr)) inner_expr.ctype pos in
      let result =
        if result_tc <> inner_expr.ctype && result_tc <> TCVoid && result_tc <> TCFibDynamic then
          mk_expr_pos (TCECast (result_tc, inner_result)) result_tc pos
        else
          { inner_result with ctype = result_tc }
      in
      if inner_expr.pending_stmts <> [] then
        { result with pending_stmts = inner_expr.pending_stmts @ result.pending_stmts;
                      gc_roots = inner_expr.gc_roots + result.gc_roots }
      else result

(* ============================================================================
 * Block Expression Conversion
 * ============================================================================ *)

(* Convert a Haxe expression to C-AST statements - for use in block expressions.
   This handles statement-like expressions (TVar) that need GC tracking. *)
and convert_expr_as_stmt ctx (e : texpr) : tc_stmt list =
  match e.eexpr with
  | TVar (v, init_opt) ->
      convert_tvar_stmt ctx v init_opt
  | TBlock exprs ->
      (* Nested block - flatten into statements *)
      List.concat_map (convert_expr_as_stmt ctx) exprs
  | TIf (cond, ethen, eelse_opt) ->
      let cond_expr = convert_expr ctx cond in
      (* Coerce FibDynamic condition to bool *)
      let cond_expr =
        if cond_expr.ctype = TCFibDynamic then
          mk_expr_inherit (TCECall (TCTFunc "fib_dynamic_to_bool", [cond_expr])) TCBool [cond_expr]
        else cond_expr
      in
      (* Save/restore gc_local_count around branches.
       * In GCFrame mode, gc_local_count only tracks stack-alloc field temp roots
       * (regular locals use frame slots), so this is typically a no-op.
       * In legacy mode, it tracks all temp roots as before. *)
      let saved_gc1 = gc_save_count ctx in
      let then_stmts = convert_expr_as_stmt ctx ethen in
      let to_pop1 = gc_roots_to_pop ctx saved_gc1 in
      let then_with_pop = if to_pop1 > 0 && not (ends_with_return ethen) then begin
        ctx.gc_local_count <- saved_gc1;
        then_stmts @ [TCSGCPop to_pop1]
      end else begin
        ctx.gc_local_count <- saved_gc1;
        then_stmts
      end in
      let else_with_pop = match eelse_opt with
        | None -> None
        | Some eelse ->
            let saved_gc2 = gc_save_count ctx in
            let else_stmts = convert_expr_as_stmt ctx eelse in
            let to_pop2 = gc_roots_to_pop ctx saved_gc2 in
            if to_pop2 > 0 && not (ends_with_return eelse) then begin
              ctx.gc_local_count <- saved_gc2;
              Some (else_stmts @ [TCSGCPop to_pop2])
            end else begin
              ctx.gc_local_count <- saved_gc2;
              Some else_stmts
            end
      in
      [TCSIf (cond_expr, then_with_pop, else_with_pop)]
  | TWhile (cond, body, flag) ->
      let cond_expr = convert_expr ctx cond in
      (* Coerce FibDynamic condition to bool *)
      let cond_expr =
        if cond_expr.ctype = TCFibDynamic then
          mk_expr_inherit (TCECall (TCTFunc "fib_dynamic_to_bool", [cond_expr])) TCBool [cond_expr]
        else cond_expr
      in
      ctx.loop_depth <- ctx.loop_depth + 1;
      let saved_try_depth_at_loop = ctx.try_depth_at_loop in
      ctx.try_depth_at_loop <- ctx.try_depth;
      let saved_gc_count = gc_save_count ctx in
      let yield_stmts = if ctx.loop_depth <= 1 then [TCSYieldPoint] else [] in
      let body_stmts = convert_expr_as_stmt ctx body in
      let to_pop = gc_roots_to_pop ctx saved_gc_count in
      let body_with_pop = if to_pop > 0 then begin
        ctx.gc_local_count <- saved_gc_count;
        yield_stmts @ body_stmts @ [TCSGCPop to_pop]
      end else
        yield_stmts @ body_stmts
      in
      ctx.try_depth_at_loop <- saved_try_depth_at_loop;
      ctx.loop_depth <- ctx.loop_depth - 1;
      let is_do_while = (flag = DoWhile) in
      [TCSWhile (cond_expr, body_with_pop, is_do_while)]
  | TReturn expr_opt ->
      let try_pops = exc_pop_stmts ctx.try_depth in
      let ret_expr = match expr_opt with
        | None -> None
        | Some inner ->
            let inner_expr = convert_expr ctx inner in
            (* Coerce to return type if known *)
            match ctx.current_ret_type with
            | Some ret_tc -> Some (coerce_to_type inner_expr ret_tc)
            | None -> Some inner_expr
      in
      if try_pops = [] then
        [TCSReturn ret_expr]
      else begin
        match ret_expr with
        | None ->
            try_pops @ [TCSReturn None]
        | Some cexpr ->
            let ret_type = cexpr.ctype in
            [TCSBlock (
              [TCSVar {
                vd_name = "__ret"; vd_type = ret_type;
                vd_init = Some cexpr;
                vd_static = false; vd_const = false; vd_volatile = false }]
              @ try_pops
              @ [TCSReturn (Some (mk_expr (TCELocal "__ret") ret_type))]
            )]
      end
  | TBreak ->
      (exc_pop_stmts (ctx.try_depth - ctx.try_depth_at_loop)) @ [TCSBreak]
  | TContinue ->
      (exc_pop_stmts (ctx.try_depth - ctx.try_depth_at_loop)) @ [TCSContinue]
  | TThrow exc ->
      let exc_expr = convert_expr ctx exc in
      let boxed_expr = 
        if exc_expr.ctype = TCFibDynamic then exc_expr
        else
          let b = mk_expr (TCEBox (exc_expr, box_kind_of_type exc_expr.ctype)) TCFibDynamic in
          (* Propagate pending_stmts from the inner expression to the box node,
             since write_expr does not emit pending_stmts of sub-expressions. *)
          { b with pending_stmts = exc_expr.pending_stmts @ b.pending_stmts;
                   gc_roots = exc_expr.gc_roots + b.gc_roots }
      in
      (* Extract pending_stmts and clear them from boxed_expr so the writer
         does not emit them a second time via emit_pending_stmts in TCSThrow. *)
      let pending = boxed_expr.pending_stmts in
      let boxed_expr = { boxed_expr with pending_stmts = [] } in
      pending @ [TCSThrow boxed_expr]
  (* Meta annotations - handle LoopLabel for break-from-switch-in-loop *)
  | TMeta ((Meta.LoopLabel, [(EConst (Int (n, _)), _)], _), inner) ->
      (match inner.eexpr with
      | TWhile _ ->
          let label = Printf.sprintf "_hx_loop_end_%s" n in
          let loop_stmts = convert_expr_as_stmt ctx inner in
          loop_stmts @ [TCSLabel label]
      | TBreak ->
          let label = Printf.sprintf "_hx_loop_end_%s" n in
          (* LoopLabel break uses goto to exit the loop; pop try handlers like a regular break *)
          (exc_pop_stmts (ctx.try_depth - ctx.try_depth_at_loop)) @ [TCSGoto label]
      | _ -> convert_expr_as_stmt ctx inner)
  | TMeta (_, inner) ->
      convert_expr_as_stmt ctx inner
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
      (* Multiple expressions - use pending_stmts instead of TCEBlock *)
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
      (* Return the last expression with all prior statements as pending_stmts.
       * This replaces the old TCEBlock pattern. *)
      { last_expr with 
        pending_stmts = final_stmts @ last_expr.pending_stmts;
        cpos = pos }

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
    let elem_tc = match arr_kind with
      | TCArrInt -> TCInt32
      | TCArrFloat -> TCFloat64
      | TCArrBool -> TCBool
      | TCArrUInt8 -> TCUInt8
      | TCArrInt64 -> TCInt64
      | TCArrUInt64 -> TCUInt64
      | TCArrFloat32 -> TCFloat32
      | TCArrGeneric -> TCFibDynamic
    in
    let item_exprs = List.map (fun item ->
      let expr = convert_expr ctx item in
      (* For generic arrays, box each element to FibDynamic *)
      if arr_kind = TCArrGeneric && expr.ctype <> TCFibDynamic then
        mk_expr_inherit (TCEBox (expr, box_kind_of_type expr.ctype)) TCFibDynamic [expr]
      (* For specialized arrays, coerce element to expected type (e.g. FibDynamic -> int32_t) *)
      else if arr_kind <> TCArrGeneric && expr.ctype <> elem_tc then
        let coerced = coerce_to_type expr elem_tc in
        if expr.pending_stmts <> [] && coerced.pending_stmts = [] then
          { coerced with pending_stmts = expr.pending_stmts; gc_roots = expr.gc_roots }
        else coerced
      else
        expr
    ) items in
    let sub_pending = collect_pending item_exprs in
    let sub_gc_roots = sum_gc_roots item_exprs in
    let result = mk_expr_pos (TCEArrayFromValues {
      afv_kind = arr_kind;
      afv_c_type = c_elem_type;
      afv_values = item_exprs;
    }) result_tc pos in
    if sub_pending <> [] then
      { result with pending_stmts = sub_pending; gc_roots = sub_gc_roots + result.gc_roots }
    else
      result
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
      (* Check if this is a static METHOD used as a value (not a call).
         The Haxe AST uses FStatic for both static var access and static method-as-value
         (unlike instance methods, which get FClosure). We detect method-as-value when
         the result type is a closure/function type. *)
      (match cf.cf_kind with
      | Method m when m <> MethDynamic && (result_tc = TCFibClosure || result_tc = TCFibDynamic) ->
          (* Static method reference — wrap in FibClosure via method thunk *)
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
          (* For String static methods, use fib_string_* runtime functions *)
          let c_func = match c.cl_path with
            | ([], "String") ->
                let c_name = match method_name with
                  | "fromCharCode" -> "fib_string_from_char_code"
                  | _ -> "fib_string_" ^ method_name
                in
                Some c_name
            | _ -> None
          in
           let defaults = match cf.cf_expr with
            | Some { Type.eexpr = Type.TFunction f } ->
              let filtered = filter_void_args f.tf_args in
               List.map (fun (_, d) -> match d with
                 | Some { Type.eexpr = Type.TConst c } -> (match c with
                   | Type.TInt i -> Some (Int32.to_string i)
                   | Type.TFloat s -> Some s
                   | Type.TBool true -> Some "true"
                   | Type.TBool false -> Some "false"
                   | Type.TString s -> Some ("fib_string_new(\"" ^ escape_string s ^ "\")")
                   | _ -> None)
                 | _ -> None) filtered
            | _ -> []
          in
          let thunk = {
            mth_thunk_name = thunk_name;
            mth_dyn_thunk_name = dyn_thunk_name;
            mth_is_static = true;
            mth_class_name = class_name;
            mth_method_name = method_name;
            mth_args = arg_types;
            mth_ret_type = ret_type;
            mth_c_func = c_func;
            mth_this_expr = None;
            mth_vtable_slot = None;
            mth_defaults = defaults;
          } in
          Hashtbl.replace ctx.method_thunks thunk_name thunk;
          mk_expr_pos (TCEMethodClosure {
            mc_thunk_name = thunk_name;
            mc_dyn_thunk_name = dyn_thunk_name;
            mc_is_static = true;
            mc_arg_count = arg_count;
            mc_obj = None;
          }) TCFibClosure pos
      | Method MethDynamic ->
          (* Static dynamic function — stored as void* global ClassName__dyn_methodName.
             Read it and coerce to the expected type (FibClosure* if used as value). *)
          let raw = mk_expr_pos (TCEStatic (class_name, "_dyn_" ^ ident cf.cf_name)) (TCPointer TCVoid) pos in
          if result_tc = TCFibClosure || result_tc = TCFibDynamic then
            coerce_to_type raw result_tc
          else
            raw
      | _ ->
          (* Enum abstract values with @:native: emit the raw C constant name.
             Enum abstracts generate an impl class (KAbstractImpl) with static fields
             for each constructor. When the field has @:native("YGDirectionLTR"), we
             emit that name directly instead of the mangled Haxe field name. *)
          (match c.cl_kind with
          | KAbstractImpl _ when Meta.has Meta.Native cf.cf_meta ->
              let native_name = match get_meta_string cf.cf_meta Meta.Native with
                | Some name -> name
                | None -> ident cf.cf_name
              in
              mk_expr_pos (TCERaw native_name) result_tc pos
          | _ ->
              (* Regular static field/variable access *)
              mk_expr_pos (TCEStatic (class_name, ident cf.cf_name)) result_tc pos))
  
  (* Instance field - special cases for Array.length and String.length *)
  | FInstance (c, _, cf) ->
      (* Array.length -> fib_*_array_length() *)
      if FiberusBuiltins.is_array_type obj.Type.etype && cf.cf_name = "length" then begin
        let arr_kind = get_array_kind obj.Type.etype in
        (* Wrap with GC-safe extraction if array is volatile *)
        wrap_single_gc_extraction_ctx (Some ctx) (fun safe_arr ->
          (* If the converted expression is still FibDynamic (e.g. from dynamic field), convert to array
             and override the Haxe-level arr_kind with generic since the runtime type is unknown *)
          let arr_expr, actual_kind = match safe_arr.ctype with
            | TCFibDynamic ->
              mk_expr (TCECall (TCTFunc "fib_dynamic_to_array", [safe_arr])) (TCFibArray TCArrGeneric), TCArrGeneric
            | _ -> safe_arr, arr_kind
          in
          mk_expr_pos (TCEArrayLength (arr_expr, actual_kind)) TCInt32 pos
        ) obj_expr
      end
      (* String.length -> fib_string_length() *)
      else if (FiberusBuiltins.is_string_type obj.Type.etype || c.cl_path = ([], "String")) && cf.cf_name = "length" then begin
        (* Wrap with GC-safe extraction if string is volatile *)
        wrap_single_gc_extraction_ctx (Some ctx) (fun safe_str ->
          (* If the converted expression is still FibDynamic (e.g. from dynamic field), convert to string *)
          let str_expr = match safe_str.ctype with
            | TCFibDynamic ->
              mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [safe_str])) TCFibString
            | _ -> safe_str
          in
          mk_expr_pos (TCEStringLength str_expr) TCInt32 pos
        ) obj_expr
      end
      else begin
        (* For interface field reads, use reflection to avoid storage type mismatches
           (e.g. interface declares Float but class stores Int). Do not use reflection
           for enum-typed fields because enum values are stored by value and field
           descriptors currently tag them as FIB_TYPE_OBJECT. *)
        let field_storage_tc = tc_type_of cf.cf_type in
        let use_reflect =
          FiberusVtable.is_interface c &&
          (match field_storage_tc with TCFibEnum _ -> false | _ -> true)
        in
        if use_reflect then begin
          let field_name = mk_raw_string cf.cf_name in
          let raw = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
            let dyn_obj = coerce_to_type safe_obj TCFibDynamic in
            mk_expr_inherit (TCECall (TCTFunc "fib_field_get", [dyn_obj; field_name])) TCFibDynamic [dyn_obj]
          ) obj_expr in
          if result_tc <> TCFibDynamic then
            coerce_to_type raw result_tc
          else
            raw
        end else begin
          (* Regular instance field access - use GC-safe extraction if obj is volatile.
           * This ensures that if obj came from an array element access or method call,
           * the intermediate pointer is rooted before we dereference it. *)
          let needs_cast = match Type.follow obj.Type.etype with
            | Type.TInst (obj_class, _) -> obj_class.cl_path <> c.cl_path
            | _ -> false
          in
          (* Field's storage type may differ from expression type in generics:
           * e.g., Node<T>.next has storage type FibDynamic but expression type Node<Int>* *)
          let arrow_tc = if field_storage_tc <> result_tc then field_storage_tc else result_tc in
          wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
            (* If the object is FibDynamic (e.g. field of a generic class with erased type params),
               unbox to the declaring class pointer before arrow access. *)
            let safe_obj =
              if safe_obj.ctype = TCFibDynamic then
                let class_tc = TCFibClass (flat_path c.cl_path) in
                let obj_ptr = mk_expr (TCECall (TCTFunc "fib_dynamic_to_object", [safe_obj])) TCFibObject in
                mk_expr (TCECast (class_tc, obj_ptr)) class_tc
              else safe_obj
            in
            let arrow_expr =
              if needs_cast then begin
                (* Cast to parent class type for inherited field access *)
                let class_name = flat_path c.cl_path in
                let cast_expr = mk_expr (TCECast (TCFibClass class_name, safe_obj)) (TCFibClass class_name) in
                mk_expr_pos (TCEArrow (cast_expr, ident cf.cf_name)) arrow_tc pos
              end else
                mk_expr_pos (TCEArrow (safe_obj, ident cf.cf_name)) arrow_tc pos
            in
            (* Unbox from storage type if needed, e.g. FibDynamic to Node pointer *)
            if arrow_tc <> result_tc then
              coerce_to_type arrow_expr result_tc
            else
              arrow_expr
          ) obj_expr
        end
      end
  
  (* Enum field *)
  | FEnum (e, ef) ->
      let enum_name = flat_path e.e_path in
      (* Check if this is a parameterized constructor used as a function value.
         When an enum constructor like A(x:Int) is used as a value (not called),
         e.g. list.map(A), we need to wrap it in a FibClosure via fib_enum_constr_closure.
         The runtime helper reads typed/dynamic thunk pointers from FibEnumConstrMeta
         and creates a closure. For 0-param constructors, TCEEnumConst emits the constant. *)
      let has_params = match Type.follow ef.ef_type with TFun _ -> true | _ -> false in
      if has_params && (result_tc = TCFibClosure || result_tc = TCFibDynamic) then begin
        let raw = Printf.sprintf "fib_enum_constr_closure(&%s_meta, %d)" enum_name ef.ef_index in
        let closure_expr = mk_expr_pos (TCERaw raw) TCFibClosure pos in
        if result_tc = TCFibDynamic then
          mk_expr_pos (TCEBox (closure_expr, TCBoxClosure)) TCFibDynamic pos
        else
          closure_expr
      end else
        mk_expr_pos (TCEEnumConst (enum_name, ident ef.ef_name)) result_tc pos
  
  (* Anonymous/dynamic field access - fib_field_get returns FibDynamic *)
  (* Wrap with GC-safe extraction since obj may be volatile *)
  (* Then unbox to the declared field type if it's a concrete type *)
  | FAnon cf ->
      let field_name = mk_raw_string cf.cf_name in
      let raw = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Box object to FibDynamic if needed (fib_field_get expects FibDynamic) *)
        let dyn_obj = coerce_to_type safe_obj TCFibDynamic in
        mk_expr_inherit (TCECall (TCTFunc "fib_field_get", [dyn_obj; field_name])) TCFibDynamic [dyn_obj]
      ) obj_expr in
      (* Unbox to declared field type if not Dynamic (e.g. p.pos where p:{pos:Int} -> fib_dynamic_to_int) *)
      if result_tc <> TCFibDynamic then
        coerce_to_type raw result_tc
      else
        raw
  
  | FDynamic name ->
      let field_name = mk_raw_string name in
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Box object to FibDynamic if needed (fib_field_get expects FibDynamic) *)
        let dyn_obj = coerce_to_type safe_obj TCFibDynamic in
        mk_expr_inherit (TCECall (TCTFunc "fib_field_get", [dyn_obj; field_name])) TCFibDynamic [dyn_obj]
      ) obj_expr
  
  (* Dynamic method as value - MethDynamic fields store a FibClosure* in a void* field.
     Reading the value just reads the field, unlike normal methods which create a thunk. *)
  | FClosure (Some (c, _), cf) when (match cf.cf_kind with Method MethDynamic -> true | _ -> false) ->
      let class_name = flat_path c.cl_path in
      let field_name = ident cf.cf_name in
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Cast object to declaring class type if needed *)
        let this_type = TCFibClass class_name in
        let cast_obj = if safe_obj.ctype <> this_type then
          mk_expr (TCECast (this_type, safe_obj)) this_type
        else safe_obj in
        (* Read the void* field and cast to FibClosure* *)
        let field_access = mk_expr (TCEArrow (cast_obj, field_name)) (TCPointer TCVoid) in
        mk_expr_pos (TCECast (TCFibClosure, field_access)) TCFibClosure pos
      ) obj_expr

  (* Closure field - method as value (FClosure with known class) *)
  | FClosure (Some (c, _), cf) ->
      let class_name = flat_path c.cl_path in
      let method_name = ident cf.cf_name in
      let thunk_name = Printf.sprintf "__%s_%s_thunk" class_name method_name in
      let dyn_thunk_name = thunk_name ^ "_dyn" in
      (* Determine if this is a static method *)
      let is_static = List.exists (fun scf -> scf.cf_name = cf.cf_name) c.cl_ordered_statics in
      (* Get argument types and return type *)
      let arg_types, ret_type = match Type.follow cf.cf_type with
        | TFun (args, ret) -> 
            (List.map (fun (n, _, t) -> (n, tc_type_of t)) args,
             tc_type_of ret)
        | _ -> ([], TCFibDynamic)
      in
      let arg_count = List.length arg_types in
      (* For Array types, methods use fib_array_* C functions, not Array_* *)
      let is_array = c.cl_path = ([], "Array") in
      (* For String types, methods use fib_string_* C functions, not String_* *)
      let is_string = c.cl_path = ([], "String") in
      (* For Map types, methods use fib_*_map_* C functions, not haxe_ds_*Map_* *)
      let map_kind = match c.cl_path with
        | (["haxe";"ds"], "IntMap") -> Some FiberusBuiltins.MapInt
        | (["haxe";"ds"], "StringMap") -> Some FiberusBuiltins.MapString
        | (["haxe";"ds"], "Int64Map") -> Some FiberusBuiltins.MapInt64
        | (["haxe";"ds"], "ObjectMap") -> Some FiberusBuiltins.MapObject
        | _ -> None
      in
      let c_func, this_expr, ret_type =
        if is_array then begin
          let c_name, override_ret = match method_name with
            | "remove" -> ("fib_array_remove_value", None)
            | "indexOf" -> ("fib_array_index_of", None)
            | "iterator" ->
                (* Use heap-allocated ArrayIterator (GC object with vtable/methods)
                   instead of stack-allocated FibArrayIterator *)
                ("haxe_iterators_ArrayIterator_new",
                 Some (TCFibClass "haxe_iterators_ArrayIterator"))
            | "keyValueIterator" ->
                (* Use heap-allocated ArrayKeyValueIterator (GC object with vtable/methods) *)
                ("haxe_iterators_ArrayKeyValueIterator_new",
                 Some (TCFibClass "haxe_iterators_ArrayKeyValueIterator"))
            | _ -> ("fib_array_" ^ method_name, None)
          in
          let effective_ret = match override_ret with Some r -> r | None -> ret_type in
          (Some c_name, Some "fib_dynamic_to_array(_c->captures[0])", effective_ret)
        end else if is_string then begin
          let c_name = match method_name with
            | "charAt" -> "fib_string_char_at_str"
            | "charCodeAt" -> "fib_string_char_code_at"
            | "indexOf" -> "fib_string_index_of"
            | "lastIndexOf" -> "fib_string_last_index_of"
            | "split" -> "fib_string_split"
            | "substr" -> "fib_string_substr"
            | "substring" -> "fib_string_substring"
            | "toLowerCase" -> "fib_string_to_lower"
            | "toUpperCase" -> "fib_string_to_upper"
            | "toString" -> "fib_string_to_string"
            | "trim" -> "fib_string_trim"
            | _ -> "fib_string_" ^ method_name
          in
          (Some c_name, Some "(FibString*)fib_dynamic_to_string(_c->captures[0])", ret_type)
        end else match map_kind with
        | Some kind ->
          let prefix = FiberusBuiltins.map_kind_prefix kind in
          let c_type = match kind with
            | FiberusBuiltins.MapInt -> "FibIntMap"
            | FiberusBuiltins.MapString -> "FibStringMap"
            | FiberusBuiltins.MapInt64 -> "FibInt64Map"
            | FiberusBuiltins.MapObject -> "FibObjectMap"
          in
			let override_ret = match method_name with
				| "keys" -> Some (match kind with
					| FiberusBuiltins.MapInt -> TCRaw "FibIntMapKeyIterator*"
					| FiberusBuiltins.MapString -> TCRaw "FibStringMapKeyIterator*"
					| FiberusBuiltins.MapInt64 -> TCRaw "FibInt64MapKeyIterator*"
					| FiberusBuiltins.MapObject -> TCRaw "FibObjectMapKeyIterator*")
				| "iterator" -> Some (match kind with
					| FiberusBuiltins.MapInt -> TCRaw "FibIntMapValueIterator*"
					| FiberusBuiltins.MapString -> TCRaw "FibStringMapValueIterator*"
					| FiberusBuiltins.MapInt64 -> TCRaw "FibInt64MapValueIterator*"
					| FiberusBuiltins.MapObject -> TCRaw "FibObjectMapValueIterator*")
				| "keyValueIterator" -> Some (TCFibClass "haxe_iterators_MapKeyValueIterator")
				| _ -> None
			in
			let effective_ret = match override_ret with Some r -> r | None -> ret_type in
			let this_cast = Printf.sprintf "(%s*)fib_dynamic_to_object(_c->captures[0])" c_type in
			let this_expr = match method_name with
				| "keyValueIterator" -> Some "fib_dynamic_object((FibObject*)fib_dynamic_to_object(_c->captures[0]))"
				| _ -> Some this_cast
			in
			let c_func = match method_name with
				| "keyValueIterator" -> Some "haxe_iterators_MapKeyValueIterator_new"
				| _ -> Some (prefix ^ method_name)
			in
			(c_func, this_expr, effective_ret)
        | None ->
          (None, None, ret_type)
      in
      (* For interface method closures, dispatch through vtable instead of direct call *)
      let vtable_slot =
        if FiberusVtable.is_interface c then
          match ctx.vtable_ctx with
          | Some vtctx -> FiberusVtable.get_interface_slot vtctx c cf
          | None -> None
        else None
      in
      let this_expr = if vtable_slot <> None then
        Some "(FibObject*)fib_dynamic_to_object(_c->captures[0])"
      else this_expr in
      (* Register the thunk for later generation *)
      let defaults = match cf.cf_expr with
        | Some { Type.eexpr = Type.TFunction f } ->
          let filtered = filter_void_args f.tf_args in
           List.map (fun (_, d) -> match d with
             | Some { Type.eexpr = Type.TConst c } -> (match c with
               | Type.TInt i -> Some (Int32.to_string i)
               | Type.TFloat s -> Some s
               | Type.TBool true -> Some "true"
               | Type.TBool false -> Some "false"
               | Type.TString s -> Some ("fib_string_new(\"" ^ escape_string s ^ "\")")
               | _ -> None)
             | _ -> None) filtered
        | _ -> []
      in
      let thunk = {
        mth_thunk_name = thunk_name;
        mth_dyn_thunk_name = dyn_thunk_name;
        mth_is_static = is_static;
        mth_class_name = class_name;
        mth_method_name = method_name;
        mth_args = arg_types;
        mth_ret_type = ret_type;
        mth_c_func = c_func;
        mth_this_expr = this_expr;
        mth_vtable_slot = vtable_slot;
        mth_defaults = defaults;
      } in
      Hashtbl.replace ctx.method_thunks thunk_name thunk;
      (* Generate the method closure expression *)
      let mc_obj = if is_static then None else Some obj_expr in
      mk_expr_pos (TCEMethodClosure {
        mc_thunk_name = thunk_name;
        mc_dyn_thunk_name = dyn_thunk_name;
        mc_is_static = is_static;
        mc_arg_count = arg_count;
        mc_obj = mc_obj;
      }) TCFibClosure pos
  
  (* Closure field - method as value on dynamic/unknown object *)
  | FClosure (None, cf) ->
      (* Instance method reference on dynamic/anon object — use dynamic field lookup.
         The object may be FibDynamic (a struct, not a pointer), so we cannot use
         arrow access. Instead, use fib_field_get which handles dynamic dispatch. *)
      let field_name = mk_raw_string cf.cf_name in
      let raw = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        let dyn_obj = coerce_to_type safe_obj TCFibDynamic in
        mk_expr_inherit (TCECall (TCTFunc "fib_field_get", [dyn_obj; field_name])) TCFibDynamic [dyn_obj]
      ) obj_expr in
      if result_tc <> TCFibDynamic then
        coerce_to_type raw result_tc
      else
        raw

(* ============================================================================
 * Array Access Conversion
 * ============================================================================ *)

and convert_array_access ctx arr idx result_tc pos =
  let arr_expr = convert_expr ctx arr in
  let idx_expr = convert_expr ctx idx in
  (* Collect pending_stmts from sub-expressions before wrapping *)
  let sub_pending = arr_expr.pending_stmts @ idx_expr.pending_stmts in
  let sub_gc_roots = arr_expr.gc_roots + idx_expr.gc_roots in
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
  let result =
    (* For specialized arrays, direct access returns the element type *)
    if arr_kind <> TCArrGeneric then begin
      let elem_tc = element_type_of_array_kind arr_kind in
      let access = {
        arr = arr_expr;
        idx = idx_expr;
        arr_kind = arr_kind;
        elem_type = elem_tc;
      } in
      let get_expr = mk_expr_pos (TCEArrayGet access) elem_tc pos in
      (* Coerce to expected type if different (e.g. int32_t -> FibDynamic when
         passed to a Dynamic parameter, or Null<Int> mapped as FibDynamic) *)
      if elem_tc <> result_tc then coerce_to_type get_expr result_tc
      else get_expr
    end else begin
      (* Generic array returns FibDynamic - need to unbox based on element type *)
      let access = {
        arr = arr_expr;
        idx = idx_expr;
        arr_kind = TCArrGeneric;
        elem_type = TCFibDynamic;
      } in
      let get_expr = mk_expr_pos (TCEArrayGet access) TCFibDynamic pos in
      (* Unbox the FibDynamic element to the expected result type.
         Use coerce_to_type which emits proper fib_dynamic_to_* calls,
         handling cross-type conversions (e.g. int boxed as FIB_TYPE_INT
         but read as Float needs fib_dynamic_to_float, not .data.floatVal). *)
      if result_tc = TCFibDynamic then get_expr
      else coerce_to_type get_expr result_tc
    end
  in
  (* Propagate pending_stmts from sub-expressions *)
  if sub_pending <> [] then
    { result with pending_stmts = sub_pending @ result.pending_stmts;
                  gc_roots = sub_gc_roots + result.gc_roots }
  else
    result

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
  
  (* Coerce a value for array operations: box to FibDynamic for generic arrays,
     or unbox to the element type for specialized arrays (e.g. FibDynamic -> int32_t for IntArray) *)
  let box_val val_expr =
    if is_specialized then
      let elem_tc = element_type_of_array_kind arr_kind in
      if val_expr.ctype <> elem_tc then coerce_to_type val_expr elem_tc
      else val_expr
    else
      let boxed = mk_expr (TCEBox (val_expr, box_kind_of_type val_expr.ctype)) TCFibDynamic in
      if val_expr.pending_stmts <> [] then
        { boxed with pending_stmts = val_expr.pending_stmts; gc_roots = val_expr.gc_roots }
      else boxed
  in
  
   (* Helper to get default value for optional int params, coercing to int32 *)
   let arg_or_default idx default =
     if idx < List.length args then
       let arg = List.nth args idx in
       match arg.Type.eexpr with
       | Type.TConst Type.TNull -> mk_int (Int32.of_int default)
       | _ ->
         let expr = List.nth arg_exprs idx in
         if expr.ctype = TCInt32 then expr
         else coerce_to_type expr TCInt32
     else mk_int (Int32.of_int default)
   in
  
  match method_name with
  | "push" ->
      let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      let val_expr = box_val val_expr in
      mk_expr_inherit (TCECall (TCTFunc (prefix ^ "push"), [arr_expr; val_expr])) TCInt32 [arr_expr; val_expr]
  
  | "pop" ->
      let elem_tc = element_type_of_array_kind arr_kind in
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "pop"), [arr_expr])) elem_tc pos in
      if is_specialized then
        (* Specialized pop returns e.g. int32_t which cannot represent null.
           Haxe semantics: pop on empty array returns null.
           Emit: (arr->length == 0) ? null : box(pop(arr)) *)
        let len_check = mk_expr (TCEBinop (TCOpEq, mk_expr (TCEArrayLength (arr_expr, arr_kind)) TCInt32, mk_int 0l)) TCBool in
        let null_expr = mk_expr_pos TCENull TCFibDynamic pos in
        let boxed_call = mk_expr (TCEBox (call, box_kind_of_type elem_tc)) TCFibDynamic in
        mk_expr_pos (TCETernary (len_check, null_expr, boxed_call)) TCFibDynamic pos
      else mk_expr_pos (TCEUnbox (call, result_tc)) result_tc pos
  
  | "shift" ->
      let elem_tc = element_type_of_array_kind arr_kind in
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "shift"), [arr_expr])) elem_tc pos in
      if is_specialized then
        (* Same as pop: specialized shift cannot represent null.
           Emit: (arr->length == 0) ? null : box(shift(arr)) *)
        let len_check = mk_expr (TCEBinop (TCOpEq, mk_expr (TCEArrayLength (arr_expr, arr_kind)) TCInt32, mk_int 0l)) TCBool in
        let null_expr = mk_expr_pos TCENull TCFibDynamic pos in
        let boxed_call = mk_expr (TCEBox (call, box_kind_of_type elem_tc)) TCFibDynamic in
        mk_expr_pos (TCETernary (len_check, null_expr, boxed_call)) TCFibDynamic pos
      else mk_expr_pos (TCEUnbox (call, result_tc)) result_tc pos
  
  | "unshift" ->
      let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      let val_expr = box_val val_expr in
      mk_expr_inherit (TCECall (TCTFunc (prefix ^ "unshift"), [arr_expr; val_expr])) TCVoid [arr_expr; val_expr]
  
  | "insert" ->
      let idx_expr = if List.length arg_exprs > 0 then List.nth arg_exprs 0 else mk_int 0l in
      let val_expr = if List.length arg_exprs > 1 then List.nth arg_exprs 1 else mk_int 0l in
      let val_expr = box_val val_expr in
      mk_expr_inherit (TCECall (TCTFunc (prefix ^ "insert"), [arr_expr; idx_expr; val_expr])) TCVoid [arr_expr; idx_expr; val_expr]
  
  | "remove" ->
      let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      let val_expr = box_val val_expr in
      mk_expr_inherit (TCECall (TCTFunc (prefix ^ "remove_value"), [arr_expr; val_expr])) TCBool [arr_expr; val_expr]
  
  | "indexOf" ->
      let val_expr = if List.length arg_exprs > 0 then List.nth arg_exprs 0 else mk_int 0l in
      let val_expr = box_val val_expr in
      let start_expr = arg_or_default 1 0 in
      mk_expr_inherit (TCECall (TCTFunc (prefix ^ "index_of"), [arr_expr; val_expr; start_expr])) TCInt32 [arr_expr; val_expr; start_expr]
  
  | "contains" ->
      let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      let val_expr = box_val val_expr in
      mk_expr_inherit (TCECall (TCTFunc (prefix ^ "contains"), [arr_expr; val_expr])) TCBool [arr_expr; val_expr]
  
  | "reverse" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "reverse"), [arr_expr])) TCVoid pos
  
  | "slice" ->
      let start_expr = arg_or_default 0 0 in
      let end_expr = arg_or_default 1 0x7FFFFFFF in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "slice"), [arr_expr; start_expr; end_expr])) arr_expr.ctype pos
  
  | "concat" ->
      let other_expr = if arg_exprs = [] then arr_expr else List.hd arg_exprs in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "concat"), [arr_expr; other_expr])) arr_expr.ctype pos
  
  | "join" ->
      let sep_expr = 
        if arg_exprs = [] then mk_expr (TCEString ",") TCFibString 
        else List.hd arg_exprs 
      in
      mk_expr_inherit (TCECall (TCTFunc "fib_array_join", [arr_expr; sep_expr])) TCFibString [arr_expr; sep_expr]
  
  | "iterator" ->
      (* Use heap-allocated haxe_iterators_ArrayIterator (proper GC object with vtable)
         instead of stack-allocated FibArrayIterator which cannot be used through dynamic dispatch *)
      let iter_tc = TCFibClass "haxe_iterators_ArrayIterator" in
      let call = mk_expr_pos (TCECall (TCTFunc "haxe_iterators_ArrayIterator_new", [arr_expr])) iter_tc pos in
      if result_tc <> iter_tc then coerce_to_type call result_tc
      else call
  
  | "splice" ->
      let pos_expr = arg_or_default 0 0 in
      let len_expr = arg_or_default 1 0 in
      (* Haxe splice(pos, len) -> fib_array_splice(arr, pos, len, NULL, 0) *)
      let null_expr = mk_expr (TCERaw "NULL") (TCRaw "FibDynamic*") in
      let zero_expr = mk_int 0l in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "splice"), [arr_expr; pos_expr; len_expr; null_expr; zero_expr])) arr_expr.ctype pos
  
  | "copy" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "copy"), [arr_expr])) arr_expr.ctype pos
  
  | "lastIndexOf" ->
      let val_expr = if List.length arg_exprs > 0 then List.nth arg_exprs 0 else mk_int 0l in
      let val_expr = box_val val_expr in
      (* Default fromIndex is max int (search from end) *)
      let from_expr = arg_or_default 1 0x7FFFFFFF in
      mk_expr_inherit (TCECall (TCTFunc (prefix ^ "last_index_of"), [arr_expr; val_expr; from_expr])) TCInt32 [arr_expr; val_expr; from_expr]
  
  | "resize" ->
      let size_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "resize"), [arr_expr; size_expr])) TCVoid pos
  
  | "sort" ->
      let cmp_expr = if arg_exprs = [] then mk_expr TCENull (TCRaw "FibClosure*") else List.hd arg_exprs in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "sort"), [arr_expr; cmp_expr])) TCVoid pos
  
  | "toString" ->
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "to_string"), [arr_expr])) TCFibString pos
  
  | "keyValueIterator" ->
      (* Use heap-allocated haxe_iterators_ArrayKeyValueIterator (proper GC object with vtable)
         same pattern as iterator() above *)
      let iter_tc = TCFibClass "haxe_iterators_ArrayKeyValueIterator" in
      let call = mk_expr_pos (TCECall (TCTFunc "haxe_iterators_ArrayKeyValueIterator_new", [arr_expr])) iter_tc pos in
      if result_tc <> iter_tc then coerce_to_type call result_tc
      else call
  
  | _ ->
      (* Fallback to generic Array_method call *)
      mk_expr_pos (TCECall (TCTMethod ("Array", ident method_name), arr_expr :: arg_exprs)) result_tc pos

(* Convert string method call *)
and convert_string_call ctx str_expr args arg_exprs method_name result_tc pos =
  (* Coerce FibDynamic to string if needed *)
  let str_expr = 
    if str_expr.ctype = TCFibDynamic then
      mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [str_expr])) TCFibString
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
      mk_expr_inherit (TCECall (TCTFunc "fib_string_char_at_str", [str_expr; idx_expr])) TCFibString [str_expr; idx_expr]
  
  | "charCodeAt" ->
      let idx_expr = arg_or_int_default 0 0 in
      mk_expr_inherit (TCECall (TCTFunc "fib_string_char_code_at", [str_expr; idx_expr])) TCFibDynamic [str_expr; idx_expr]
  
  | "substr" ->
      let start_expr = arg_or_int_default 0 0 in
      (* Use INT_MAX as sentinel for "no length specified" — negative values are valid
         per Haxe spec: substr(0, -1) means "all except last 1 char" *)
      let len_expr = arg_or_int_default 1 0x7FFFFFFF in
      mk_expr_inherit (TCECall (TCTFunc "fib_string_substr", [str_expr; start_expr; len_expr])) TCFibString [str_expr; start_expr; len_expr]
  
  | "substring" ->
      let start_expr = arg_or_int_default 0 0 in
      let end_expr = arg_or_int_default 1 (Int32.to_int Int32.min_int) in
      mk_expr_inherit (TCECall (TCTFunc "fib_string_substring", [str_expr; start_expr; end_expr])) TCFibString [str_expr; start_expr; end_expr]
  
  | "indexOf" ->
      let needle_expr = arg_or_string_default 0 "" in
      let start_expr = arg_or_int_default 1 0 in
      (* Wrap with GC extraction to protect allocating string arguments *)
      wrap_call_with_gc_extraction_ctx (Some ctx)
        (fun args -> mk_expr_pos (TCECall (TCTFunc "fib_string_index_of", args)) TCInt32 pos)
        [str_expr; needle_expr; start_expr]
  
  | "lastIndexOf" ->
      let needle_expr = arg_or_string_default 0 "" in
      (* Default startIndex: use max int so it clamps to string length *)
      let start_expr = arg_or_int_default 1 0x7FFFFFFF in
      (* Wrap with GC extraction to protect allocating string arguments *)
      wrap_call_with_gc_extraction_ctx (Some ctx)
        (fun args -> mk_expr_pos (TCECall (TCTFunc "fib_string_last_index_of", args)) TCInt32 pos)
        [str_expr; needle_expr; start_expr]
  
  | "split" ->
      let delim_expr = arg_or_string_default 0 "" in
      (* Wrap with GC extraction to protect allocating string arguments *)
      wrap_call_with_gc_extraction_ctx (Some ctx)
        (fun args -> mk_expr_pos (TCECall (TCTFunc "fib_string_split", args)) (TCFibArray TCArrGeneric) pos)
        [str_expr; delim_expr]
  
  | "toUpperCase" ->
      mk_expr_pos (TCECall (TCTFunc "fib_string_to_upper", [str_expr])) TCFibString pos
  
  | "toLowerCase" ->
      mk_expr_pos (TCECall (TCTFunc "fib_string_to_lower", [str_expr])) TCFibString pos
  
  | "trim" ->
      mk_expr_pos (TCECall (TCTFunc "fib_string_trim", [str_expr])) TCFibString pos
  
  | "toString" ->
      (* String.toString() is identity *)
      str_expr
  
  | "length" ->
      mk_expr_pos (TCEStringLength str_expr) TCInt32 pos
  
  | _ ->
      (* Fallback to generic String_method call *)
      mk_expr_pos (TCECall (TCTMethod ("String", ident method_name), str_expr :: arg_exprs)) result_tc pos

(* Convert map method call *)
and convert_map_call ctx map_expr args arg_exprs kind method_name value_type result_tc pos =
  let prefix = FiberusBuiltins.map_kind_prefix kind in
  
  (* ObjectMap needs key cast to FibObject*.
     When key is FibDynamic (e.g. from Dynamic-typed code), unbox via fib_dynamic_to_object
     instead of C pointer cast, since FibDynamic is a struct, not a pointer. *)
  let cast_key key_expr =
    if kind = FiberusBuiltins.MapObject then begin
      if key_expr.ctype = TCFibDynamic then
        mk_expr (TCEUnbox (key_expr, TCFibObject)) TCFibObject
      else
        mk_expr (TCECast (TCFibObject, key_expr)) TCFibObject
    end else key_expr
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
      (* When suffix is "_dynamic" but value isn't already FibDynamic, box it.
         This happens when e.g. map.set(key, true) where the map stores Dynamic values. *)
      let boxed_val = if suffix = "_dynamic" && val_expr.ctype <> TCFibDynamic then
        let result = mk_expr (TCEBox (val_expr, box_kind_of_type val_expr.ctype)) TCFibDynamic in
        if val_expr.pending_stmts <> [] then
          { result with pending_stmts = val_expr.pending_stmts; gc_roots = val_expr.gc_roots }
        else result
      else val_expr in
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "set" ^ suffix), [map_expr; key_expr; boxed_val])) TCVoid pos in
      let arg_pending = key_expr.pending_stmts @ boxed_val.pending_stmts in
      let arg_gc = key_expr.gc_roots + boxed_val.gc_roots in
      if arg_pending <> [] then { call with pending_stmts = arg_pending @ call.pending_stmts; gc_roots = arg_gc + call.gc_roots } else call
  
  | "get" ->
      let key_expr = if List.length arg_exprs > 0 then cast_key (List.nth arg_exprs 0) else mk_int 0l in
      (* Map.get() returns Null<T> - when the call site needs a nullable result (TCFibDynamic),
         we must use get_dynamic to preserve null semantics. Specialized getters like get_int
         return bare int32_t and can't represent null (they return 0 for missing keys).
         Only use specialized getters when the call site expects a concrete non-nullable type. *)
      let use_dynamic = (result_tc = TCFibDynamic) in
      let func_name = if use_dynamic then prefix ^ "get_dynamic" else get_func_name () in
      let ret_type = if use_dynamic then TCFibDynamic
        else match value_type with
          | TCInt32 | TCFloat64 | TCFibString | TCInt64 -> value_type
          | _ -> TCFibDynamic
      in
      let call = mk_expr_pos (TCECall (TCTFunc func_name, [map_expr; key_expr])) ret_type pos in
      if key_expr.pending_stmts <> [] then { call with pending_stmts = key_expr.pending_stmts @ call.pending_stmts; gc_roots = key_expr.gc_roots + call.gc_roots } else call
  
  | "exists" ->
      let key_expr = if List.length arg_exprs > 0 then cast_key (List.nth arg_exprs 0) else mk_int 0l in
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "exists"), [map_expr; key_expr])) TCBool pos in
      if key_expr.pending_stmts <> [] then { call with pending_stmts = key_expr.pending_stmts @ call.pending_stmts; gc_roots = key_expr.gc_roots + call.gc_roots } else call
  
  | "remove" ->
      let key_expr = if List.length arg_exprs > 0 then cast_key (List.nth arg_exprs 0) else mk_int 0l in
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "remove"), [map_expr; key_expr])) TCBool pos in
      if key_expr.pending_stmts <> [] then { call with pending_stmts = key_expr.pending_stmts @ call.pending_stmts; gc_roots = key_expr.gc_roots + call.gc_roots } else call
  
  | "keys" ->
      let iter_type = match kind with
        | FiberusBuiltins.MapInt -> TCRaw "FibIntMapKeyIterator*"
        | FiberusBuiltins.MapString -> TCRaw "FibStringMapKeyIterator*"
        | FiberusBuiltins.MapInt64 -> TCRaw "FibInt64MapKeyIterator*"
        | FiberusBuiltins.MapObject -> TCRaw "FibObjectMapKeyIterator*"
      in
      mk_expr_pos (TCECall (TCTFunc (prefix ^ "keys"), [map_expr])) iter_type pos
  
	| "iterator" ->
		let iter_type = match kind with
			| FiberusBuiltins.MapInt -> TCRaw "FibIntMapValueIterator*"
			| FiberusBuiltins.MapString -> TCRaw "FibStringMapValueIterator*"
			| FiberusBuiltins.MapInt64 -> TCRaw "FibInt64MapValueIterator*"
			| FiberusBuiltins.MapObject -> TCRaw "FibObjectMapValueIterator*"
		in
		mk_expr_pos (TCECall (TCTFunc (prefix ^ "iterator"), [map_expr])) iter_type pos

	| "keyValueIterator" ->
		let iter_tc = TCFibClass "haxe_iterators_MapKeyValueIterator" in
		let map_dyn = coerce_to_type map_expr TCFibDynamic in
		let call = mk_expr_pos (TCECall (TCTFunc "haxe_iterators_MapKeyValueIterator_new", [map_dyn])) iter_tc pos in
		if result_tc <> iter_tc then coerce_to_type call result_tc else call
  
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
  | Type.TInst (_, [_; t]) when kind = FiberusBuiltins.MapObject -> tc_type_of t
  | Type.TInst (_, [t]) -> tc_type_of t
  | _ -> TCFibDynamic

(* ============================================================================
 * Fiber.spawn Conversion Helpers
 * ============================================================================
 * These helpers generate code for Fiber.spawn/spawnOn/spawnAny/spawnWithStack.
 * The pattern uses pending_stmts to lift setup code to statement level,
 * avoiding GCC statement expressions.
 *
 * Generated code pattern:
 *   gc_mature_alloc_begin();
 *   FibClosure* _fc = FIB_CLOSURE_CREATE_FOR_FIBER_N(...);
 *   gc_push_temp_root([address of _fc]);
 *   Fiber* _fib = scheduler_spawn(..., _fc);
 *   gc_mature_alloc_end();
 *   gc_pop_temp_roots(1);
 *   [expression value is _fib]
 *)

(* Extract closure information from a Fiber.spawn argument *)
and extract_fiber_closure ctx arg =
  match arg.Type.eexpr with
  | Type.TFunction f ->
      (* Found a closure - register it as a fiber spawn closure *)
      let closure_name = fresh_closure_name ctx in
      let impl_name = closure_name ^ "_impl" in
      let free_vars = FiberusClosure.find_free_vars f in
      
      (* Convert captured variables to (capture_expr, var_name, type) triples.
         Use _gc.name for the capture expression when in a GC frame. *)
      let captures = List.map (fun v ->
        let name = ident v.v_name in
        let capture_expr =
          if ctx.in_gc_frame && gc_frame_has_var ctx name then
            Printf.sprintf "%s.%s" ctx.gc_frame_name name
          else name
        in
        (capture_expr, name, tc_type_of (Type.follow v.v_type))
      ) free_vars in
      
      (* Convert function body with fiber_spawn context and GCFrame tracking.
       * Same pattern as regular closures — build GCFrame in the conversion phase. *)
      let args = List.map (fun (v, _) ->
        { fa_name = ident v.v_name; fa_type = tc_type_of (Type.follow v.v_type) }
      ) f.tf_args in
      let ret_type = tc_type_of (Type.follow f.tf_type) in
      let cl_captures_list = List.mapi (fun i (_, name, typ) ->
        { cap_var = name; cap_type = typ; cap_index = i }
      ) captures in
      let frame_name = "_gc" in
      let frame_rooted_vars = Hashtbl.create 16 in
      let param_inits = ref [] in
      let initial_slots = ref [] in
      (* Always root _closure *)
      initial_slots := ("_closure", TCFibClosure) :: !initial_slots;
      Hashtbl.replace frame_rooted_vars "_closure" ();
      param_inits := ("_closure", mk_expr (TCELocal "_closure") TCFibClosure) :: !param_inits;
      (* GC-typed parameters *)
      List.iter (fun arg ->
        if needs_gc_root arg.fa_type then begin
          initial_slots := (arg.fa_name, arg.fa_type) :: !initial_slots;
          Hashtbl.replace frame_rooted_vars arg.fa_name ();
          param_inits := (arg.fa_name, mk_expr (TCELocal arg.fa_name) arg.fa_type) :: !param_inits
        end
      ) args;
      (* GC-typed captures *)
      List.iter (fun cap ->
        if needs_gc_root cap.cap_type then begin
          initial_slots := (cap.cap_var, cap.cap_type) :: !initial_slots;
          Hashtbl.replace frame_rooted_vars cap.cap_var ()
        end
      ) cl_captures_list;
      let body_ctx = { (ctx_for_scope ctx) with 
        current_ret_type = Some ret_type;
        closures = ctx.closures;
        in_gc_frame = true;
        gc_frame_name = frame_name;
        gc_frame_slots = List.rev !initial_slots;
        gc_frame_rooted_vars = frame_rooted_vars;
        func_gc_root_count = 0;
        gc_local_count = 0;  (* Reset: spawn closure has its own temp root scope *)
        in_fiber_spawn = true;
      } in
      let body_stmts = convert_stmt body_ctx f.tf_expr in
      let body_stmts = mark_volatile_for_try body_stmts in
      (* Build prologue *)
      let prologue = ref [TCSGCCtx] in
      let frame_info = gc_frame_build_info_with_inits body_ctx !param_inits in
      let has_gc_slots = frame_info.gfi_slots <> [] in
      if has_gc_slots then
        prologue := !prologue @ [TCSGCFrameDecl frame_info];
      if captures = [] then
        prologue := !prologue @ [TCSRaw "(void)_closure;"];
      List.iter (fun cap ->
        let extract_str = FiberusSourceWriter.capture_extract_expr cap in
        prologue := !prologue @ [TCSVar {
          vd_name = cap.cap_var; vd_type = cap.cap_type;
          vd_init = Some (mk_expr (TCERaw extract_str) cap.cap_type);
          vd_static = false; vd_const = false; vd_volatile = false;
        }];
        if needs_gc_root cap.cap_type then
          prologue := !prologue @ [TCSGCFrameAssign (frame_name, cap.cap_var, mk_expr (TCELocal cap.cap_var) cap.cap_type)]
      ) cl_captures_list;
      (* Epilogue: pop any legacy temp roots (from stack-alloc fields) + GC_FRAME_POP for fall-through *)
      let epilogue = if ret_type = TCVoid && not (ends_with_return f.tf_expr) then begin
        let temp_pop = if body_ctx.gc_local_count > 0 then [TCSGCPop body_ctx.gc_local_count] else [] in
        let frame_pop = if has_gc_slots then [TCSGCFramePop frame_name] else [] in
        temp_pop @ frame_pop
      end else [] in
      let full_body = !prologue @ body_stmts @ epilogue in
      
      (* Sync nested closures back to parent context *)
      ctx.closures <- body_ctx.closures;
      
      (* Create closure definition *)
      let closure_def = {
        cl_id = ctx.closure_counter - 1;
        cl_name = closure_name;
        cl_impl_name = impl_name;
        cl_args = args;
        cl_ret = ret_type;
        cl_captures = cl_captures_list;
        cl_body = full_body;
        cl_defaults = List.map (fun _ -> None) args;  (* Fiber spawn closures have no defaults *)
      } in
      ctx.closures <- closure_def :: ctx.closures;
      
      Some (closure_name, impl_name, captures, List.length f.tf_args)
  | _ ->
      (* Not a closure literal - will use simple Fiber_spawn *)
      None

(* Convert Fiber.spawn(closure) *)
and convert_fiber_spawn ctx spawn_func trampoline_func args pos =
  match args with
  | [arg] ->
      (match extract_fiber_closure ctx arg with
      | Some (closure_name, impl_name, captures, _arg_count) ->
          (* Generate unique variable names to avoid redefinition errors *)
          let (fc_name, fib_name, _id) = fresh_spawn_vars ctx in
          
          (* Build pending_stmts for setup code *)
          let pending = [
            (* gc_mature_alloc_begin(); *)
            TCSExpr (mk_expr (TCECall (TCTFunc "gc_mature_alloc_begin", [])) TCVoid);
          ] in
          
          (* Build closure creation expression *)
          let closure_expr = mk_expr (TCEClosureCreate {
            cc_name = closure_name;
            cc_impl_name = impl_name;
            cc_captures = captures;
            cc_arg_count = 0;  (* Fiber closures take 1 arg (FibDynamic) but dynamic calling not needed *)
            cc_for_fiber = true;
          }) TCFibClosure in
          
          (* FibClosure* _fcN = ...; *)
          let fc_var = TCSVar {
            vd_name = fc_name;
            vd_type = TCFibClosure;
            vd_init = Some closure_expr;
            vd_static = false;
            vd_const = false; vd_volatile = false;
          } in
          
          (* Root protection for _fcN during spawn *)
          let root_push, root_pop = if ctx.in_gc_frame then begin
            (* GCFrame mode: register _fcN as a frame slot *)
            gc_frame_add_slot ctx fc_name TCFibClosure;
            let assign = TCSGCFrameAssign (ctx.gc_frame_name, fc_name, mk_expr (TCELocal fc_name) TCFibClosure) in
            ([assign], [])
          end else begin
            (* Legacy mode: push/pop temp root *)
            let push = TCSExpr (mk_expr (TCECall (TCTFunc "gc_push_temp_root", 
              [mk_expr (TCECast (TCPointer (TCPointer TCVoid), mk_expr (TCEAddrOf (mk_expr (TCELocal fc_name) TCFibClosure)) (TCPointer TCFibClosure))) (TCPointer (TCPointer TCVoid))]
            )) TCVoid) in
            let pop = TCSExpr (mk_expr (TCECall (TCTFunc "gc_pop_temp_roots", [mk_int 1l])) TCVoid) in
            ([push], [pop])
          end in
          
          (* Fiber* _fibN = scheduler_spawn(trampoline, _fcN) *)
          let spawn_call = mk_expr (TCECall (TCTFunc spawn_func, [
            mk_expr (TCELocal trampoline_func) (TCPointer TCVoid);
            mk_expr (TCECast (TCPointer TCVoid, mk_expr (TCELocal fc_name) TCFibClosure)) (TCPointer TCVoid)
          ])) TCFiber in
          
          let fib_var = TCSVar {
            vd_name = fib_name;
            vd_type = TCFiber;
            vd_init = Some spawn_call;
            vd_static = false;
            vd_const = false; vd_volatile = false;
          } in
          
          (* gc_mature_alloc_end(); *)
          let alloc_end = TCSExpr (mk_expr (TCECall (TCTFunc "gc_mature_alloc_end", [])) TCVoid) in
          
          (* Final expression is just _fibN *)
          let result = mk_expr (TCELocal fib_name) TCFiber in
          
          (* Combine all pending statements *)
          let all_pending = pending @ [fc_var] @ root_push @ [fib_var; alloc_end] @ root_pop in
          
          with_pending all_pending result
          
      | None ->
          (* No closure - just call Fiber_spawn *)
          let arg_expr = convert_expr ctx arg in
          mk_expr_pos (TCECall (TCTFunc "Fiber_spawn", [arg_expr])) TCFiber pos)
  | _ ->
      mk_expr_pos (TCERaw "/* Fiber.spawn: wrong args */") TCFiber pos

(* Convert Fiber.spawnOn(threadId, closure) *)
and convert_fiber_spawn_on ctx tid_expr arg pos =
  match extract_fiber_closure ctx arg with
  | Some (closure_name, impl_name, captures, _arg_count) ->
      (* Generate unique variable names to avoid redefinition errors *)
      let (fc_name, fib_name, spawn_id) = fresh_spawn_vars ctx in
      let tid_name = Printf.sprintf "_tid%d" spawn_id in
      
      let pending = [
        (* int _tidN = tid_expr; *)
        TCSVar {
          vd_name = tid_name;
          vd_type = TCInt32;
          vd_init = Some tid_expr;
          vd_static = false; vd_const = false; vd_volatile = false;
        };
        (* gc_mature_alloc_begin(); *)
        TCSExpr (mk_expr (TCECall (TCTFunc "gc_mature_alloc_begin", [])) TCVoid);
      ] in
      
      let closure_expr = mk_expr (TCEClosureCreate {
        cc_name = closure_name;
        cc_impl_name = impl_name;
        cc_captures = captures;
        cc_arg_count = 0;
        cc_for_fiber = true;
      }) TCFibClosure in
      
      let fc_var = TCSVar {
        vd_name = fc_name;
        vd_type = TCFibClosure;
        vd_init = Some closure_expr;
        vd_static = false; vd_const = false; vd_volatile = false;
      } in
      
      (* Root protection for _fcN during spawn *)
      let root_push, root_pop = if ctx.in_gc_frame then begin
        gc_frame_add_slot ctx fc_name TCFibClosure;
        let assign = TCSGCFrameAssign (ctx.gc_frame_name, fc_name, mk_expr (TCELocal fc_name) TCFibClosure) in
        ([assign], [])
      end else begin
        let push = TCSExpr (mk_expr (TCECall (TCTFunc "gc_push_temp_root", 
          [mk_expr (TCECast (TCPointer (TCPointer TCVoid), mk_expr (TCEAddrOf (mk_expr (TCELocal fc_name) TCFibClosure)) (TCPointer TCFibClosure))) (TCPointer (TCPointer TCVoid))]
        )) TCVoid) in
        let pop = TCSExpr (mk_expr (TCECall (TCTFunc "gc_pop_temp_roots", [mk_int 1l])) TCVoid) in
        ([push], [pop])
      end in
      
      let spawn_call = mk_expr (TCECall (TCTFunc "scheduler_spawn_on", [
        mk_expr (TCELocal tid_name) TCInt32;
        mk_expr (TCELocal "_fib_spawn_on_closure_trampoline") (TCPointer TCVoid);
        mk_expr (TCECast (TCPointer TCVoid, mk_expr (TCELocal fc_name) TCFibClosure)) (TCPointer TCVoid)
      ])) TCFiber in
      
      let fib_var = TCSVar {
        vd_name = fib_name;
        vd_type = TCFiber;
        vd_init = Some spawn_call;
        vd_static = false; vd_const = false; vd_volatile = false;
      } in
      
      let alloc_end = TCSExpr (mk_expr (TCECall (TCTFunc "gc_mature_alloc_end", [])) TCVoid) in
      
      let result = mk_expr (TCELocal fib_name) TCFiber in
      let all_pending = pending @ [fc_var] @ root_push @ [fib_var; alloc_end] @ root_pop in
      
      with_pending all_pending result
      
  | None ->
      let arg_expr = convert_expr ctx arg in
      mk_expr_pos (TCECall (TCTFunc "Fiber_spawnOn", [tid_expr; arg_expr])) TCFiber pos

(* Convert Fiber.spawnWithStack(size, closure) *)
and convert_fiber_spawn_with_stack ctx size_expr arg pos =
  match extract_fiber_closure ctx arg with
  | Some (closure_name, impl_name, captures, _arg_count) ->
      (* Generate unique variable names to avoid redefinition errors *)
      let (fc_name, fib_name, spawn_id) = fresh_spawn_vars ctx in
      let sz_name = Printf.sprintf "_sz%d" spawn_id in
      
      let pending = [
        (* size_t _szN = size_expr; *)
        TCSVar {
          vd_name = sz_name;
          vd_type = TCUInt64;  (* size_t *)
          vd_init = Some (mk_expr (TCECast (TCUInt64, size_expr)) TCUInt64);
          vd_static = false; vd_const = false; vd_volatile = false;
        };
        (* gc_mature_alloc_begin(); *)
        TCSExpr (mk_expr (TCECall (TCTFunc "gc_mature_alloc_begin", [])) TCVoid);
      ] in
      
      let closure_expr = mk_expr (TCEClosureCreate {
        cc_name = closure_name;
        cc_impl_name = impl_name;
        cc_captures = captures;
        cc_arg_count = 0;
        cc_for_fiber = true;
      }) TCFibClosure in
      
      let fc_var = TCSVar {
        vd_name = fc_name;
        vd_type = TCFibClosure;
        vd_init = Some closure_expr;
        vd_static = false; vd_const = false; vd_volatile = false;
      } in
      
      (* Root protection for _fcN during spawn *)
      let root_push, root_pop = if ctx.in_gc_frame then begin
        gc_frame_add_slot ctx fc_name TCFibClosure;
        let assign = TCSGCFrameAssign (ctx.gc_frame_name, fc_name, mk_expr (TCELocal fc_name) TCFibClosure) in
        ([assign], [])
      end else begin
        let push = TCSExpr (mk_expr (TCECall (TCTFunc "gc_push_temp_root", 
          [mk_expr (TCECast (TCPointer (TCPointer TCVoid), mk_expr (TCEAddrOf (mk_expr (TCELocal fc_name) TCFibClosure)) (TCPointer TCFibClosure))) (TCPointer (TCPointer TCVoid))]
        )) TCVoid) in
        let pop = TCSExpr (mk_expr (TCECall (TCTFunc "gc_pop_temp_roots", [mk_int 1l])) TCVoid) in
        ([push], [pop])
      end in
      
      let spawn_call = mk_expr (TCECall (TCTFunc "scheduler_spawn_sized", [
        mk_expr (TCELocal sz_name) TCUInt64;
        mk_expr (TCELocal "_fib_spawn_closure_trampoline") (TCPointer TCVoid);
        mk_expr (TCECast (TCPointer TCVoid, mk_expr (TCELocal fc_name) TCFibClosure)) (TCPointer TCVoid)
      ])) TCFiber in
      
      let fib_var = TCSVar {
        vd_name = fib_name;
        vd_type = TCFiber;
        vd_init = Some spawn_call;
        vd_static = false; vd_const = false; vd_volatile = false;
      } in
      
      let alloc_end = TCSExpr (mk_expr (TCECall (TCTFunc "gc_mature_alloc_end", [])) TCVoid) in
      
      let result = mk_expr (TCELocal fib_name) TCFiber in
      let all_pending = pending @ [fc_var] @ root_push @ [fib_var; alloc_end] @ root_pop in
      
      with_pending all_pending result
      
  | None ->
      let arg_expr = convert_expr ctx arg in
      mk_expr_pos (TCECall (TCTFunc "Fiber_spawnWithStack", [size_expr; arg_expr])) TCFiber pos

and convert_call ctx callee args result_tc pos =
  (* Heap-allocate any anonymous objects in call arguments to prevent dangling
     stack pointers if the callee stores them (e.g. PosInfos in exceptions). *)
  let arg_exprs = List.map (fun a -> mark_anon_heap_alloc (convert_expr ctx a)) args in
  
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
      let arg_pending = arg.pending_stmts in
      let arg_gc = arg.gc_roots in
      let propagate r = { r with pending_stmts = arg_pending @ r.pending_stmts;
                                  gc_roots = arg_gc + r.gc_roots } in
      (match arg.ctype with
       | TCFibString ->
           (* Null string must become the string "null", not a null pointer.
              Cache arg in a temp to avoid double evaluation of side effects. *)
           let tmp_name = gen_gc_temp_name () in
           let tmp_decl = TCSVar { vd_name = tmp_name; vd_type = TCFibString; vd_init = Some { arg with pending_stmts = [] }; vd_static = false; vd_const = false; vd_volatile = false } in
           let tmp_ref = mk_expr (TCELocal tmp_name) TCFibString in
           let null_str = mk_expr (TCEString "null") TCFibString in
           let ternary = mk_expr_pos (TCETernary (tmp_ref, tmp_ref, null_str)) TCFibString pos in
           { ternary with pending_stmts = arg_pending @ [tmp_decl]; gc_roots = arg_gc + ternary.gc_roots }
       | TCInt32 -> propagate (mk_expr_pos (TCECall (TCTFunc "fib_string_from_int", [arg])) TCFibString pos)
       | TCFloat64 | TCFloat32 -> propagate (mk_expr_pos (TCECall (TCTFunc "fib_string_from_float", [arg])) TCFibString pos)
       | TCInt64 -> propagate (mk_expr_pos (TCECall (TCTFunc "fib_string_from_int64", [arg])) TCFibString pos)
       | TCBool -> propagate (mk_expr_pos (TCETernary (arg, mk_expr (TCEString "true") TCFibString, mk_expr (TCEString "false") TCFibString)) TCFibString pos)
       | TCFibDynamic -> propagate (mk_expr_pos (TCECall (TCTFunc "fib_dynamic_to_string", [arg])) TCFibString pos)
       | TCFibClass _ | TCFibObject ->
           propagate (mk_expr_pos (TCECall (TCTFunc "fib_object_to_string", [mk_expr (TCECast (TCFibObject, arg)) TCFibObject])) TCFibString pos)
       | _ ->
           let dyn = mk_expr (TCEBox (arg, box_kind_of_type arg.ctype)) TCFibDynamic in
           propagate (mk_expr_pos (TCECall (TCTFunc "fib_dynamic_to_string", [dyn])) TCFibString pos))
  
  | Some FiberusBuiltins.IStdIsOfType ->
      (* Std.isOfType(value, Type) - check type at runtime *)
      (match args with
       | [_; type_arg] ->
           let val_expr = if arg_exprs = [] then mk_int 0l else List.hd arg_exprs in
           (match type_arg.Type.eexpr with
            | Type.TTypeExpr (Type.TClassDecl c) ->
                (match c.cl_path with
                 | ([], "String") ->
                      if val_expr.ctype = TCFibString then
                        (* String pointer: null check — null is not a String *)
                        let null_lit = mk_expr_pos TCENull TCFibString pos in
                        mk_expr_pos (TCEBinop (TCOpNeq, val_expr, null_lit)) TCBool pos
                      else
                        let dyn_val = coerce_to_type val_expr TCFibDynamic in
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_string", [dyn_val])) TCBool pos in
                        { call with pending_stmts = collect_pending [dyn_val] @ call.pending_stmts }
                 | ([], "Array") ->
                      (match val_expr.ctype with
                       | TCFibArray _ ->
                        (* Array pointer: null check — null is not an Array *)
                        let null_lit = mk_expr_pos TCENull (val_expr.ctype) pos in
                        mk_expr_pos (TCEBinop (TCOpNeq, val_expr, null_lit)) TCBool pos
                       | _ ->
                        let dyn_val = coerce_to_type val_expr TCFibDynamic in
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_array", [dyn_val])) TCBool pos in
                        { call with pending_stmts = collect_pending [dyn_val] @ call.pending_stmts })
                 | ([], "Int") ->
                      if val_expr.ctype = TCFibDynamic then
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_int", [val_expr])) TCBool pos in
                        { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      else if val_expr.ctype = TCInt32 || val_expr.ctype = TCInt64 then
                        mk_expr_pos (TCEBool true) TCBool pos
                      else if val_expr.ctype = TCFloat64 || val_expr.ctype = TCFloat32 then
                        (* Float value: check if it has no fractional part *)
                        let boxed = mk_expr (TCEBox (val_expr, box_kind_of_type val_expr.ctype)) TCFibDynamic in
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_int", [boxed])) TCBool pos in
                        { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      else
                        mk_expr_pos (TCEBool false) TCBool pos
                 | ([], "Float") ->
                      if val_expr.ctype = TCFibDynamic then
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_float", [val_expr])) TCBool pos in
                        { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      else if val_expr.ctype = TCFloat64 || val_expr.ctype = TCFloat32
                             || val_expr.ctype = TCInt32 || val_expr.ctype = TCInt64 then
                        mk_expr_pos (TCEBool true) TCBool pos
                      else
                        mk_expr_pos (TCEBool false) TCBool pos
                 | ([], "Bool") ->
                      if val_expr.ctype = TCFibDynamic then
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_bool", [val_expr])) TCBool pos in
                        { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      else if val_expr.ctype = TCBool then
                        mk_expr_pos (TCEBool true) TCBool pos
                      else
                        mk_expr_pos (TCEBool false) TCBool pos
                 | ([], "Dynamic") ->
                       (* Std.isOfType(x, Dynamic) is true for any non-null value *)
                       if val_expr.ctype = TCFibDynamic then
                         let is_null = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [val_expr])) TCBool in
                         let result = mk_expr_pos (TCEUnop (TCUNot, is_null)) TCBool pos in
                         { result with pending_stmts = val_expr.pending_stmts @ result.pending_stmts }
                       else
                         mk_expr_pos (TCEBool true) TCBool pos
                 | (["haxe";"ds"], ("IntMap" | "StringMap" | "ObjectMap" | "Int64Map")) ->
                       (* Extern Map classes: generate instanceof check against sentinel class *)
                       let target_class = flat_path c.cl_path in
                       if val_expr.ctype = TCFibDynamic then
                         let class_ptr = mk_expr (TCEAddrOf (mk_expr (TCELocal (target_class ^ "_class")) TCVoid)) (TCPointer TCVoid) in
                         let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_instanceof", [val_expr; class_ptr])) TCBool pos in
                         { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                       else begin
                         let cast_obj = mk_expr (TCECast (TCFibObject, val_expr)) TCFibObject in
                         let class_ptr = mk_expr (TCEAddrOf (mk_expr (TCELocal (target_class ^ "_class")) TCVoid)) (TCPointer TCVoid) in
                         let call = mk_expr_pos (TCECall (TCTFunc "fib_object_instanceof", [cast_obj; class_ptr])) TCBool pos in
                         { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                       end
                 | _ when not (has_class_flag c CExtern) ->
                      let target_class = flat_path c.cl_path in
                      if val_expr.ctype = TCFibDynamic then
                        (* For Dynamic values, must check type is OBJECT before casting *)
                         let class_ptr = mk_expr (TCEAddrOf (mk_expr (TCELocal (target_class ^ "_class")) TCVoid)) (TCPointer TCVoid) in
                         let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_instanceof", [val_expr; class_ptr])) TCBool pos in
                         { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                       else begin
                         (* For non-Dynamic typed values: only object pointer types can be instanceof a class.
                            String, Int, Float, Bool, Array, Closure etc. are never instances of a user class. *)
                         match val_expr.ctype with
                         | TCFibString | TCInt32 | TCInt64 | TCFloat64 | TCFloat32 | TCBool
                         | TCFibClosure | TCFibArray _ | TCVoid ->
                           mk_expr_pos (TCEBool false) TCBool pos
                         | _ ->
                           let cast_obj = mk_expr (TCECast (TCFibObject, val_expr)) TCFibObject in
                           let class_ptr = mk_expr (TCEAddrOf (mk_expr (TCELocal (target_class ^ "_class")) TCVoid)) (TCPointer TCVoid) in
                           let call = mk_expr_pos (TCECall (TCTFunc "fib_object_instanceof", [cast_obj; class_ptr])) TCBool pos in
                           { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      end
                 | _ -> mk_expr_pos (TCEBool false) TCBool pos)
            | Type.TTypeExpr (Type.TAbstractDecl a) ->
                (match a.a_path with
                 | ([], "Int") ->
                      if val_expr.ctype = TCFibDynamic then
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_int", [val_expr])) TCBool pos in
                        { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      else if val_expr.ctype = TCInt32 || val_expr.ctype = TCInt64 then
                        mk_expr_pos (TCEBool true) TCBool pos
                      else if val_expr.ctype = TCFloat64 || val_expr.ctype = TCFloat32 then
                        let boxed = mk_expr (TCEBox (val_expr, box_kind_of_type val_expr.ctype)) TCFibDynamic in
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_int", [boxed])) TCBool pos in
                        { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      else
                        mk_expr_pos (TCEBool false) TCBool pos
                 | ([], "Float") ->
                      if val_expr.ctype = TCFibDynamic then
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_float", [val_expr])) TCBool pos in
                        { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      else if val_expr.ctype = TCFloat64 || val_expr.ctype = TCFloat32
                             || val_expr.ctype = TCInt32 || val_expr.ctype = TCInt64 then
                        mk_expr_pos (TCEBool true) TCBool pos
                      else
                        mk_expr_pos (TCEBool false) TCBool pos
                 | ([], "Bool") ->
                      if val_expr.ctype = TCFibDynamic then
                        let call = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_bool", [val_expr])) TCBool pos in
                        { call with pending_stmts = val_expr.pending_stmts @ call.pending_stmts }
                      else if val_expr.ctype = TCBool then
                        mk_expr_pos (TCEBool true) TCBool pos
                      else
                        mk_expr_pos (TCEBool false) TCBool pos
                  | ([], "Dynamic") ->
                       if val_expr.ctype = TCFibDynamic then
                         let is_null = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [val_expr])) TCBool in
                         let result = mk_expr_pos (TCEUnop (TCUNot, is_null)) TCBool pos in
                         { result with pending_stmts = val_expr.pending_stmts @ result.pending_stmts }
                       else
                         mk_expr_pos (TCEBool true) TCBool pos
                  | ([], ("Class" | "Enum")) ->
                       (* Class/Enum sentinel checks: Std.isOfType(v, Class) or Std.isOfType(v, Enum)
                          Class and Enum are @:coreType abstracts in Haxe, so they arrive as TAbstractDecl.
                          Must use fib_instanceof_dynamic which handles FIB_TYPE_CLASS values
                          and distinguishes Class vs Enum via FIB_ENUM_META_MAGIC. *)
                       let sentinel_name = (match a.a_path with (_, n) -> n) ^ "_class" in
                       let dyn_val = coerce_to_type val_expr TCFibDynamic in
                       let dyn_type = mk_expr (TCERaw (Printf.sprintf
                         "(FibDynamic){ .type = FIB_TYPE_CLASS, .data = { .ptrVal = &%s } }" sentinel_name)) TCFibDynamic in
                       let call = mk_expr_pos (TCECall (TCTFunc "fib_instanceof_dynamic", [dyn_val; dyn_type])) TCBool pos in
                       { call with pending_stmts = collect_pending [dyn_val] @ call.pending_stmts }
                   | _ -> mk_expr_pos (TCEBool false) TCBool pos)
             | _ ->
                 (* Abstract type not recognized — fall through to runtime check *)
                 let type_expr = convert_expr ctx type_arg in
                 let dyn_val = coerce_to_type val_expr TCFibDynamic in
                 let dyn_type = coerce_to_type type_expr TCFibDynamic in
                 let call = mk_expr_pos (TCECall (TCTFunc "fib_instanceof_dynamic", [dyn_val; dyn_type])) TCBool pos in
                 { call with pending_stmts = collect_pending [dyn_val; dyn_type] @ call.pending_stmts })
        | _ -> mk_expr_pos (TCEBool false) TCBool pos)
  
  (* Fiber.spawn - spawn a fiber with a closure *)
  | Some FiberusBuiltins.IFiberSpawn ->
      convert_fiber_spawn ctx "scheduler_spawn" "_fib_spawn_closure_trampoline" args pos
  
  (* Fiber.spawnOn - spawn a fiber on a specific thread *)
  | Some FiberusBuiltins.IFiberSpawnOn ->
      (match args with
      | [thread_id; closure_arg] ->
          (* Convert thread_id first *)
          let tid_expr = convert_expr ctx thread_id in
          (* Use dedicated spawnOn converter that handles tid + closure *)
          convert_fiber_spawn_on ctx tid_expr closure_arg pos
      | _ -> mk_expr_pos (TCERaw "/* Fiber.spawnOn: wrong args */") TCFiber pos)
  
  (* Fiber.spawnAny - spawn a fiber on any available thread *)
  | Some FiberusBuiltins.IFiberSpawnAny ->
      convert_fiber_spawn ctx "scheduler_spawn_any" "_fib_spawn_on_closure_trampoline" args pos
  
  (* Fiber.spawnWithStack - spawn a fiber with custom stack size *)
  | Some FiberusBuiltins.IFiberSpawnWithStack ->
      (match args with
      | [stack_size; closure_arg] ->
          let size_expr = convert_expr ctx stack_size in
          convert_fiber_spawn_with_stack ctx size_expr closure_arg pos
      | _ -> mk_expr_pos (TCERaw "/* Fiber.spawnWithStack: wrong args */") TCFiber pos)
  
  (* trace(msg, infos) -> haxe_Log_trace(boxed_msg, infos) *)
  | Some FiberusBuiltins.ITrace ->
      (match args with
      | [msg; infos] ->
          let msg_expr = convert_expr ctx msg in
          let infos_expr = convert_expr ctx infos in
          (* Box the message to FibDynamic based on its type *)
          let boxed_msg = match msg_expr.ctype with
            | TCFibString -> mk_expr (TCECall (TCTFunc "fib_string_to_dynamic", [msg_expr])) TCFibDynamic
            | TCInt32 -> mk_expr (TCECall (TCTFunc "fib_dynamic_int", [msg_expr])) TCFibDynamic
            | TCFloat64 -> mk_expr (TCECall (TCTFunc "fib_dynamic_float", [msg_expr])) TCFibDynamic
            | TCBool -> mk_expr (TCECall (TCTFunc "fib_dynamic_bool", [msg_expr])) TCFibDynamic
            | TCFibDynamic -> msg_expr
            | _ -> 
                (* Object or unknown type - convert to FibDynamic via object *)
                let cast_obj = mk_expr (TCECast (TCFibObject, msg_expr)) TCFibObject in
                mk_expr (TCECall (TCTFunc "fib_dynamic_object", [cast_obj])) TCFibDynamic
          in
          (* Combine pending_stmts from both expressions *)
          let all_pending = msg_expr.pending_stmts @ infos_expr.pending_stmts in
          let call_expr = mk_expr (TCECall (TCTFunc "haxe_Log_trace", [boxed_msg; infos_expr])) TCVoid in
          { call_expr with pending_stmts = all_pending; cpos = pos }
      | [msg] ->
          (* trace with just message, no infos - create null infos *)
          let msg_expr = convert_expr ctx msg in
          let boxed_msg = match msg_expr.ctype with
            | TCFibString -> mk_expr (TCECall (TCTFunc "fib_string_to_dynamic", [msg_expr])) TCFibDynamic
            | TCInt32 -> mk_expr (TCECall (TCTFunc "fib_dynamic_int", [msg_expr])) TCFibDynamic
            | TCFloat64 -> mk_expr (TCECall (TCTFunc "fib_dynamic_float", [msg_expr])) TCFibDynamic
            | TCBool -> mk_expr (TCECall (TCTFunc "fib_dynamic_bool", [msg_expr])) TCFibDynamic
            | TCFibDynamic -> msg_expr
            | _ -> 
                let cast_obj = mk_expr (TCECast (TCFibObject, msg_expr)) TCFibObject in
                mk_expr (TCECall (TCTFunc "fib_dynamic_object", [cast_obj])) TCFibDynamic
          in
          let null_infos = mk_expr TCENull (TCPointer TCVoid) in
          let call_expr = mk_expr (TCECall (TCTFunc "haxe_Log_trace", [boxed_msg; null_infos])) TCVoid in
          { call_expr with pending_stmts = msg_expr.pending_stmts; cpos = pos }
      | _ -> mk_expr_pos (TCERaw "/* trace: wrong number of args */") TCVoid pos)
  
  (* __fiberus__() raw code emission - concatenate string literals with converted expressions *)
  | Some FiberusBuiltins.IFiberus ->
      (* Build raw C code by iterating through arguments:
         - String constants are emitted directly
         - Other expressions are converted to C-AST and serialized
         
         IMPORTANT: We need to collect pending_stmts from arguments that may
         have been extracted for GC safety (e.g., field access on array elements).
         These pending_stmts declare temp variables that must be emitted BEFORE
         the raw code that uses them. *)
      let buf = Buffer.create 64 in
      let all_pending = ref [] in
      let total_gc_roots = ref 0 in
      List.iter (fun arg ->
        match arg.Type.eexpr with
        | Type.TConst (Type.TString s) -> Buffer.add_string buf s
        | _ ->
            (* Convert expression to C-AST and serialize via SourceWriter *)
            let arg_expr = convert_expr ctx arg in
            (* Collect pending_stmts for later emission *)
            all_pending := !all_pending @ arg_expr.pending_stmts;
            total_gc_roots := !total_gc_roots + arg_expr.gc_roots;
            let w = FiberusSourceWriter.create () in
            FiberusSourceWriter.write_expr w arg_expr;
            Buffer.add_string buf (FiberusSourceWriter.contents w)
      ) args;
      let result = mk_expr_pos (TCERaw (Buffer.contents buf)) result_tc pos in
      { result with pending_stmts = !all_pending; gc_roots = !total_gc_roots }
  
  | None ->
  
  (* Helper to coerce argument to expected parameter type.
     default_expr is an optional Haxe AST expression for the parameter's default value.
     When the arg is null and a non-null default is provided, use the default instead of 0. *)
  let coerce_arg ?(default_expr : Type.texpr option = None) arg_expr param_tc =
    (* Special handling for null - convert to appropriate default for primitives *)
    let is_null_expr = match arg_expr.cexpr with TCENull -> true | _ -> false in
    let is_dynamic_null = 
      match arg_expr.cexpr with 
      | TCECall (TCTFunc "fib_dynamic_null", []) -> true 
      | _ -> false 
    in
    let result =
      if (is_null_expr || is_dynamic_null) && param_tc <> TCFibDynamic then
        (* Try to use the function's actual default value instead of type zero *)
        let from_default = match default_expr with
          | Some { Type.eexpr = Type.TConst c } -> begin match c with
              | Type.TNull -> None  (* default is null itself - use type zero *)
              | Type.TInt i -> Some (mk_int i)
              | Type.TFloat s -> Some (mk_expr (TCEFloat s) param_tc)
              | Type.TBool b -> Some (mk_expr (TCEBool b) TCBool)
              | Type.TString s -> Some (mk_expr (TCEString s) TCFibString)
              | _ -> None
            end
          | Some default_e ->
            (* Non-constant default (enum constructors, etc.): convert the
               Haxe AST expression to get the actual value. *)
            Some (convert_expr ctx default_e)
          | None -> None
        in
        begin match from_default with
        | Some e -> e
        | None ->
          (* No explicit default or default is null - use type's zero value *)
          match param_tc with
          | TCInt32 | TCInt8 | TCInt16 | TCUInt8 | TCUInt16 | TCUInt32 -> mk_int 0l
          | TCInt64 | TCUInt64 -> mk_expr (TCEInt64 0L) param_tc
          | TCFloat32 | TCFloat64 -> mk_expr (TCEFloat "0.0") param_tc
          | TCBool -> mk_expr (TCEBool false) TCBool
          | _ -> mk_expr TCENull param_tc  (* Pointer types can use NULL *)
        end
      else if arg_expr.ctype = param_tc then arg_expr
      else if param_tc = TCFibDynamic && arg_expr.ctype <> TCFibDynamic then
        (* Box to FibDynamic *)
        mk_expr (TCEBox (arg_expr, box_kind_of_type arg_expr.ctype)) TCFibDynamic
      else if arg_expr.ctype = TCFibDynamic && param_tc <> TCFibDynamic then begin
        (* Unbox from FibDynamic - if default_expr is available and param is a primitive,
           check for null at runtime and substitute the default value *)
        let unboxed = mk_expr (TCEUnbox (arg_expr, param_tc)) param_tc in
        let is_primitive_tc = match param_tc with
          | TCInt32 | TCInt8 | TCInt16 | TCUInt8 | TCUInt16 | TCUInt32
          | TCInt64 | TCUInt64 | TCFloat32 | TCFloat64 | TCBool -> true
          | _ -> false in
        match default_expr, is_primitive_tc with
        | Some { Type.eexpr = Type.TConst c }, true when c <> Type.TNull ->
          let default_val = match c with
            | Type.TInt i -> mk_expr (if param_tc = TCFloat64 || param_tc = TCFloat32 then TCEFloat (Int32.to_string i ^ ".0") else TCEInt i) param_tc
            | Type.TFloat s -> mk_expr (TCEFloat s) param_tc
            | Type.TBool b -> mk_expr (TCEBool b) param_tc
            | _ -> unboxed  (* fallback: no null guard for non-primitive defaults *)
          in
          if default_val != unboxed then
            let null_check = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [arg_expr])) TCBool in
            mk_expr (TCETernary (null_check, default_val, unboxed)) param_tc
          else unboxed
        | _ -> unboxed
      end
      else if (arg_expr.ctype = TCInt32 || arg_expr.ctype = TCInt64) && (param_tc = TCFloat64 || param_tc = TCFloat32) then
        (* Numeric promotion: Int -> Float *)
        mk_expr (TCECast (param_tc, arg_expr)) param_tc
      else if (arg_expr.ctype = TCFloat64 || arg_expr.ctype = TCFloat32) && (param_tc = TCInt32 || param_tc = TCInt64) then
        (* Numeric truncation: Float -> Int *)
        mk_expr (TCECast (param_tc, arg_expr)) param_tc
      else
        arg_expr
    in
    (* Propagate pending_stmts from the original argument expression *)
    if arg_expr.pending_stmts <> [] && result.pending_stmts = [] then
      { result with pending_stmts = arg_expr.pending_stmts; gc_roots = arg_expr.gc_roots + result.gc_roots }
    else
      result
  in
  
  (* Get parameter types from function type *)
  let get_param_tc_types func_type =
    match Type.follow func_type with
    | Type.TFun (params, _) -> List.map (fun (_, _, t) -> tc_type_of t) params
    | _ -> []
  in

  (* Get parameter types for closure calls, respecting the optional flag.
     CTFunction annotations like (Int, ?Int)->Int store bare Int with opt=true,
     but closure impls/thunks use FibDynamic for optional primitives (Null<T>).
     This variant ensures the function pointer cast matches the actual thunk signature. *)
  let get_closure_param_tc_types func_type =
    match Type.follow func_type with
    | Type.TFun (params, _) -> List.map (fun (_, opt, t) ->
        let tc = tc_type_of t in
        if opt then
          match tc with
          | TCInt32 | TCInt64 | TCFloat64 | TCFloat32 | TCBool -> TCFibDynamic
          | _ -> tc
        else tc
      ) params
    | _ -> []
  in
  
  (* Extract default value expressions from a class field's function definition *)
  let get_cf_defaults (cf : Type.tclass_field) : Type.texpr option list =
    match cf.cf_expr with
    | Some { Type.eexpr = Type.TFunction f } ->
        List.map (fun (_, default_opt) -> default_opt) f.tf_args
    | _ -> []
  in

  (* Coerce all arguments to match parameter types.
     cf_opt: optional class field for looking up default parameter values. *)
  let coerce_args ?(cf_opt : Type.tclass_field option = None) arg_exprs param_types =
    let defaults = match cf_opt with
      | Some cf -> get_cf_defaults cf
      | None -> []
    in
    let rec coerce acc args params defs =
      match args, params, defs with
      | [], _, _ -> List.rev acc
      | arg :: rest_args, param :: rest_params, def :: rest_defs ->
          coerce (coerce_arg ~default_expr:def arg param :: acc) rest_args rest_params rest_defs
      | arg :: rest_args, param :: rest_params, [] ->
          coerce (coerce_arg arg param :: acc) rest_args rest_params []
      | arg :: rest_args, [], _ ->
          (* More args than params - pass as-is *)
          coerce (arg :: acc) rest_args [] []
    in
    coerce [] arg_exprs param_types defaults
  in
  
  match callee.eexpr with
  (* String.fromCharCode(code) -> fib_string_from_char_code(code) *)
  | TField (_, FStatic ({ cl_path = ([], "String") }, { cf_name = "fromCharCode" })) ->
      let coerced_args = coerce_args arg_exprs [TCInt32] in
      let args_pending = collect_pending coerced_args in
      let call = mk_expr_pos (TCECall (TCTFunc "fib_string_from_char_code", coerced_args)) result_tc pos in
      { call with pending_stmts = args_pending @ call.pending_stmts }

  (* Static dynamic function call — dispatch through closure variable via fn_dynamic.
     Must use TCEDynamicCall (not TCEClosureCall) because the closure may be reassigned
     to any function with a compatible signature, whose ->fn has different typed parameters.
     fn_dynamic takes all args as FibDynamic and handles unboxing inside the thunk. *)
  | TField (_, FStatic (c, cf)) when (match cf.cf_kind with Method MethDynamic -> true | _ -> false) ->
      let class_name = flat_path c.cl_path in
      let param_types = get_param_tc_types cf.cf_type in
      let coerced_args = coerce_args ~cf_opt:(Some cf) arg_exprs param_types in
      let args_pending = collect_pending coerced_args in
      (* Read the __dyn_ variable and wrap as FibDynamic for _fib_dyn_call_N *)
      let dyn_var = mk_expr (TCEStatic (class_name, "_dyn_" ^ ident cf.cf_name)) (TCPointer TCVoid) in
      let closure_as_dyn = mk_expr (TCECall (TCTFunc "fib_dynamic_object", [
        mk_expr (TCECast (TCFibObject, dyn_var)) TCFibObject
      ])) TCFibDynamic in
      (* Box all args to FibDynamic *)
      let box_arg arg =
        match arg.ctype with
        | TCFibDynamic -> arg
        | TCInt32 -> mk_expr (TCECall (TCTFunc "fib_dynamic_int", [arg])) TCFibDynamic
        | TCInt64 -> mk_expr (TCECall (TCTFunc "fib_dynamic_int64", [arg])) TCFibDynamic
        | TCFloat64 -> mk_expr (TCECall (TCTFunc "fib_dynamic_float", [arg])) TCFibDynamic
        | TCBool -> mk_expr (TCECall (TCTFunc "fib_dynamic_bool", [arg])) TCFibDynamic
        | TCFibString -> mk_expr (TCECall (TCTFunc "fib_dynamic_string", [arg])) TCFibDynamic
        | TCFibArray _ -> mk_expr (TCECall (TCTFunc "fib_dynamic_array", [mk_expr (TCECast (TCFibArray TCArrGeneric, arg)) (TCFibArray TCArrGeneric)])) TCFibDynamic
        | _ -> mk_expr (TCECall (TCTFunc "fib_dynamic_object", [mk_expr (TCECast (TCFibObject, arg)) TCFibObject])) TCFibDynamic
      in
      let boxed_args = List.map box_arg coerced_args in
      let dyn_result = mk_expr_pos (TCEDynamicCall {
        closure = closure_as_dyn;
        args = boxed_args;
      }) TCFibDynamic pos in
      (* Unbox result if needed *)
      let result = match result_tc with
        | TCFibDynamic -> dyn_result
        | TCVoid -> dyn_result  (* void calls just discard the result *)
        | TCInt32 -> mk_expr (TCECall (TCTFunc "fib_dynamic_to_int", [dyn_result])) TCInt32
        | TCFloat64 -> mk_expr (TCECall (TCTFunc "fib_dynamic_to_float", [dyn_result])) TCFloat64
        | TCBool -> mk_expr (TCECall (TCTFunc "fib_dynamic_to_bool", [dyn_result])) TCBool
        | TCFibString -> mk_expr (TCECall (TCTFunc "fib_dynamic_coerce_string", [dyn_result])) TCFibString
        | _ -> mk_expr (TCECast (result_tc, dyn_result)) result_tc
      in
      { result with pending_stmts = args_pending @ dyn_result.pending_stmts }

   (* Static variable of function type — direct call if generated as plain function,
      closure call if stored as FibClosure variable.
      Uses Abstract.follow_with_abstracts to also match @:callable abstracts whose
      underlying type is TFun (e.g. abstract Foo(Bool->Void)). *)
   | TField (_, FStatic (c, cf)) when (match cf.cf_kind with Var _ -> true | _ -> false)
       && (match Abstract.follow_with_abstracts cf.cf_type with Type.TFun _ -> true | _ -> false) ->
       let class_name = flat_path c.cl_path in
       let resolved_type = Abstract.follow_with_abstracts cf.cf_type in
       let param_types = match resolved_type with
         | Type.TFun (params, _) -> List.map (fun (_, _, t) -> tc_type_of t) params
         | _ -> []
       in
       let coerced_args = coerce_args ~cf_opt:(Some cf) arg_exprs param_types in
       let args_pending = collect_pending coerced_args in
       (* When cf_expr is TFunction, genfiberus generates a plain C function (no variable decl).
             In that case, emit a direct call instead of a closure call. *)
       let is_plain_function = match cf.cf_expr with
         | Some { eexpr = TFunction _ } -> true
         | _ -> false
       in
       if is_plain_function then begin
         let method_name = ident cf.cf_name in
         let erased_ret_tc = match resolved_type with
           | Type.TFun (_, ret) -> tc_type_of ret
           | _ -> result_tc
         in
         let call = mk_expr_pos (TCECall (TCTMethod (class_name, method_name), coerced_args)) erased_ret_tc pos in
         let call = { call with pending_stmts = args_pending @ call.pending_stmts } in
         if erased_ret_tc <> result_tc then coerce_to_type call result_tc else call
        end else begin
          (* Check if the closure's typed ->fn might have different param types than
             what we expect. This happens when any param is a type parameter, anon,
             or pointer-typed class/interface -- the actual closure may have FibDynamic
             params due to generic erasure or structural typing. *)
          let needs_dynamic_dispatch =
            match resolved_type with
            | Type.TFun (params, _) ->
              List.exists (fun (_, _, t) ->
                match Type.follow t with
                | Type.TInst ({ cl_kind = KTypeParameter _ }, _) -> true
                | Type.TAnon _ -> true
                | Type.TInst _ | Type.TAbstract _ ->
                  (match tc_type_of t with
                   | TCFibClass _ | TCFibObject | TCFibClosure | TCPointer _
                   | TCFibString | TCFibArray _ -> true
                   | _ -> false)
                | _ -> false
              ) params
            | _ -> false
          in
          if needs_dynamic_dispatch then begin
            let closure_expr = mk_expr (TCEStatic (class_name, ident cf.cf_name)) TCFibClosure in
            let boxed_closure = mk_expr (TCEBox (closure_expr, TCBoxClosure)) TCFibDynamic in
            let boxed_args = box_args_for_dynamic_call arg_exprs in
            let dyn_call = mk_expr_pos (TCEDynamicCall { closure = boxed_closure; args = boxed_args }) TCFibDynamic pos in
            let call = { dyn_call with pending_stmts = args_pending @ dyn_call.pending_stmts } in
            unwrap_dynamic_result call result_tc
          end else begin
            let closure_expr = mk_expr (TCEStatic (class_name, ident cf.cf_name)) TCFibClosure in
            let arg_types = if param_types <> [] then param_types
                            else List.map (fun e -> e.ctype) coerced_args in
            let call = mk_expr_pos (TCEClosureCall {
              closure = closure_expr;
              arg_types = arg_types;
              ret_type = result_tc;
              args = coerced_args;
            }) result_tc pos in
            { call with pending_stmts = args_pending @ call.pending_stmts }
          end
        end

   (* Static variable of Dynamic type used as callable -- must use dynamic dispatch
      because the closure's ->fn may have any typed signature. TCEDynamicCall goes
      through ->fn_dynamic which accepts FibDynamic args and unboxes correctly. *)
   | TField (_, FStatic (c, cf)) when (match cf.cf_kind with Var _ -> true | _ -> false)
       && (tc_type_of cf.cf_type = TCFibDynamic) ->
       let class_name = flat_path c.cl_path in
       let args_pending = collect_pending arg_exprs in
       let boxed_args = box_args_for_dynamic_call arg_exprs in
       let dyn_var = mk_expr (TCEStatic (class_name, ident cf.cf_name)) TCFibDynamic in
       let dyn_call = mk_expr_pos (TCEDynamicCall { closure = dyn_var; args = boxed_args }) TCFibDynamic pos in
       let call = { dyn_call with pending_stmts = args_pending @ dyn_call.pending_stmts } in
       if result_tc <> TCFibDynamic then coerce_to_type call result_tc else call

   (* Extern static method call with @:native — direct C function call.
      This only triggers when the method itself has @:native metadata,
      which indicates a user-defined extern mapping to a specific C function.
      Fiberus runtime extern classes (Counter, GC, Fiber, etc.) don't use
      @:native on methods, so they fall through to the regular TCTMethod path.

      Callback handling: if any parameter has a function type (TFun), the
      codegen generates a trampoline function + global FibCallbackCtx* and
      replaces the closure argument with the trampoline function pointer.
      The trampoline exits the GC-free zone, marshals C args to FibDynamic,
      invokes the closure via fib_callback_invoke, and re-enters the zone.

      When callbacks are present, @:gcBlocking is implied — the call is
      always wrapped in enter/exit gc_free zone because the trampoline
      expects to be called from within a gc_free zone. *)
   | TField (_, FStatic (c, cf)) when has_class_flag c CExtern && Meta.has Meta.Native cf.cf_meta ->
       let native_name = match get_meta_string cf.cf_meta Meta.Native with
         | Some name -> name
         | None -> cf.cf_name  (* shouldn't happen given the guard, but safe fallback *)
       in
       (* Determine return type *)
       let ret_tc = match Type.follow cf.cf_type with
         | Type.TFun (_, ret) -> tc_type_of ret
         | _ -> result_tc
       in
       (* Get parameter Haxe types from the function signature *)
       let haxe_param_types = match Type.follow cf.cf_type with
         | Type.TFun (params, _) -> List.map (fun (_, _, t) -> Type.follow t) params
         | _ -> []
       in
       (* Detect callback parameters: any parameter whose Haxe type is TFun *)
       let has_callbacks = List.exists (fun t ->
         match t with Type.TFun _ -> true | _ -> false
       ) haxe_param_types in
       (* Check for @:gcBlocking metadata — implied when callbacks present *)
       let is_gc_blocking = has_callbacks || Meta.has (Meta.Custom ":gcBlocking") cf.cf_meta in
       (* Process arguments, replacing callback closures with trampoline pointers *)
       let callback_setup_stmts = ref [] in
       let processed_args = List.mapi (fun i arg_expr ->
         let haxe_t = if i < List.length haxe_param_types then
           List.nth haxe_param_types i
         else
           Type.TDynamic None  (* shouldn't happen *)
         in
         match haxe_t with
         | Type.TFun (cb_params, cb_ret) ->
           (* This parameter is a callback — generate a trampoline *)
           let cb_param_tcs = List.map (fun (_, _, t) -> tc_type_of (Type.follow t)) cb_params in
           let cb_ret_tc = tc_type_of (Type.follow cb_ret) in
           let trampoline = gen_callback_trampoline native_name i cb_param_tcs cb_ret_tc in
           (* At the call site: create callback context BEFORE entering gc_free zone.
              fib_callback_create must be called from managed code. *)
           let create_stmt = TCSRaw (Printf.sprintf
             "%s = fib_callback_create((FibClosure*)%s);"
             trampoline.cb_global_name
             (* The arg_expr is the closure expression — we need its C representation.
                For now, emit it as a raw expression. The pending_stmts from the arg
                are collected separately. *)
             (match arg_expr.cexpr with
              | TCERaw s -> s
              | TCELocal name -> name
               | _ ->
                 (* For complex expressions, we need to lift them to a temp var.
                    Use a global counter to avoid name collisions when multiple
                    callback registrations happen in the same C function scope. *)
                 let cb_id = !global_cb_arg_counter in
                 global_cb_arg_counter := cb_id + 1;
                 let tmp = Printf.sprintf "_cb_arg_%d" cb_id in
                callback_setup_stmts := !callback_setup_stmts @ [
                  TCSVar { vd_name = tmp; vd_type = TCFibClosure;
                           vd_init = Some arg_expr;
                           vd_const = false; vd_static = false; vd_volatile = false }
                ];
                tmp)
           ) in
           callback_setup_stmts := !callback_setup_stmts @ arg_expr.pending_stmts @ [create_stmt];
           (* Replace the argument with the trampoline function pointer *)
           mk_expr_pos (TCERaw trampoline.cb_trampoline_name)
             (TCRaw (Printf.sprintf "void*")) pos
          | _ ->
            (* For non-callback args, coerce FibString* to const char* for extern C calls.
               C functions expect const char*, not FibString*. We use fib_string_data() to extract. *)
            if arg_expr.ctype = TCFibString then
              mk_expr_pos (TCECall (TCTFunc "fib_string_data", [arg_expr])) (TCConstPointer TCChar) pos
            else
              arg_expr
       ) arg_exprs in
       let args_pending = collect_pending processed_args in
       let extra_pending = !callback_setup_stmts in
       let call_expr = mk_expr_pos (TCECall (TCTFunc native_name, processed_args)) ret_tc pos in
       let call_expr = { call_expr with pending_stmts = args_pending @ call_expr.pending_stmts } in
       if is_gc_blocking then begin
         (* Wrap with GC-free zone enter/exit.
            For non-void returns: lift the call into pending_stmts with a temp var,
            so enter/exit bracket the call properly.
            Callback setup (fib_callback_create) MUST happen before enter_gc_free. *)
         let enter_stmt = TCSRaw "fib_extern_enter_gc_free();" in
         let exit_stmt = TCSRaw "fib_extern_exit_gc_free();" in
         if ret_tc = TCVoid then begin
           (* void return: setup, enter, call, exit — all in pending_stmts *)
           let call_stmt = TCSExpr call_expr in
           let result = mk_expr_pos (TCERaw "((void)0)") TCVoid pos in
           { result with pending_stmts = extra_pending @ call_expr.pending_stmts @ [enter_stmt; call_stmt; exit_stmt] }
         end else begin
           (* non-void: setup, enter, type _r = call, exit *)
           let tmp_name = Printf.sprintf "_ext_%d" (abs (Hashtbl.hash pos)) in
           let decl_stmt = TCSVar {
             vd_name = tmp_name;
             vd_type = ret_tc;
             vd_init = Some call_expr;
             vd_const = false;
             vd_static = false;
             vd_volatile = false;
           } in
           let result = mk_expr_pos (TCERaw tmp_name) ret_tc pos in
           { result with pending_stmts = extra_pending @ call_expr.pending_stmts @ [enter_stmt; decl_stmt; exit_stmt] }
         end
       end else begin
         let call_expr = { call_expr with pending_stmts = extra_pending @ call_expr.pending_stmts } in
         if ret_tc <> result_tc then
           coerce_to_type call_expr result_tc
         else call_expr
       end

   (* Static method call *)
   | TField (_, FStatic (c, cf)) ->
       let class_name = flat_path c.cl_path in
       let method_name = ident cf.cf_name in
       let param_types = get_param_tc_types cf.cf_type in
       let coerced_args = coerce_args ~cf_opt:(Some cf) arg_exprs param_types in
       (* Collect pending_stmts from arguments *)
       let args_pending = collect_pending coerced_args in
       (* For generic functions, the C return type is the erased type (e.g. FibDynamic for T),
          but result_tc is the monomorphized type (e.g. FibString). Unbox if they differ. *)
       let erased_ret_tc = match Type.follow cf.cf_type with
         | Type.TFun (_, ret) -> tc_type_of ret
         | _ -> result_tc
       in
       let call = mk_expr_pos (TCECall (TCTMethod (class_name, method_name), coerced_args)) erased_ret_tc pos in
       let call = { call with pending_stmts = args_pending @ call.pending_stmts } in
       if erased_ret_tc <> result_tc then
         coerce_to_type call result_tc
       else call
  
  (* Array method call - wrap with GC-safe extraction if array is volatile *)
  | TField (arr, FInstance (_, _, cf)) when FiberusBuiltins.is_array_type arr.Type.etype ->
      let arr_expr = convert_expr ctx arr in
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_arr ->
        convert_array_call ctx arr safe_arr args arg_exprs cf.cf_name result_tc pos
      ) arr_expr
  
  (* String method call - wrap with GC-safe extraction if string is volatile *)
  | TField (str, FInstance (_, _, cf)) when FiberusBuiltins.is_string_type str.Type.etype ->
      let str_expr = convert_expr ctx str in
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_str ->
        convert_string_call ctx safe_str args arg_exprs cf.cf_name result_tc pos
      ) str_expr
  
  (* Map method call (IntMap, StringMap, Int64Map, ObjectMap) - wrap with GC-safe extraction.
     Check both the expression type AND the FInstance class, since map literals may have
     abstract Map<K,V> as etype while FInstance resolves to the concrete IntMap/StringMap/etc.
     IMap interface calls fall through to vtable dispatch (handled by hash map vtables). *)
  | TField (map, FInstance (c, _, cf)) when (FiberusBuiltins.map_kind_of_type map.Type.etype <> None
      || FiberusBuiltins.map_kind_of_class c <> None) ->
      let map_expr_raw = convert_expr ctx map in
      let kind = match FiberusBuiltins.map_kind_of_type map.Type.etype with
        | Some k -> k
        | None -> (match FiberusBuiltins.map_kind_of_class c with Some k -> k | None -> FiberusBuiltins.MapInt)
      in
      let expected_tc = match kind with
        | FiberusBuiltins.MapInt -> TCFibIntMap
        | FiberusBuiltins.MapString -> TCFibStringMap
        | FiberusBuiltins.MapInt64 -> TCFibInt64Map
        | FiberusBuiltins.MapObject -> TCFibObjectMap
      in
      (* Coerce to correct map type (e.g. FibDynamic -> FibIntMap* when receiver is Null<Map<Int,T>>) *)
      let map_expr = coerce_to_type map_expr_raw expected_tc in
      let value_type = get_map_value_type map.Type.etype kind in
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_map ->
        convert_map_call ctx safe_map args arg_exprs kind cf.cf_name value_type result_tc pos
      ) map_expr
  
  (* Super method call - super.method(args) must emit a direct static call to the
     parent class's implementation, bypassing vtable dispatch. Without this, the vtable
     resolves to the subclass's override, causing infinite recursion.
     e.g. super.connect(host, port) -> sys_net_Socket_connect((sys_net_Socket)_gc.this, host, port)
     Note: MethDynamic is excluded — dynamic functions are fields, not virtual methods. *)
  | TField (obj, FInstance (c, _, cf))
    when (match cf.cf_kind with Method m when m <> MethDynamic -> true | _ -> false)
      && (match obj.eexpr with TConst TSuper -> true | _ -> false) ->
      let obj_expr = convert_expr ctx obj in
      let parent_name = flat_path c.cl_path in
      let method_name = ident cf.cf_name in
      let param_types = get_param_tc_types cf.cf_type in
      let coerced_args = coerce_args ~cf_opt:(Some cf) arg_exprs param_types in
      let args_pending = collect_pending coerced_args in
      (* Cast this to parent type for the direct call *)
      let parent_this = mk_expr (TCECast (TCFibClass parent_name, obj_expr)) (TCFibClass parent_name) in
      let call = mk_expr_pos (TCECall (TCTMethod (parent_name, method_name), parent_this :: coerced_args)) result_tc pos in
      { call with pending_stmts = args_pending @ call.pending_stmts }

  (* Dynamic method call - MethDynamic fields are stored as void* holding FibClosure*.
     Must use TCEDynamicCall (not TCEClosureCall) because the closure may be reassigned
     to any function with a compatible signature, whose ->fn has different typed params.
     fn_dynamic takes all args as FibDynamic and handles unboxing inside the thunk. *)
  | TField (obj, FInstance (c, _, cf)) when (match cf.cf_kind with Method MethDynamic -> true | _ -> false) ->
      let obj_expr = convert_expr ctx obj in
      let args_pending = collect_pending arg_exprs in
      let boxed_args = box_args_for_dynamic_call arg_exprs in
      let call_result =
        if FiberusVtable.is_interface c then begin
          (* Interface dynamic method: struct layout differs per concrete class, so we
             cannot use direct ->field access. Read via fib_field_get (dynamic dispatch)
             which looks up by name through the actual object's field descriptor. *)
          let field_name_str = mk_raw_string cf.cf_name in
          wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
            let dyn_obj = coerce_to_type safe_obj TCFibDynamic in
            let closure_as_dyn = mk_expr_inherit
              (TCECall (TCTFunc "fib_field_get", [dyn_obj; field_name_str]))
              TCFibDynamic [dyn_obj] in
            let dyn_call = mk_expr_pos (TCEDynamicCall { closure = closure_as_dyn; args = boxed_args }) TCFibDynamic pos in
            unwrap_dynamic_result dyn_call result_tc
          ) obj_expr
        end else begin
          let class_name = flat_path c.cl_path in
          let field_name = ident cf.cf_name in
          wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
            (* Cast object to declaring class type if needed *)
            let this_type = TCFibClass class_name in
            let cast_obj = if safe_obj.ctype <> this_type then
              mk_expr (TCECast (this_type, safe_obj)) this_type
            else safe_obj in
            (* Read the void* field, cast to FibObject, box as FibDynamic for _fib_dyn_call_N *)
            let field_access = mk_expr (TCEArrow (cast_obj, field_name)) (TCPointer TCVoid) in
            let closure_as_dyn = mk_expr (TCECall (TCTFunc "fib_dynamic_object", [
              mk_expr (TCECast (TCFibObject, field_access)) TCFibObject
            ])) TCFibDynamic in
            let dyn_call = mk_expr_pos (TCEDynamicCall { closure = closure_as_dyn; args = boxed_args }) TCFibDynamic pos in
            unwrap_dynamic_result dyn_call result_tc
          ) obj_expr
        end
      in
      { call_result with pending_stmts = args_pending @ call_result.pending_stmts }

  (* Instance method call - only match actual methods, not function-typed Var fields.
     Var fields with function types (e.g. var replacer:(Dynamic,Dynamic)->Dynamic) must
     fall through to the closure call handler below.
     Note: MethDynamic is excluded — handled above as closure field calls. *)
  | TField (obj, FInstance (c, _, cf)) when (match cf.cf_kind with Method m when m <> MethDynamic -> true | _ -> false) ->
      let obj_expr = convert_expr ctx obj in
      let class_name = flat_path c.cl_path in
      let method_name = ident cf.cf_name in
      let param_types = get_param_tc_types cf.cf_type in
      let is_interface_call = FiberusVtable.is_interface c in
      let has_missing_optional =
        (* Extern classes have no fn_dynamic thunk; defaults must be filled at call site
           by the Haxe compiler, so never use dynamic dispatch for them. *)
        if has_class_flag c CExtern then false
        else
        match Type.follow cf.cf_type with
        | Type.TFun (params, _) ->
            let arg_count = List.length arg_exprs in
            let param_count = List.length params in
            let is_null_arg e = match e.cexpr with
              | TCENull -> true
              | TCECall (TCTFunc "fib_dynamic_null", []) -> true
              | _ -> false
            in
            let rec all_optional idx =
              if idx >= param_count then true
              else
                let (_, opt, _) = List.nth params idx in
                opt && all_optional (idx + 1)
            in
            let rec any_missing idx =
              if idx >= param_count then false
              else if idx >= arg_count then all_optional idx
              else
                let (_, opt, _) = List.nth params idx in
                if opt && is_null_arg (List.nth arg_exprs idx) then true
                else any_missing (idx + 1)
            in
            any_missing 0
        | _ -> false
      in
      let coerced_args = coerce_args ~cf_opt:(Some cf) arg_exprs param_types in
      (* Collect pending_stmts from arguments - these must be emitted before the call *)
      let args_pending = if has_missing_optional then collect_pending arg_exprs else collect_pending coerced_args in
      
      (* Wrap the method call generation with GC-safe extraction of the object.
       * This ensures that if the object came from an array element access or
       * method call, it's rooted before we evaluate arguments or call the method. *)
      let call_result = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Cast this pointer to declaring class type if it differs from the object's
         * actual type. This avoids -Wincompatible-pointer-types when calling a parent
         * class method on a subclass instance, e.g. haxe_Exception_toString called
         * on a PosException pointer.
         * If the object is FibDynamic (e.g. generic class with unresolved type params),
         * first unbox to FibObject then cast. *)
        let this_type = TCFibClass class_name in
        (* If the object is FibDynamic (e.g. generic class with unresolved type params),
           unbox to a pointer type first. The vtable call emitter casts obj to FibObject
           pointer, which does not work on FibDynamic structs. *)
        let safe_obj =
          if safe_obj.ctype = TCFibDynamic then
            mk_expr (TCECall (TCTFunc "fib_dynamic_to_object", [safe_obj])) TCFibObject
          else safe_obj in
        let cast_obj = if safe_obj.ctype <> this_type then
          mk_expr (TCECast (this_type, safe_obj)) this_type
        else safe_obj in
        (* If optional args are omitted, use dynamic field lookup and fn_dynamic so
           defaults are applied by the actual method implementation at runtime. *)
        if has_missing_optional then begin
          let field_name = mk_raw_string cf.cf_name in
          let boxed_args = box_args_for_dynamic_call arg_exprs in
          let dyn_obj = coerce_to_type safe_obj TCFibDynamic in
          let closure_as_dyn = mk_expr_inherit (TCECall (TCTFunc "fib_field_get", [dyn_obj; field_name])) TCFibDynamic [dyn_obj] in
          let dyn_call = mk_expr_pos (TCEDynamicCall { closure = closure_as_dyn; args = boxed_args }) TCFibDynamic pos in
          unwrap_dynamic_result dyn_call result_tc
        end else
        (* Check if this needs vtable dispatch *)
        (* For generic classes like Tls<T>, the function definition uses the erased
           type (FibDynamic) for type parameters, but the call site has the monomorphized
           type (e.g. FibString for Tls<String>). The vtable function pointer cast must
           use the erased types matching the actual function signature, then we unbox
           the result to the caller's expected type if they differ. *)
        let erased_ret_tc = match Type.follow cf.cf_type with
          | Type.TFun (_, ret) -> tc_type_of ret
          | _ -> result_tc
        in
        (* Compute erased types for the function pointer cast in vtable calls.
           The cast must match the C function's actual compiled signature, which uses
           the defining class's erased types (type params -> Dynamic, Array<T> -> FibArray, etc.),
           not the monomorphized call-site types (Array<Int> -> FibIntArray). *)
        let defining_cf_opt =
          let defining_class = FiberusVtable.find_defining_class c cf.cf_name in
          List.find_opt (fun f -> f.cf_name = cf.cf_name) defining_class.cl_ordered_fields
        in
        let erased_arg_tc_types = match defining_cf_opt with
          | Some def_cf -> get_param_tc_types def_cf.cf_type
          | None -> List.map (fun arg -> arg.ctype) coerced_args
        in
        let erased_ret_tc = match defining_cf_opt with
          | Some def_cf ->
            (match Type.follow def_cf.cf_type with
             | Type.TFun (_, ret) -> tc_type_of ret
             | _ -> erased_ret_tc)
           | None -> erased_ret_tc
        in
        (* Re-coerce vtable call arguments to erased types.
           The coerced_args were built from the call-site's monomorphized types
           (e.g. FibIntArray* for Array<Int>), but the vtable function pointer
           expects the defining class's erased types (e.g. FibArray* for Array<T>).
           We need to cast each arg to its erased type. *)
        let vtable_args =
          let rec coerce_pairs args erased = match args, erased with
            | [], _ | _, [] -> args
            | a :: ra, et :: re -> coerce_to_type a et :: coerce_pairs ra re
          in
          coerce_pairs coerced_args erased_arg_tc_types
        in
        match ctx.vtable_ctx with
        | Some vtctx ->
            if is_interface_call then begin
              (* Interface calls ALWAYS need vtable dispatch *)
              match FiberusVtable.get_interface_slot vtctx c cf with
              | Some slot ->
                  (* Interface calls use FibObject as this type since we don't know concrete class *)
                   let vtcall = mk_expr_pos (TCEVtableCall {
                    obj = safe_obj;
                    slot = slot;
                    this_type = TCFibObject;
                    ret_type = erased_ret_tc;
                    cast_arg_types = erased_arg_tc_types;
                    args = vtable_args;
                    is_interface = true;
                  }) erased_ret_tc pos in
                  if erased_ret_tc <> result_tc then
                    coerce_to_type vtcall result_tc
                  else vtcall
              | None ->
                  mk_expr_pos (TCERaw (Printf.sprintf "/* ERROR: Interface method %s has no vtable slot */" cf.cf_name)) result_tc pos
            end else begin
              match FiberusVtable.get_vtable_slot vtctx c cf with
              | Some slot_info ->
                  (* Virtual dispatch through vtable *)
                  let vtcall = mk_expr_pos (TCEVtableCall {
                    obj = safe_obj;
                    slot = slot_info.FiberusVtable.slot_index;
                    this_type = TCFibClass class_name;
                    ret_type = erased_ret_tc;
                    cast_arg_types = erased_arg_tc_types;
                    args = vtable_args;
                    is_interface = false;
                  }) erased_ret_tc pos in
                  if erased_ret_tc <> result_tc then
                    coerce_to_type vtcall result_tc
                  else vtcall
              | None ->
                  (* Direct call - use cast_obj for correct pointer type *)
                  let call = mk_expr_pos (TCECall (TCTMethod (class_name, method_name), cast_obj :: coerced_args)) erased_ret_tc pos in
                  if erased_ret_tc <> result_tc then
                    coerce_to_type call result_tc
                  else call
            end
        | None ->
            (* No vtable context - direct call, use cast_obj for correct pointer type *)
            let call = mk_expr_pos (TCECall (TCTMethod (class_name, method_name), cast_obj :: coerced_args)) erased_ret_tc pos in
            if erased_ret_tc <> result_tc then
              coerce_to_type call result_tc
            else call
      ) obj_expr in
      (* Prepend arguments' pending_stmts to ensure temp vars are declared before call *)
      { call_result with pending_stmts = args_pending @ call_result.pending_stmts }
  
  (* Constructor call - TNew handles this, but might appear as call too *)
  | TField (_, FEnum (e, ef)) ->
      let enum_name = flat_path e.e_path in
      let constr_name = ident ef.ef_name in
      (* Collect pending_stmts from arguments *)
      let args_pending = collect_pending arg_exprs in
      (* Coerce arguments to match enum constructor parameter types.
         E.g. Custom(e:Dynamic) needs String->FibDynamic boxing. *)
      let param_types = match Type.follow ef.ef_type with
        | TFun (params, _) -> List.map (fun (_, _, t) -> tc_type_of t) params
        | _ -> []
      in
      let rec coerce_enum_args aexprs ptypes = match aexprs, ptypes with
        | [], _ | _, [] -> aexprs
        | a :: rest_a, pt :: rest_pt ->
            coerce_to_type a pt :: coerce_enum_args rest_a rest_pt
      in
      let coerced_args = coerce_enum_args arg_exprs param_types in
      let call = mk_expr_pos (TCEEnumConstruct (enum_name, constr_name, coerced_args)) (TCFibEnum enum_name) pos in
      { call with pending_stmts = args_pending @ call.pending_stmts }
  
  (* Dynamic/anonymous field call - wrap with GC-safe extraction *)
  | TField (obj, FAnon cf) ->
      let obj_expr = convert_expr ctx obj in
      (* Intercept map iterator hasNext()/next() calls: when the receiver's C type
         is a map iterator (TCRaw "FibXxxMapYyyIterator*"), route to the correct
         static C function instead of dynamic dispatch. *)
      let map_iter_info = match obj_expr.ctype with
        | TCRaw "FibIntMapKeyIterator*" -> Some ("fib_int_map_key_iterator_", TCInt32)
        | TCRaw "FibIntMapValueIterator*" -> Some ("fib_int_map_value_iterator_", TCFibDynamic)
        | TCRaw "FibStringMapKeyIterator*" -> Some ("fib_string_map_key_iterator_", TCFibString)
        | TCRaw "FibStringMapValueIterator*" -> Some ("fib_string_map_value_iterator_", TCFibDynamic)
        | TCRaw "FibInt64MapKeyIterator*" -> Some ("fib_int64_map_key_iterator_", TCInt64)
        | TCRaw "FibInt64MapValueIterator*" -> Some ("fib_int64_map_value_iterator_", TCFibDynamic)
        | TCRaw "FibObjectMapKeyIterator*" -> Some ("fib_object_map_key_iterator_", TCFibObject)
        | TCRaw "FibObjectMapValueIterator*" -> Some ("fib_object_map_value_iterator_", TCFibDynamic)
        | _ -> None
      in
      (match map_iter_info, cf.cf_name with
      | Some (func_prefix, _), "hasNext" ->
          mk_expr_pos (TCECall (TCTFunc (func_prefix ^ "has_next"), [obj_expr])) TCBool pos
      | Some (func_prefix, next_type), "next" ->
          mk_expr_pos (TCECall (TCTFunc (func_prefix ^ "next"), [obj_expr])) next_type pos
      | _ ->
      let field_name = mk_raw_string cf.cf_name in
      (* Collect pending_stmts from arguments *)
      let args_pending = collect_pending arg_exprs in
      let boxed_args = box_args_for_dynamic_call arg_exprs in
      let call_result = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Box object to FibDynamic if needed (e.g. FibArray* -> FibDynamic for dynamic dispatch) *)
        let dyn_obj = coerce_to_type safe_obj TCFibDynamic in
        (* Get closure from dynamic field, then call it *)
        let closure = mk_expr_inherit (TCECall (TCTFunc "fib_dynamic_get_field", [dyn_obj; field_name])) TCFibClosure [dyn_obj] in
        let dyn_call = mk_expr_pos (TCEDynamicCall { closure; args = boxed_args }) TCFibDynamic pos in
        unwrap_dynamic_result dyn_call result_tc
      ) obj_expr in
      { call_result with pending_stmts = args_pending @ call_result.pending_stmts })
  
  | TField (obj, FDynamic name) ->
      let obj_expr = convert_expr ctx obj in
      let field_name = mk_raw_string name in
      (* Collect pending_stmts from arguments *)
      let args_pending = collect_pending arg_exprs in
      let boxed_args = box_args_for_dynamic_call arg_exprs in
      let call_result = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Box object to FibDynamic if needed *)
        let dyn_obj = coerce_to_type safe_obj TCFibDynamic in
        let closure = mk_expr_inherit (TCECall (TCTFunc "fib_dynamic_get_field", [dyn_obj; field_name])) TCFibClosure [dyn_obj] in
        let dyn_call = mk_expr_pos (TCEDynamicCall { closure; args = boxed_args }) TCFibDynamic pos in
        unwrap_dynamic_result dyn_call result_tc
      ) obj_expr in
      { call_result with pending_stmts = args_pending @ call_result.pending_stmts }
  
  (* Super constructor call: super(args) -> ParentClass_init(this, args) *)
  | TConst TSuper ->
      (match ctx.current_class with
      | Some c ->
          (match c.cl_super with
          | Some (parent_c, _) ->
              let parent_name = flat_path parent_c.cl_path in
              (* Get parent constructor parameter types and defaults *)
              let parent_ctor = parent_c.cl_constructor in
              let param_types = match parent_ctor with
                | Some cf -> get_param_tc_types cf.cf_type
                | None -> []
              in
              let coerced_args = coerce_args ~cf_opt:parent_ctor arg_exprs param_types in
              (* Collect pending_stmts from arguments *)
              let args_pending = collect_pending coerced_args in
              (* Cast this to parent type - TCFibClass already represents ClassName* *)
              let parent_this = mk_expr (TCECast (TCFibClass parent_name, mk_expr TCEThis (TCPointer TCVoid))) (TCFibClass parent_name) in
              let call = mk_expr_pos (TCECall (TCTMethod (parent_name, "init"), parent_this :: coerced_args)) TCVoid pos in
              { call with pending_stmts = args_pending @ call.pending_stmts }
          | None ->
              mk_expr_pos (TCERaw "/* super() with no parent class */") TCVoid pos)
      | None ->
          mk_expr_pos (TCERaw "/* super() outside of class context */") TCVoid pos)
  
  (* Closure call - callee is already a closure value *)
  | _ ->
      let callee_expr = convert_expr ctx callee in
      (* Collect pending_stmts from arguments *)
      let args_pending = collect_pending arg_exprs in
      let call = (match callee_expr.ctype with
      | TCFibClosure ->
          (* Check if closure param types come from type parameter erasure.
             When a generic class like Dispatcher<T> calls a closure l(e) where l: T->Void,
             the type parameter T is erased to FibDynamic at the C level. But the closure's
             ->fn is the typed implementation (e.g., (FibClosure, ConcreteType) -> void).
             We must use dynamic dispatch (fn_dynamic) in this case, not the typed ->fn. *)
          (* Check if closure param types could cause ABI mismatch.
             A closure variable's actual typed thunk may have been compiled with
             FibDynamic params (when the lambda used structural/anonymous typing),
             while the call site casts to concrete class pointer types.
             Must use dynamic dispatch (fn_dynamic) when:
             1. Any param is a type parameter (generic erasure)
             2. Any param is a class/interface pointer type - the actual closure
                may have FibDynamic there if the lambda was structurally typed *)
           let needs_dynamic_dispatch =
            match Type.follow callee.etype with
            | Type.TFun (params, ret) ->
              (* In this fallback path, the callee is a local closure variable (not a
                 known static/instance method). The variable could hold a closure that
                 passed through Dynamic, in which case its actual typed thunk may have
                 different numeric primitive types than what the call site expects.
                 For example: var f: Int->Float = make(foo) where foo: Float->Float.
                 The typed thunk expects double in XMM0 but we would pass int32 in EDI.
                 To prevent ABI mismatch, force dynamic dispatch whenever any param or
                 the return type is a numeric primitive -- fn_dynamic boxes/unboxes
                 correctly regardless of the actual thunk's primitive types. *)
              let is_numeric_primitive t = match tc_type_of t with
                | TCInt32 | TCInt64 | TCFloat64 | TCFloat32 | TCBool
                | TCInt8 | TCInt16 | TCUInt8 | TCUInt16 | TCUInt32 | TCUInt64
                | TCChar | TCSizeT -> true
                | _ -> false
              in
              let has_numeric_param = List.exists (fun (_, _, t) -> is_numeric_primitive t) params in
              let has_numeric_ret = is_numeric_primitive ret in
              if has_numeric_param || has_numeric_ret then true
              else
              List.exists (fun (_, opt, t) ->
                (* Optional primitive params are passed as FibDynamic (to represent null)
                   but the closure impl takes the concrete type. Must use dynamic dispatch. *)
                if opt then
                  (match tc_type_of t with
                   | TCInt32 | TCInt64 | TCFloat64 | TCFloat32 | TCBool
                   | TCInt8 | TCInt16 | TCUInt8 | TCUInt16 | TCUInt32 | TCUInt64
                   | TCChar | TCSizeT -> true
                   | _ -> false)
                else
                match Type.follow t with
                | Type.TInst ({ cl_kind = KTypeParameter _ }, _) -> true
                | Type.TAnon _ -> true
                | Type.TInst _ | Type.TAbstract _ ->
                  (* Class/abstract param: the closure might have FibDynamic instead.
                     Only use dynamic dispatch if the param maps to a pointer type,
                     since primitive types (Int, Float, Bool) have the same ABI. *)
                  (match tc_type_of t with
                   | TCFibClass _ | TCFibObject | TCFibClosure | TCPointer _
                   | TCFibString | TCFibArray _ -> true
                   (* Null<primitive> maps to FibDynamic but the closure impl takes
                      the concrete primitive type. Must use dynamic dispatch to go
                      through the wrapper which unboxes FibDynamic args properly. *)
                   | TCFibDynamic -> true
                   | _ -> false)
                | _ -> false
              ) params
            | _ -> false
          in
          if needs_dynamic_dispatch then begin
            let boxed_closure = mk_expr (TCEBox (callee_expr, TCBoxClosure)) TCFibDynamic in
            let boxed_args = box_args_for_dynamic_call arg_exprs in
            let dyn_call = mk_expr_pos (TCEDynamicCall { closure = boxed_closure; args = boxed_args }) TCFibDynamic pos in
            unwrap_dynamic_result dyn_call result_tc
          end else begin
            (* Safe to use typed call: all params are primitives or FibDynamic,
               so the ABI matches regardless of the closure's actual compilation. *)
            let formal_param_types = get_closure_param_tc_types callee.etype in
            let coerced_args = coerce_args arg_exprs formal_param_types in
            let arg_types = if formal_param_types <> [] then formal_param_types
                            else List.map (fun e -> e.ctype) coerced_args in
            mk_expr_pos (TCEClosureCall {
              closure = callee_expr;
              arg_types = arg_types;
              ret_type = result_tc;
              args = coerced_args;
            }) result_tc pos
          end
      | _ ->
          (* Unknown callable - use dynamic call, boxing args to FibDynamic *)
          let boxed_args = box_args_for_dynamic_call arg_exprs in
          let dyn_call = mk_expr_pos (TCEDynamicCall { closure = callee_expr; args = boxed_args }) TCFibDynamic pos in
          unwrap_dynamic_result dyn_call result_tc) in
      { call with pending_stmts = callee_expr.pending_stmts @ args_pending @ call.pending_stmts }

(* ============================================================================
 * TVar Conversion (shared between convert_stmt and convert_expr_as_stmt)
 * ============================================================================
 * 
 * Handles three paths:
 * 1. Stack allocation: struct on stack + pointer alias + init call + per-field GC pushes
 * 2. Normal with init: pending_stmts + var decl + pop init gc_roots + push var root  
 * 3. Normal without init: var decl + push var root
 *
 * GC root ordering is critical for the init case:
 * - The initializer may leave gc_roots on the temp root stack (from GC-safe extraction)
 * - We must POP those BEFORE pushing the variable itself, because temp roots are LIFO
 * - If we push first then pop, we'd pop the variable we just pushed!
 * - The object is briefly unprotected between pop and push, but gc_push doesn't allocate
 *   so no GC can trigger in between.
 *)

and convert_tvar_stmt (ctx : conv_ctx) (v : tvar) (init_opt : texpr option) : tc_stmt list =
  let name = ident v.v_name in
  let vtype_raw = tc_type_of v.v_type in
  (* When the Haxe type is TAnon (e.g. Iterator<T> typedef) but the init expression
     is a map keys()/iterator() call, use the concrete C iterator type instead of FibDynamic.
     Iterator<T> resolves to TAnon { hasNext, next } -> TCFibDynamic, but the actual C type
     is e.g. FibIntMapKeyIterator*. Without this, the variable is FibDynamic and
     hasNext()/next() go through broken dynamic dispatch. *)
  let vtype = match vtype_raw, init_opt with
    | TCFibDynamic, Some init_e ->
        let map_iter_type_of call_expr map_obj =
          let method_name = match call_expr with
            | { Type.eexpr = TField (_, FInstance (_, _, cf)) } -> cf.cf_name
            | { Type.eexpr = TField (_, FAnon cf) } -> cf.cf_name
            | _ -> ""
          in
          let map_kind = FiberusBuiltins.map_kind_of_type (Type.follow map_obj.Type.etype) in
          match map_kind, method_name with
          | Some FiberusBuiltins.MapInt, "keys" -> Some (TCRaw "FibIntMapKeyIterator*")
          | Some FiberusBuiltins.MapInt, "iterator" -> Some (TCRaw "FibIntMapValueIterator*")
          | Some FiberusBuiltins.MapString, "keys" -> Some (TCRaw "FibStringMapKeyIterator*")
          | Some FiberusBuiltins.MapString, "iterator" -> Some (TCRaw "FibStringMapValueIterator*")
          | Some FiberusBuiltins.MapInt64, "keys" -> Some (TCRaw "FibInt64MapKeyIterator*")
          | Some FiberusBuiltins.MapInt64, "iterator" -> Some (TCRaw "FibInt64MapValueIterator*")
          | Some FiberusBuiltins.MapObject, "keys" -> Some (TCRaw "FibObjectMapKeyIterator*")
          | Some FiberusBuiltins.MapObject, "iterator" -> Some (TCRaw "FibObjectMapValueIterator*")
          | _ -> None
        in
        (match init_e.eexpr with
        | TCall (({ eexpr = TField (map_obj, _) } as call_e), _) ->
            (match map_iter_type_of call_e map_obj with
            | Some iter_type ->
                (* Register the override so TLocal references use the correct type *)
                Hashtbl.replace ctx.var_type_overrides v.v_id iter_type;
                iter_type
            | None -> vtype_raw)
        | _ -> vtype_raw)
    | _ -> vtype_raw
  in
  let is_fiber_mature = Hashtbl.mem ctx.fiber_mature_vars v.v_id in
  let is_stack_alloc = Hashtbl.mem ctx.stack_alloc_vars v.v_id in
  let stmts =
    if is_stack_alloc then begin
      (* Stack allocation path: declare struct on stack, pointer alias, init call, per-field GC pushes *)
      let c = Hashtbl.find ctx.stack_alloc_vars v.v_id in
      let class_name = flat_path c.cl_path in
      (* 1. Declare the struct on the stack with class pointer *)
      let struct_decl = TCSRaw (Printf.sprintf "%s _stack_%s = { ._obj.clazz = &%s_class };" class_name name class_name) in
      (* 2. Declare the pointer variable pointing to the stack struct *)
      let ptr_decl = TCSVar { vd_name = name; vd_type = TCFibClass class_name;
                              vd_init = Some (mk_expr (TCERaw (Printf.sprintf "&_stack_%s" name)) (TCFibClass class_name));
                              vd_static = false; vd_const = false; vd_volatile = false } in
      (* 3. Build init call with constructor arguments *)
      let init_args, args_pending = match init_opt with
        | Some { eexpr = TNew (tc, _, args) } when List.length args > 0 ->
            let arg_exprs = List.map (convert_expr ctx) args in
            (* Collect pending stmts from args *)
            let pending = collect_pending arg_exprs in
            (* Coerce arguments to parameter types, substituting defaults for null args *)
            let param_types = match tc.cl_constructor with
              | Some cf -> get_param_types cf.cf_type
              | None -> []
            in
            let defaults = match tc.cl_constructor with
              | Some cf -> begin match cf.cf_expr with
                  | Some { eexpr = TFunction f } ->
                      List.map (fun (_, default_opt) -> default_opt) f.tf_args
                  | _ -> []
                end
              | None -> []
            in
            let is_null_tc_expr e =
              match e.cexpr with
              | TCENull -> true
              | TCECall (TCTFunc "fib_dynamic_null", []) -> true
              | TCECall (TCTFunc "fib_dynamic_to_int", [{ cexpr = TCECall (TCTFunc "fib_dynamic_null", []) }]) -> true
              | TCECall (TCTFunc "fib_dynamic_to_float", [{ cexpr = TCECall (TCTFunc "fib_dynamic_null", []) }]) -> true
              | TCECall (TCTFunc "fib_dynamic_to_bool", [{ cexpr = TCECall (TCTFunc "fib_dynamic_null", []) }]) -> true
              | _ -> false
            in
            let apply_default a target_tc default_opt =
              if is_null_tc_expr a && target_tc <> TCFibDynamic then
                match default_opt with
                | Some { eexpr = TConst c } -> begin match c with
                    | TInt i -> Some (mk_int i)
                    | TFloat s -> Some (mk_expr (TCEFloat s) target_tc)
                    | TBool b -> Some (mk_expr (TCEBool b) TCBool)
                    | TString s -> Some (mk_expr (TCEString s) TCFibString)
                    | _ -> None
                  end
                | _ -> None
              else None
            in
            let rec coerce_args aexprs ptypes defs = match aexprs, ptypes, defs with
              | [], _, _ -> []
              | a :: rest_a, pt :: rest_pt, d :: rest_d ->
                  let target_tc = tc_type_of pt in
                  let coerced = match apply_default { a with pending_stmts = [] } target_tc d with
                    | Some default_val -> default_val
                    | None -> coerce_to_type { a with pending_stmts = [] } target_tc
                  in
                  coerced :: coerce_args rest_a rest_pt rest_d
              | a :: rest_a, pt :: rest_pt, [] ->
                  coerce_to_type { a with pending_stmts = [] } (tc_type_of pt) :: coerce_args rest_a rest_pt []
              | a :: rest_a, [], _ ->
                  { a with pending_stmts = [] } :: coerce_args rest_a [] []
            in
            (coerce_args arg_exprs param_types defaults, pending)
        | _ -> ([], [])
      in
      let this_arg = mk_expr (TCELocal name) (TCFibClass class_name) in
      let init_call = TCSExpr (mk_expr (TCECall (TCTFunc (class_name ^ "_init"), this_arg :: init_args)) TCVoid) in
      (* 4. Push temp roots for each GC-pointer field of the stack-allocated object.
       * This enables eliminating conservative stack scanning in minor GC, since all
       * GC pointers are now precisely tracked via temp roots.
       * Note: TCSGCPush adds & automatically, so we pass the field lvalue directly. *)
      let field_gc_pushes = List.filter_map (fun (cf : tclass_field) ->
        match cf.cf_kind with
        | Var _ when haxe_type_needs_gc_root cf.cf_type ->
            ctx.gc_local_count <- ctx.gc_local_count + 1;
            let field_tc = tc_type_of cf.cf_type in
            Some (TCSGCPush (mk_expr (TCEArrow (mk_expr (TCELocal name) (TCFibClass class_name), ident cf.cf_name)) field_tc))
        | _ -> None
      ) c.cl_ordered_fields in
      args_pending @ [struct_decl; ptr_decl; init_call] @ field_gc_pushes
    end else begin
      (* Normal heap allocation path *)
      match init_opt with
      | None ->
          if needs_gc_root_tc vtype && ctx.in_gc_frame then begin
            (* GCFrame mode, no initializer: just register the slot in the
               frame struct.  The frame declaration already initializes it to
               NULL/{0}, so we need neither a local variable nor an assignment.
               Emitting the bare local would trigger -Wunused-variable, and
               assigning it to _gc would trigger -Wuninitialized. *)
            gc_frame_add_slot ctx name vtype;
            []
          end else begin
            (* Non-GC type or legacy mode: emit the local variable declaration *)
            let var_stmt = TCSVar { vd_name = name; vd_type = vtype; vd_init = None; vd_static = false; vd_const = false; vd_volatile = false } in
            if needs_gc_root_tc vtype then begin
              ctx.gc_local_count <- ctx.gc_local_count + 1;
              var_stmt :: [TCSGCPush (mk_expr (TCELocal name) vtype)]
            end else
              [var_stmt]
          end
      | Some init_e ->
          (* Convert the initializer expression *)
          let cexpr = convert_expr ctx init_e in
          (* Anonymous objects stored in variables must be heap-allocated,
             since stack-allocated compound literals are only valid in the
             enclosing expression statement. *)
          let cexpr = mark_anon_heap_alloc cexpr in
          (* Coerce to variable type if needed *)
          let coerced = coerce_to_type cexpr vtype in
          (* When coerce_to_type downgrades a specialized array to generic (because the
             value came from Dynamic), use the coerced type as the variable type.
             This prevents declaring e.g. FibIntArray* for a variable that actually holds
             a FibArray* at runtime.  Also register a type override so subsequent TLocal
             references use the correct type. *)
          let vtype = match vtype, coerced.ctype with
            | TCFibArray k1, TCFibArray k2 when k1 <> k2 ->
                Hashtbl.replace ctx.var_type_overrides v.v_id coerced.ctype;
                coerced.ctype
            | _ -> vtype
          in
          (* Extract pending statements - they must be emitted BEFORE the var decl *)
          let pending = coerced.pending_stmts in
          let init_gc_roots = coerced.gc_roots in
          let clean_init = { coerced with pending_stmts = []; gc_roots = 0 } in
          let var_stmt = TCSVar { vd_name = name; vd_type = vtype; vd_init = Some clean_init; vd_static = false; vd_const = false; vd_volatile = false } in
          (* GC root ordering: pop init roots BEFORE pushing variable root.
           * This is critical because temp roots are a LIFO stack. *)
          let is_gc_ptr = needs_gc_root_tc vtype in
          let gc_stmts =
            if is_gc_ptr then begin
              let pop_stmts = if init_gc_roots > 0 then begin
                ctx.gc_local_count <- ctx.gc_local_count - init_gc_roots;
                [TCSGCPop init_gc_roots]
              end else [] in
              let push_stmts = gc_push_if_needed ctx name vtype in
              pop_stmts @ push_stmts
            end else if init_gc_roots > 0 then begin
              (* Non-GC pointer type but init had gc_roots - still need to pop *)
              ctx.gc_local_count <- ctx.gc_local_count - init_gc_roots;
              [TCSGCPop init_gc_roots]
            end else
              []
          in
          pending @ [var_stmt] @ gc_stmts
    end
  in
  (* Wrap with gc_force_mature if this variable is fiber-captured.
   * We emit begin/end at the same scope level (not in a block) so the
   * variable remains visible in the enclosing scope. *)
  if is_fiber_mature then
    [TCSRaw "gc_force_mature_begin();"] @ stmts @ [TCSRaw "gc_force_mature_end();"]
  else
    stmts

(* ============================================================================
 * Statement Conversion
 * ============================================================================ *)

(* Emit TCSLine if source line changed since last emission (dedup like hxcpp HXLINE).
   Only active at debug_level >= 2 and when function has a stack frame (FIBLINE
   references _fib_stackframe which is only declared by FIB_STACKFRAME). *)
and maybe_emit_line ctx (e : texpr) : tc_stmt list =
  if ctx.debug_level < 2 || not ctx.has_stack_frame then []
  else
    let line = Lexer.get_error_line e.epos in
    if line <> ctx.last_line && line > 0 then begin
      ctx.last_line <- line;
      [TCSLine line]
    end else
      []

and convert_stmt (ctx : conv_ctx) (e : texpr) : tc_stmt list =
  let line_stmts = match e.eexpr with
    | TBlock _ -> []
    | _ -> maybe_emit_line ctx e
  in
  let stmts = match e.eexpr with
  (* Variable declaration *)
  | TVar (v, init_opt) ->
      convert_tvar_stmt ctx v init_opt
  
  (* Block of statements - flatten into parent scope to preserve variable lifetimes.
   * We don't wrap in TCSBlock here because that creates C { } scopes which end
   * variable lifetimes while GC roots still reference them. The caller (TWhile body,
   * TIf branch, etc.) wraps in TCSBlock if scoping is needed. *)
  | TBlock exprs ->
      let stmts = List.concat_map (convert_stmt ctx) exprs in
      mark_volatile_for_try stmts
  
  (* If statement - save/restore GC roots around each branch to prevent
   * roots from branch-scoped variables leaking into the enclosing scope.
   * Skip pop if branch ends with return (return handles its own GC cleanup).
   * In GCFrame mode, gc_local_count only tracks stack-alloc field temp roots
   * (regular locals use frame slots), so pops are only emitted when needed. *)
  | TIf (cond, ethen, eelse_opt) ->
      let cond_expr = convert_expr ctx cond in
      (* Coerce FibDynamic condition to bool *)
      let cond_expr =
        if cond_expr.ctype = TCFibDynamic then
          mk_expr_inherit (TCECall (TCTFunc "fib_dynamic_to_bool", [cond_expr])) TCBool [cond_expr]
        else cond_expr
      in
      let saved_gc1 = gc_save_count ctx in
      let then_stmts = convert_stmt ctx ethen in
      let to_pop1 = gc_roots_to_pop ctx saved_gc1 in
      let then_with_pop = if to_pop1 > 0 && not (ends_with_return ethen) then begin
        ctx.gc_local_count <- saved_gc1;
        then_stmts @ [TCSGCPop to_pop1]
      end else begin
        ctx.gc_local_count <- saved_gc1;
        then_stmts
      end in
      let else_with_pop = match eelse_opt with
        | None -> None
        | Some eelse ->
            let saved_gc2 = gc_save_count ctx in
            let else_stmts = convert_stmt ctx eelse in
            let to_pop2 = gc_roots_to_pop ctx saved_gc2 in
            if to_pop2 > 0 && not (ends_with_return eelse) then begin
              ctx.gc_local_count <- saved_gc2;
              Some (else_stmts @ [TCSGCPop to_pop2])
            end else begin
              ctx.gc_local_count <- saved_gc2;
              Some else_stmts
            end
      in
      [TCSIf (cond_expr, then_with_pop, else_with_pop)]
  
  (* While loop - save/restore GC roots around loop body to prevent
   * unbounded temp root accumulation from loop-scoped GC pointer variables.
   * Also inject yield point for outer loops (depth <= 1) to allow fiber scheduling.
   * In GCFrame mode, gc_local_count only tracks stack-alloc field temp roots. *)
  | TWhile (cond, body, flag) ->
      let cond_expr = convert_expr ctx cond in
      (* Coerce FibDynamic condition to bool *)
      let cond_expr =
        if cond_expr.ctype = TCFibDynamic then
          mk_expr_inherit (TCECall (TCTFunc "fib_dynamic_to_bool", [cond_expr])) TCBool [cond_expr]
        else cond_expr
      in
      ctx.loop_depth <- ctx.loop_depth + 1;
      let saved_try_depth_at_loop = ctx.try_depth_at_loop in
      ctx.try_depth_at_loop <- ctx.try_depth;
      let saved_gc_count = gc_save_count ctx in
      (* Yield point for outer loops - inner loops are short-lived *)
      let yield_stmts = if ctx.loop_depth <= 1 then [TCSYieldPoint] else [] in
      let body_stmts = convert_stmt ctx body in
      let to_pop = gc_roots_to_pop ctx saved_gc_count in
      let body_with_pop = if to_pop > 0 then begin
        ctx.gc_local_count <- saved_gc_count;
        yield_stmts @ body_stmts @ [TCSGCPop to_pop]
      end else
        yield_stmts @ body_stmts
      in
      ctx.try_depth_at_loop <- saved_try_depth_at_loop;
      ctx.loop_depth <- ctx.loop_depth - 1;
      let is_do_while = (flag = DoWhile) in
      [TCSWhile (cond_expr, body_with_pop, is_do_while)]
  
  (* Return statement - with GC root cleanup when inside a converted function.
   * When inside a try block (try_depth > 0), we must also emit fib_exc_pop()
   * for each enclosing try, since the return bypasses FIB_CATCH_BEGIN which
   * normally pops the exception handler. Order: evaluate expr, pop exc handlers,
   * pop GC roots, return. *)
  | TReturn expr_opt ->
      let try_pops = exc_pop_stmts ctx.try_depth in
      if ctx.in_gc_frame then begin
        (* GCFrame path: pop any legacy temp roots (from stack-alloc field tracking),
         * then emit GC_FRAME_POP before return. *)
        let has_frame_slots = ctx.gc_frame_slots <> [] in
        let temp_root_pop = if ctx.gc_local_count > 0 then [TCSGCPop ctx.gc_local_count] else [] in
        let frame_pop = if has_frame_slots then [TCSGCFramePop ctx.gc_frame_name] else [] in
        let cleanup = try_pops @ temp_root_pop @ frame_pop in
        let needs_cleanup = cleanup <> [] in
        match expr_opt with
        | None ->
            cleanup @ [TCSReturn None]
        | Some inner ->
            let inner_expr = convert_expr ctx inner in
            (* Anonymous objects returned from functions must be heap-allocated,
               since stack-allocated compound literals (FIB_ANON_NEW_N) become
               dangling pointers once the function's stack frame is popped. *)
            let inner_expr = mark_anon_heap_alloc inner_expr in
            let cexpr = match ctx.current_ret_type with
              | Some ret_tc -> coerce_to_type inner_expr ret_tc
              | None -> inner_expr
            in
            let has_pending = cexpr.pending_stmts <> [] in
            if not needs_cleanup && not has_pending then
              [TCSReturn (Some cexpr)]
            else if not has_pending then begin
              (* Always evaluate the return expression BEFORE cleanup.
               * The return expression may reference _gc frame slots (e.g. _gc.cmd,
               * _gc.this->field) or call functions that trigger GC. If cleanup runs
               * first, the GCFrame is unlinked and those references become unrooted.
               * Save to __ret temp regardless of return type. *)
              let ret_type = cexpr.ctype in
              let stmts = ref [] in
              stmts := !stmts @ [TCSVar {
                vd_name = "__ret"; vd_type = ret_type;
                vd_init = Some cexpr;
                vd_static = false; vd_const = false; vd_volatile = false }];
              stmts := !stmts @ cleanup;
              stmts := !stmts @ [TCSReturn (Some (mk_expr (TCELocal "__ret") ret_type))];
              [TCSBlock !stmts]
            end else begin
              (* Complex: pending stmts + cleanup *)
              let ret_type = cexpr.ctype in
              let stmts = ref [] in
              stmts := !stmts @ cexpr.pending_stmts;
              stmts := !stmts @ [TCSVar {
                vd_name = "__ret"; vd_type = ret_type;
                vd_init = Some { cexpr with pending_stmts = [] };
                vd_static = false; vd_const = false; vd_volatile = false }];
              stmts := !stmts @ cleanup;
              stmts := !stmts @ [TCSReturn (Some (mk_expr (TCELocal "__ret") ret_type))];
              [TCSBlock !stmts]
            end
      end else if ctx.func_gc_root_count < 0 then begin
        (* Legacy path -- function prologue handled by gen_function in genfiberus.ml *)
        let ret_expr = match expr_opt with
          | None -> None
          | Some inner ->
              let inner_expr = mark_anon_heap_alloc (convert_expr ctx inner) in
              match ctx.current_ret_type with
              | Some ret_tc -> Some (coerce_to_type inner_expr ret_tc)
              | None -> Some inner_expr
        in
        if try_pops = [] then
          [TCSReturn ret_expr]
        else begin
          match ret_expr with
          | None ->
              try_pops @ [TCSReturn None]
          | Some cexpr ->
              let ret_type = cexpr.ctype in
              [TCSBlock (
                [TCSVar {
                  vd_name = "__ret"; vd_type = ret_type;
                  vd_init = Some cexpr;
                  vd_static = false; vd_const = false; vd_volatile = false }]
                @ try_pops
                @ [TCSReturn (Some (mk_expr (TCELocal "__ret") ret_type))]
              )]
        end
      end else begin
        (* Legacy C-AST function path -- we own the GC cleanup *)
        let total_to_pop = ctx.gc_local_count in
        match expr_opt with
        | None ->
            let gc_pop = if total_to_pop > 0 then [TCSGCPop total_to_pop] else [] in
            try_pops @ gc_pop @ [TCSReturn None]
        | Some inner ->
            let inner_expr = mark_anon_heap_alloc (convert_expr ctx inner) in
            let cexpr = match ctx.current_ret_type with
              | Some ret_tc -> coerce_to_type inner_expr ret_tc
              | None -> inner_expr
            in
            let expr_gc_roots = cexpr.gc_roots in
            let has_pending = cexpr.pending_stmts <> [] in
            let all_to_pop = total_to_pop + expr_gc_roots in
            let is_simple = match inner.eexpr with
              | TConst _ | TLocal _ -> true
              | _ -> false
            in
            if is_simple && all_to_pop = 0 && not has_pending && try_pops = [] then
              [TCSReturn (Some cexpr)]
            else if is_simple && expr_gc_roots = 0 && not has_pending && try_pops = [] then begin
              if total_to_pop > 0 then
                [TCSGCPop total_to_pop; TCSReturn (Some cexpr)]
              else
                [TCSReturn (Some cexpr)]
            end else begin
              let ret_type = cexpr.ctype in
              let stmts = ref [] in
              if has_pending then
                stmts := !stmts @ cexpr.pending_stmts;
              stmts := !stmts @ [TCSVar {
                vd_name = "__ret"; vd_type = ret_type;
                vd_init = Some { cexpr with pending_stmts = [] };
                vd_static = false; vd_const = false; vd_volatile = false }];
              stmts := !stmts @ try_pops;
              if all_to_pop > 0 then
                stmts := !stmts @ [TCSGCPop all_to_pop];
              stmts := !stmts @ [TCSReturn (Some (mk_expr (TCELocal "__ret") ret_type))];
              [TCSBlock !stmts]
            end
      end
  
  (* Break - pop exception handlers between here and enclosing loop *)
  | TBreak ->
      (exc_pop_stmts (ctx.try_depth - ctx.try_depth_at_loop)) @ [TCSBreak]
  
  (* Continue - pop exception handlers between here and enclosing loop *)
  | TContinue ->
      (exc_pop_stmts (ctx.try_depth - ctx.try_depth_at_loop)) @ [TCSContinue]
  
  (* Throw *)
  | TThrow e ->
      let exc_expr = convert_expr ctx e in
      (* Box to FibDynamic if not already *)
      let boxed_expr = 
        if exc_expr.ctype = TCFibDynamic then exc_expr
        else
          let b = mk_expr (TCEBox (exc_expr, box_kind_of_type exc_expr.ctype)) TCFibDynamic in
          (* Propagate pending_stmts from the inner expression to the box node,
             since write_expr does not emit pending_stmts of sub-expressions. *)
          { b with pending_stmts = exc_expr.pending_stmts @ b.pending_stmts;
                   gc_roots = exc_expr.gc_roots + b.gc_roots }
      in
      (* Extract pending_stmts and clear them from boxed_expr so the writer
         does not emit them a second time via emit_pending_stmts in TCSThrow. *)
      let pending = boxed_expr.pending_stmts in
      let boxed_expr = { boxed_expr with pending_stmts = [] } in
      pending @ [TCSThrow boxed_expr]
  
  (* Try/catch - increment try_depth while converting the try body so that
   * return/break/continue inside the body emit fib_exc_pop() to clean up
   * the exception handler pushed by FIB_TRY. Catch bodies do NOT increment
   * try_depth because the handler has already been consumed by the throw. *)
  | TTry (body, catches) ->
      let saved_try_depth = ctx.try_depth in
      ctx.try_depth <- ctx.try_depth + 1;
      let body_stmts = convert_stmt ctx body in
      ctx.try_depth <- saved_try_depth;
      let catch_blocks = List.map (fun (v, catch_body) ->
        let ct = tc_type_of v.v_type in
        let ck = match ct with
          | TCFibDynamic -> TCCatchDynamic
          | TCInt32 -> TCCatchInt
          | TCFloat64 -> TCCatchFloat
          | TCBool -> TCCatchBool
          | TCFibString -> TCCatchString
          | TCFibClass name -> TCCatchObject name
          | TCFibEnum name -> TCCatchEnum name
          | _ -> TCCatchDynamic
        in
        {
          catch_var = ident v.v_name;
          catch_type = ct;
          catch_kind = ck;
          catch_body = convert_stmt ctx catch_body;
        }
      ) catches in
      [TCSTry { try_body = body_stmts; try_catches = catch_blocks }]
  
  (* Switch - detect string switches and emit if/else chain instead of C switch *)
  | TSwitch sw ->
      if is_string_type sw.switch_subject.etype then begin
        (* String switch: emit if/else chain with fib_string_eq *)
        let subj_expr = convert_expr ctx sw.switch_subject in
        (* Store subject in a temp variable to avoid re-evaluation *)
        let tmp_name = Printf.sprintf "_sw%d" (ctx.closure_counter) in
        ctx.closure_counter <- ctx.closure_counter + 1;
        let tmp_var = TCSVar { vd_name = tmp_name; vd_type = TCFibString;
                               vd_init = Some { subj_expr with pending_stmts = [] };
                               vd_static = false; vd_const = false; vd_volatile = false } in
        let tmp_ref = mk_expr (TCELocal tmp_name) TCFibString in
        (* Build if/else chain *)
        let cases = List.map (fun case ->
          (* Join multiple patterns with || *)
          let cond = match case.case_patterns with
            | [pat] ->
                let pat_expr = convert_expr ctx pat in
                mk_expr (TCECall (TCTFunc "fib_string_eq", [tmp_ref; pat_expr])) TCBool
            | pats ->
                let pat_exprs = List.map (fun pat ->
                  let pe = convert_expr ctx pat in
                  mk_expr (TCECall (TCTFunc "fib_string_eq", [tmp_ref; pe])) TCBool
                ) pats in
                List.fold_left (fun acc e ->
                  mk_expr (TCEBinop (TCOpBoolOr, acc, e)) TCBool
                ) (List.hd pat_exprs) (List.tl pat_exprs)
          in
          let body = convert_stmt ctx case.case_expr in
          (cond, body)
        ) sw.switch_cases in
        let default_stmts = Option.map (convert_stmt ctx) sw.switch_default in
        (* Build nested if/else chain from cases *)
        let rec build_chain = function
          | [] -> (match default_stmts with
                   | Some stmts -> stmts
                   | None -> [])
          | [(cond, body)] ->
              [TCSIf (cond, body, default_stmts)]
          | (cond, body) :: rest ->
              let else_chain = build_chain rest in
              [TCSIf (cond, body, Some else_chain)]
        in
        subj_expr.pending_stmts @ [tmp_var] @ build_chain cases
      end else begin
        let cond_expr = convert_expr ctx sw.switch_subject in
        let is_c_switchable = match cond_expr.ctype with
          | TCInt32 | TCInt64 | TCInt8 | TCInt16
          | TCUInt8 | TCUInt16 | TCUInt32 | TCUInt64
          | TCChar | TCBool -> true
          | _ -> false
        in
        if is_c_switchable then begin
          (* Integer/enum switch - use C switch *)
          let case_blocks = List.map (fun case ->
            let value_exprs = List.map (convert_expr ctx) case.case_patterns in
            let body_stmts = convert_stmt ctx case.case_expr in
            (value_exprs, body_stmts)
          ) sw.switch_cases in
          let default_stmts = Option.map (convert_stmt ctx) sw.switch_default in
          cond_expr.pending_stmts @ [TCSSwitch { sw_expr = cond_expr; sw_cases = case_blocks; sw_default = default_stmts }]
        end else begin
          (* Non-integer switch (e.g. FibDynamic from enum params) - emit if/else chain
             with fib_dynamic_equals, mirroring the string switch pattern above *)
          let tmp_name = Printf.sprintf "_sw%d" (ctx.closure_counter) in
          ctx.closure_counter <- ctx.closure_counter + 1;
          let tmp_var = TCSVar { vd_name = tmp_name; vd_type = cond_expr.ctype;
                                 vd_init = Some { cond_expr with pending_stmts = [] };
                                 vd_static = false; vd_const = false; vd_volatile = false } in
          let tmp_ref = mk_expr (TCELocal tmp_name) cond_expr.ctype in
          (* Box subject to FibDynamic if needed (e.g. enum struct types) *)
          let dyn_ref = coerce_to_type tmp_ref TCFibDynamic in
          let cases = List.map (fun case ->
            let cond = match case.case_patterns with
              | [pat] ->
                  let pat_expr = coerce_to_type (convert_expr ctx pat) TCFibDynamic in
                  mk_expr (TCECall (TCTFunc "fib_dynamic_equals", [dyn_ref; pat_expr])) TCBool
              | pats ->
                  let pat_exprs = List.map (fun pat ->
                    let pe = coerce_to_type (convert_expr ctx pat) TCFibDynamic in
                    mk_expr (TCECall (TCTFunc "fib_dynamic_equals", [dyn_ref; pe])) TCBool
                  ) pats in
                  List.fold_left (fun acc e ->
                    mk_expr (TCEBinop (TCOpBoolOr, acc, e)) TCBool
                  ) (List.hd pat_exprs) (List.tl pat_exprs)
            in
            let body = convert_stmt ctx case.case_expr in
            (cond, body)
          ) sw.switch_cases in
          let default_stmts = Option.map (convert_stmt ctx) sw.switch_default in
          let rec build_chain = function
            | [] -> (match default_stmts with
                     | Some stmts -> stmts
                     | None -> [])
            | [(cond, body)] ->
                [TCSIf (cond, body, default_stmts)]
            | (cond, body) :: rest ->
                let else_chain = build_chain rest in
                [TCSIf (cond, body, Some else_chain)]
          in
          cond_expr.pending_stmts @ [tmp_var] @ build_chain cases
        end
      end
  
  (* Meta annotations - handle LoopLabel for break-from-switch-in-loop patterns.
   * The Haxe filter mark_switch_break_loops wraps while loops and their inner
   * break statements with Meta.LoopLabel(n). In C, switch break != loop break,
   * so we use goto to implement labeled breaks. *)
  | TMeta ((Meta.LoopLabel, [(EConst (Int (n, _)), _)], _), inner) ->
      (match inner.eexpr with
      | TWhile _ ->
          let label = Printf.sprintf "_hx_loop_end_%s" n in
          let loop_stmts = convert_stmt ctx inner in
          loop_stmts @ [TCSLabel label]
      | TBreak ->
          let label = Printf.sprintf "_hx_loop_end_%s" n in
          (* LoopLabel break uses goto to exit the loop; pop try handlers like a regular break *)
          (exc_pop_stmts (ctx.try_depth - ctx.try_depth_at_loop)) @ [TCSGoto label]
      | _ -> convert_stmt ctx inner)
  | TMeta (_, inner) ->
      convert_stmt ctx inner

  (* Expression statement *)
  | _ ->
      let expr = convert_expr ctx e in
      [TCSExpr expr]
  in
  line_stmts @ stmts

(* ============================================================================
 * Function Conversion
 * ============================================================================ *)

(* Convert a Haxe function to C-AST function definition (bare — no prologue/epilogue).
   Used for closures and other contexts where the caller manages GC setup. *)
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
  (* Set return type in context for proper coercion *)
  let body_ctx = { ctx with current_ret_type = Some ret_type; last_line = 0; has_stack_frame = false } in
  let body = convert_stmt body_ctx func.tf_expr in
  {
    fd_name = name;
    fd_ret = ret_type;
    fd_args = args;
    fd_body = body;
    fd_static = false;  (* C static keyword, not Haxe static *)
    fd_inline = false;
    fd_attrs = [];
  }

(* ============================================================================
 * Peephole optimization: fib_bytes_alloc + fib_bytes_fill fusion
 * 
 * When Bytes.alloc(n) is followed by fill(0, n, val), the calloc zeroing in
 * fib_bytes_alloc is redundant because fill will memset the entire buffer.
 * This pass replaces fib_bytes_alloc with fib_bytes_alloc_uninitialized
 * when a full-range fill is detected in the same scope.
 * ============================================================================ *)

(* Extract the size argument from a "fib_bytes_alloc(SIZE)" raw string *)
let extract_bytes_alloc_size (raw : string) : string option =
  let prefix = "fib_bytes_alloc(" in
  let prefix_len = String.length prefix in
  if String.length raw > prefix_len + 1 
     && String.sub raw 0 prefix_len = prefix 
     && raw.[String.length raw - 1] = ')' then
    Some (String.sub raw prefix_len (String.length raw - prefix_len - 1))
  else
    None

(* Check if string s contains substring sub *)
let string_contains s sub =
  let sub_len = String.length sub in
  let s_len = String.length s in
  if sub_len > s_len then false
  else begin
    let found = ref false in
    for i = 0 to s_len - sub_len do
      if not !found && String.sub s i sub_len = sub then
        found := true
    done;
    !found
  end

(* Check if a raw string is "fib_bytes_fill(EXPR, 0, SIZE, VALUE)" with matching size *)
let is_matching_bytes_fill (raw : string) (alloc_size : string) : bool =
  let prefix = "fib_bytes_fill(" in
  let prefix_len = String.length prefix in
  if String.length raw > prefix_len && String.sub raw 0 prefix_len = prefix then begin
    (* Parse arguments: skip first arg (the data pointer), check pos=0, match size *)
    let inner = String.sub raw prefix_len (String.length raw - prefix_len - 1) in
    (* Look for ", 0, SIZE, " or ", 0, SIZE)" pattern *)
    string_contains inner (", 0, " ^ alloc_size ^ ", ")
    || string_contains inner (", 0, " ^ alloc_size ^ ")")
  end else
    false

(* Check if a statement list contains a full-range fib_bytes_fill for the given alloc size *)
let rec has_matching_fill (stmts : tc_stmt list) (alloc_size : string) : bool =
  List.exists (fun stmt ->
    match stmt with
    | TCSExpr { cexpr = TCERaw raw; _ } ->
        is_matching_bytes_fill raw alloc_size
    | _ -> false
  ) stmts

(* Replace "fib_bytes_alloc(" with "fib_bytes_alloc_uninitialized(" in a raw string *)
let replace_alloc_with_uninit (raw : string) : string =
  let old_prefix = "fib_bytes_alloc(" in
  let new_prefix = "fib_bytes_alloc_uninitialized(" in
  if String.length raw >= String.length old_prefix 
     && String.sub raw 0 (String.length old_prefix) = old_prefix then
    new_prefix ^ String.sub raw (String.length old_prefix) (String.length raw - String.length old_prefix)
  else
    raw

(* Apply bytes alloc+fill peephole optimization to a statement list.
   Recurses into while loops, if branches, and blocks. *)
let rec peephole_bytes_alloc_fill (stmts : tc_stmt list) : tc_stmt list =
  (* First pass: collect alloc sizes that have matching fills in this scope *)
  let alloc_sizes_with_fill = Hashtbl.create 4 in
  List.iter (fun stmt ->
    match stmt with
    | TCSVar { vd_type = TCFibBytesData; vd_init = Some { cexpr = TCERaw raw; _ }; _ } ->
        (match extract_bytes_alloc_size raw with
         | Some size when has_matching_fill stmts size ->
             Hashtbl.replace alloc_sizes_with_fill size true
         | _ -> ())
    | _ -> ()
  ) stmts;
  (* Second pass: rewrite alloc calls and recurse into sub-statements *)
  List.map (fun stmt ->
    match stmt with
    | TCSVar ({ vd_type = TCFibBytesData; vd_init = Some ({ cexpr = TCERaw raw; _ } as init_expr); _ } as vd) ->
        (match extract_bytes_alloc_size raw with
         | Some size when Hashtbl.mem alloc_sizes_with_fill size ->
             let new_raw = replace_alloc_with_uninit raw in
             TCSVar { vd with vd_init = Some { init_expr with cexpr = TCERaw new_raw } }
         | _ -> stmt)
    | TCSWhile (cond, body, is_do) ->
        TCSWhile (cond, peephole_bytes_alloc_fill body, is_do)
    | TCSBlock body ->
        TCSBlock (peephole_bytes_alloc_fill body)
    | TCSIf (cond, then_stmts, else_stmts) ->
        TCSIf (cond, peephole_bytes_alloc_fill then_stmts,
               Option.map peephole_bytes_alloc_fill else_stmts)
    | TCSFor (init, cond, step, body) ->
        TCSFor (init, cond, step, peephole_bytes_alloc_fill body)
    | _ -> stmt
  ) stmts

(* Convert a Haxe class method to C-AST function definition WITH full prologue/epilogue.
   Uses GCFrame-based shadow stack for GC root tracking.
   Emits: FIB_GC_CTX, GCFrame declaration, GC safe point, debug assertions,
   stack frame, escape analysis setup, and GC_FRAME_POP at return/end.
   This replaces gen_function in genfiberus.ml. *)
let convert_class_method ctx name (func : tfunc) is_static class_name =
  let ret_type = tc_type_of func.tf_type in
  let filtered_args = filter_void_args func.tf_args in
  let tc_args = List.map (fun (v, _) ->
    { fa_name = ident v.v_name; fa_type = tc_type_of v.v_type }
  ) filtered_args in
  (* Add 'this' parameter for instance methods *)
  let fd_args = if is_static then tc_args
    else { fa_name = "this"; fa_type = TCFibClass class_name } :: tc_args
  in
  let func_name = Printf.sprintf "%s_%s" class_name (ident name) in
  (* Run escape analysis *)
  let escape_result = analyze_function func in
  (* Set up GCFrame-based body context.
   * We register param slots upfront, then the body conversion adds more slots
   * as it encounters GC-typed locals and expression temps.
   * After body conversion, we know ALL slots and prepend the frame declaration. *)
  let frame_name = "_gc" in
  let frame_rooted_vars = Hashtbl.create 16 in
  let param_inits = ref [] in
   (* Collect GC-typed parameters as initial frame slots.
      For optional parameters with non-null defaults, substitute the default
      when the param is null at runtime.
      Handles FibDynamic params (boxed defaults) and enum params (index sentinel). *)
   let initial_slots = ref [] in
  List.iter (fun (v, default_opt) ->
    let tc = tc_type_of v.v_type in
    let vname = ident v.v_name in
    if needs_gc_root tc then begin
      initial_slots := (vname, tc) :: !initial_slots;
      Hashtbl.replace frame_rooted_vars vname ();
      let init_expr = mk_expr (TCELocal vname) tc in
      let init_expr = match tc, default_opt with
      | TCFibDynamic, Some { Type.eexpr = Type.TConst c } when c <> Type.TNull ->
          let boxed_default = match c with
            | Type.TInt i -> mk_expr (TCEBox (mk_expr (TCEInt i) TCInt32, TCBoxInt)) TCFibDynamic
            | Type.TFloat s -> mk_expr (TCEBox (mk_expr (TCEFloat s) TCFloat64, TCBoxFloat)) TCFibDynamic
            | Type.TBool b -> mk_expr (TCEBox (mk_expr (TCEBool b) TCBool, TCBoxBool)) TCFibDynamic
            | Type.TString s -> mk_expr (TCEBox (mk_expr (TCEString s) TCFibString, TCBoxString)) TCFibDynamic
            | _ -> init_expr
          in
          if boxed_default != init_expr then
            let null_check = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [init_expr])) TCBool in
            mk_expr (TCETernary (null_check, boxed_default, init_expr)) TCFibDynamic
          else init_expr
      | TCFibDynamic, Some default_e when (match default_e.Type.eexpr with Type.TConst Type.TNull -> false | _ -> true) ->
          let converted = convert_expr ctx default_e in
          let boxed = coerce_to_type converted TCFibDynamic in
          let null_check = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [init_expr])) TCBool in
          mk_expr (TCETernary (null_check, boxed, init_expr)) TCFibDynamic
      | TCFibString, Some { Type.eexpr = Type.TConst (Type.TString s) } ->
          let default_str = mk_expr (TCEString s) TCFibString in
          let null_check = mk_expr (TCEBinop (TCOpEq, init_expr, mk_expr TCENull TCFibString)) TCBool in
          mk_expr (TCETernary (null_check, default_str, init_expr)) TCFibString
      | TCFibString, Some default_e when (match default_e.Type.eexpr with Type.TConst Type.TNull -> false | _ -> true) ->
          let converted = convert_expr ctx default_e in
          let default_str = coerce_to_type converted TCFibString in
          let null_check = mk_expr (TCEBinop (TCOpEq, init_expr, mk_expr TCENull TCFibString)) TCBool in
          mk_expr (TCETernary (null_check, default_str, init_expr)) TCFibString
      | TCFibEnum _, Some default_e when (match default_e.Type.eexpr with Type.TConst Type.TNull -> false | _ -> true) ->
          let converted = convert_expr ctx default_e in
          let index_field = mk_expr (TCERaw (vname ^ ".index")) TCInt32 in
          let null_check = mk_expr (TCEBinop (TCOpEq, index_field, mk_expr (TCEUnop (TCUNeg, mk_expr (TCEInt 1l) TCInt32)) TCInt32)) TCBool in
          mk_expr (TCETernary (null_check, converted, init_expr)) tc
      | _ -> init_expr
      in
      param_inits := (vname, init_expr) :: !param_inits
    end
  ) filtered_args;
  (* Add 'this' for instance methods *)
  if not is_static then begin
    let this_tc = TCFibClass class_name in
    initial_slots := ("this", this_tc) :: !initial_slots;
    Hashtbl.replace frame_rooted_vars "this" ();
    param_inits := ("this", mk_expr (TCELocal "this") this_tc) :: !param_inits
  end;
  (* Convert body with GCFrame tracking enabled *)
  let body_ctx = {
    ctx with
    current_ret_type = Some ret_type;
    gc_local_count = 0;  (* Not used in frame mode *)
    func_gc_root_count = 0;  (* Not used in frame mode *)
    gc_frame_name = frame_name;
    gc_frame_slots = List.rev !initial_slots;  (* param slots first, in order *)
    gc_frame_rooted_vars = frame_rooted_vars;
    in_gc_frame = true;
    fiber_mature_vars = escape_result.fiber_mature_vars;
    stack_alloc_vars = escape_result.stack_allocatable;
    last_line = 0;  (* Reset for fresh FIBLINE dedup per function *)
    has_stack_frame = ctx.debug_level > 0;  (* TCSStackFrame emitted when debug_level > 0 *)
  } in
  let body_stmts = convert_stmt body_ctx func.tf_expr in
  (* Mark non-GC locals as volatile if function body contains try/catch *)
  let body_stmts = mark_volatile_for_try body_stmts in
  (* Peephole: replace fib_bytes_alloc with fib_bytes_alloc_uninitialized
     when a full-range fib_bytes_fill follows in the same scope *)
  let body_stmts = peephole_bytes_alloc_fill body_stmts in
  (* For non-GC enum params with defaults, emit null-sentinel substitution.
     These are value-type params not tracked in the GC frame but need
     their default applied when the caller passes the null sentinel. *)
  let enum_default_stmts = List.filter_map (fun (v, default_opt) ->
    let tc = tc_type_of v.v_type in
    let vname = ident v.v_name in
    match tc, default_opt with
    | TCFibEnum _, Some default_e when (match default_e.Type.eexpr with Type.TConst Type.TNull -> false | _ -> true) ->
        let converted = convert_expr ctx default_e in
        let index_field = mk_expr (TCERaw (vname ^ ".index")) TCInt32 in
        let null_check = mk_expr (TCEBinop (TCOpEq, index_field, mk_expr (TCEUnop (TCUNeg, mk_expr (TCEInt 1l) TCInt32)) TCInt32)) TCBool in
        let assign = TCSExpr (mk_expr (TCEAssign (mk_expr (TCELocal vname) tc, converted)) tc) in
        Some (TCSIf (null_check, [assign], None))
    | _ -> None
  ) filtered_args in
  let body_stmts = enum_default_stmts @ body_stmts in
  (* Propagate closures and counters back to caller's context *)
  ctx.closures <- body_ctx.closures @ ctx.closures;
  ctx.closure_counter <- body_ctx.closure_counter;
  ctx.spawn_counter <- body_ctx.spawn_counter;
  (* Build prologue: FIB_GC_CTX + GCFrame declaration *)
  let prologue = ref [] in
  prologue := [TCSGCCtx];
  (* Suppress -Wunused-parameter for scalar (non-GC) parameters that may not
     be referenced in the body (e.g., encoding, index).  GC-rooted params are
     always used because they're assigned into the GC frame. *)
  List.iter (fun arg ->
    if not (Hashtbl.mem frame_rooted_vars arg.fa_name) then
      prologue := !prologue @ [TCSExpr (mk_expr (TCECast (TCVoid, mk_expr (TCELocal arg.fa_name) arg.fa_type)) TCVoid)]
  ) tc_args;
  (* Build frame info with all accumulated slots (params + body locals + temps) *)
  let frame_info = gc_frame_build_info_with_inits body_ctx !param_inits in
  let has_gc_slots = frame_info.gfi_slots <> [] in
  if has_gc_slots then
    prologue := !prologue @ [TCSGCFrameDecl frame_info];
  (* GC safe point — now that roots are in frame *)
  prologue := !prologue @ [TCSGCSafePoint];
  (* Stack frame for source mapping *)
  if ctx.debug_level > 0 then begin
    let file = strip_file func.tf_expr.epos.pfile in
    let line = Lexer.get_error_line func.tf_expr.epos in
    prologue := !prologue @ [TCSStackFrame {
      sf_class = class_name;
      sf_func = name;
      sf_file = file;
      sf_line = line;
    }]
  end;
  (* Epilogue: pop any legacy temp roots (from stack-alloc fields) + GC_FRAME_POP for fall-through *)
  let epilogue = if not (ends_with_return func.tf_expr) then begin
    let temp_pop = if body_ctx.gc_local_count > 0 then [TCSGCPop body_ctx.gc_local_count] else [] in
    let frame_pop = if has_gc_slots then [TCSGCFramePop frame_name] else [] in
    temp_pop @ frame_pop
  end else [] in
  {
    fd_name = func_name;
    fd_ret = ret_type;
    fd_args = fd_args;
    fd_body = !prologue @ body_stmts @ epilogue;
    fd_static = false;
    fd_inline = false;
    fd_attrs = [];
  }

(* Convert a Haxe constructor to two C-AST function definitions:
   1. ClassName_init(this, args) — initializes fields on existing object
   2. ClassName_new(args) — allocates and calls _init
   Returns None for empty constructors or simple constructors (handled in header).
   This replaces gen_constructor in genfiberus.ml. *)
let convert_constructor ctx (c : tclass) =
  let class_name = match ctx.current_class_name with
    | Some n -> n | None -> flat_path c.cl_path in
  let has_dyn_instance_methods = List.exists (fun cf2 ->
    match cf2.cf_kind with Method MethDynamic -> true | _ -> false
  ) c.cl_ordered_fields in
  match c.cl_constructor with
  | None when has_dyn_instance_methods ->
      (* No explicit constructor but class has MethDynamic fields.
         Generate _init that creates closures for dynamic fields. *)
      let this_tc = TCFibClass class_name in
      let frame_name = "_gc" in
      let frame_rooted_vars = Hashtbl.create 8 in
      Hashtbl.replace frame_rooted_vars "this" ();
      let init_body_ctx = {
        ctx with
        current_ret_type = None;
        gc_local_count = 0;
        func_gc_root_count = 0;
        gc_frame_name = frame_name;
        gc_frame_slots = [("this", this_tc)];
        gc_frame_rooted_vars = frame_rooted_vars;
        in_gc_frame = true;
        fiber_mature_vars = Hashtbl.create 0;
        stack_alloc_vars = Hashtbl.create 0;
        last_line = 0;
        has_stack_frame = false;
      } in
      let dyn_init_stmts = List.fold_left (fun acc cf2 ->
        match cf2.cf_kind, cf2.cf_expr with
        | Method MethDynamic, Some ({ eexpr = TFunction _ } as func_expr) ->
          let this_expr = { eexpr = TConst TThis;
            etype = TInst (c, extract_param_types c.cl_params);
            epos = c.cl_pos } in
          let field_access = { eexpr = TField (this_expr, FInstance (c, [], cf2));
            etype = cf2.cf_type; epos = cf2.cf_pos } in
          let assign_expr = { eexpr = TBinop (OpAssign, field_access, func_expr);
            etype = cf2.cf_type; epos = cf2.cf_pos } in
          let this_local = mk_expr (TCELocal "this") (TCFibClass class_name) in
          let field_expr = mk_expr (TCEArrow (this_local, ident cf2.cf_name)) (TCPointer TCVoid) in
          let null_expr = mk_expr TCENull (TCPointer TCVoid) in
          let cond = mk_expr (TCEBinop (TCOpEq, field_expr, null_expr)) TCBool in
          acc @ [TCSIf (cond, convert_expr_as_stmt init_body_ctx assign_expr, None)]
        | _ -> acc
      ) [] c.cl_ordered_fields in
      ctx.closures <- init_body_ctx.closures @ ctx.closures;
      ctx.closure_counter <- init_body_ctx.closure_counter;
      ctx.spawn_counter <- init_body_ctx.spawn_counter;
      let init_prologue = ref [TCSGCCtx] in
      let init_epilogue = ref [] in
      let param_inits = [("this", mk_expr (TCELocal "this") this_tc)] in
      let frame_info = gc_frame_build_info_with_inits init_body_ctx param_inits in
      let has_gc_slots = frame_info.gfi_slots <> [] in
      if has_gc_slots then
        init_prologue := !init_prologue @ [TCSGCFrameDecl frame_info];
      if init_body_ctx.gc_local_count > 0 then
        init_epilogue := [TCSGCPop init_body_ctx.gc_local_count];
      if has_gc_slots then
        init_epilogue := !init_epilogue @ [TCSGCFramePop frame_name];
      let init_func = {
        fd_name = Printf.sprintf "%s_init" class_name;
        fd_ret = TCVoid;
        fd_args = [{ fa_name = "this"; fa_type = this_tc }];
        fd_body = !init_prologue @ dyn_init_stmts @ !init_epilogue;
        fd_static = false; fd_inline = false; fd_attrs = [];
      } in
      (* _new must root 'this' in a GCFrame so nursery evacuation
         during _init does not leave the local pointer stale. *)
      let gc_this_expr = mk_expr (TCEDot (mk_expr (TCELocal "_gc") TCVoid, "this")) this_tc in
      let alloc_stmt = TCSGCFrameAssign ("_gc", "this",
        mk_expr (TCERaw (Printf.sprintf
          "gc_alloc_object_with_class(sizeof(%s), &%s_class)" class_name class_name)) this_tc) in
      let init_call = TCSExpr (mk_expr (TCECall (
        TCTFunc (Printf.sprintf "%s_init" class_name),
        [gc_this_expr]
      )) TCVoid) in
      let return_this = TCSReturn (Some gc_this_expr) in
      let new_frame_info = {
        gfi_name = "_gc";
        gfi_slots = [{ gfs_name = "this"; gfs_type = this_tc; gfs_init = None }];
      } in
      let new_func = {
        fd_name = Printf.sprintf "%s_new" class_name;
        fd_ret = this_tc;
        fd_args = [];
        fd_body = [TCSGCCtx; TCSGCFrameDecl new_frame_info;
                   alloc_stmt; init_call;
                   TCSGCFramePop "_gc"; return_this];
        fd_static = false; fd_inline = false; fd_attrs = [];
      } in
      Some (init_func, new_func)
  | None -> None
  | Some cf ->
      (match cf.cf_expr with
      | Some { eexpr = TFunction func } ->
           let has_dyn_methods = List.exists (fun cf2 ->
             match cf2.cf_kind with Method MethDynamic -> true | _ -> false
           ) c.cl_ordered_fields in
           if FiberusGenClass.is_simple_constructor func && not has_dyn_methods then
             None  (* Simple constructors generated inline in header *)
           else begin
            let filtered_args = filter_void_args func.tf_args in
            let tc_args = List.map (fun (v, _) ->
              { fa_name = ident v.v_name; fa_type = tc_type_of v.v_type }
            ) filtered_args in
            let escape_result = analyze_function func in
            (* === _init function (GCFrame-based) ===
               Always emit FIB_GC_CTX and use the GCFrame path, matching
               convert_class_method.  The previous ctor_needs_gc_context heuristic
               was incomplete: it missed MethDynamic field inits and string-concat
               temporaries, causing undeclared _fib_gc_ctx errors. *)
            let frame_name = "_gc" in
            let frame_rooted_vars = Hashtbl.create 16 in
            let param_inits = ref [] in
            let initial_slots = ref [] in
            (* Collect GC-typed parameters as initial frame slots *)
            List.iter (fun (v, _) ->
              let tc = tc_type_of v.v_type in
              let vname = ident v.v_name in
              if needs_gc_root tc then begin
                initial_slots := (vname, tc) :: !initial_slots;
                Hashtbl.replace frame_rooted_vars vname ();
                param_inits := (vname, mk_expr (TCELocal vname) tc) :: !param_inits
              end
            ) filtered_args;
            (* Add 'this' *)
            let this_tc = TCFibClass class_name in
            initial_slots := ("this", this_tc) :: !initial_slots;
            Hashtbl.replace frame_rooted_vars "this" ();
            param_inits := ("this", mk_expr (TCELocal "this") this_tc) :: !param_inits;
            let init_body_ctx = {
              ctx with
              current_ret_type = None;
              gc_local_count = 0;
              func_gc_root_count = 0;
              gc_frame_name = frame_name;
              gc_frame_slots = List.rev !initial_slots;
              gc_frame_rooted_vars = frame_rooted_vars;
              in_gc_frame = true;
              fiber_mature_vars = escape_result.fiber_mature_vars;
              stack_alloc_vars = escape_result.stack_allocatable;
              last_line = 0;  (* Reset for fresh FIBLINE dedup per function *)
              has_stack_frame = false;  (* _init has no FIB_STACKFRAME *)
            } in
            (* Generate MethDynamic field default closure initializations.
               Like HashLink (genhl.ml:3549), we must init dynamic function fields
               BEFORE the user constructor body runs, so that e.g. emptyOnData = onData
               can read the already-initialized default closure. *)
            let dyn_init_stmts = List.fold_left (fun acc cf ->
              match cf.cf_kind, cf.cf_expr with
              | Method MethDynamic, Some ({ eexpr = TFunction _ } as func_expr) ->
                (* Synthesize: if (this.fieldName == NULL) this.fieldName = <default closure> *)
                let this_expr = { eexpr = TConst TThis;
                  etype = TInst (c, extract_param_types c.cl_params);
                  epos = c.cl_pos } in
                let field_access = { eexpr = TField (this_expr, FInstance (c, [], cf));
                  etype = cf.cf_type; epos = cf.cf_pos } in
                let assign_expr = { eexpr = TBinop (OpAssign, field_access, func_expr);
                  etype = cf.cf_type; epos = cf.cf_pos } in
                let this_local = mk_expr (TCELocal "this") (TCFibClass class_name) in
                let field_expr = mk_expr (TCEArrow (this_local, ident cf.cf_name)) (TCPointer TCVoid) in
                let null_expr = mk_expr TCENull (TCPointer TCVoid) in
                let cond = mk_expr (TCEBinop (TCOpEq, field_expr, null_expr)) TCBool in
                acc @ [TCSIf (cond, convert_expr_as_stmt init_body_ctx assign_expr, None)]
              | _ -> acc
            ) [] c.cl_ordered_fields in
            let init_body_stmts = convert_stmt init_body_ctx func.tf_expr in
            let init_body_stmts = dyn_init_stmts @ init_body_stmts in
            let init_body_stmts = mark_volatile_for_try init_body_stmts in
            ctx.closures <- init_body_ctx.closures @ ctx.closures;
            ctx.closure_counter <- init_body_ctx.closure_counter;
            ctx.spawn_counter <- init_body_ctx.spawn_counter;
            let init_prologue = ref [TCSGCCtx] in
            (* Suppress -Wunused-parameter for scalar (non-GC) constructor params
               that may not be referenced in the body (mirrors convert_class_method). *)
            List.iter (fun arg ->
              if not (Hashtbl.mem frame_rooted_vars arg.fa_name) then
                init_prologue := !init_prologue @ [TCSExpr (mk_expr (TCECast (TCVoid, mk_expr (TCELocal arg.fa_name) arg.fa_type)) TCVoid)]
            ) tc_args;
            let init_epilogue = ref [] in
            let frame_info = gc_frame_build_info_with_inits init_body_ctx !param_inits in
            let has_gc_slots = frame_info.gfi_slots <> [] in
            if has_gc_slots then
              init_prologue := !init_prologue @ [TCSGCFrameDecl frame_info];
            (* Pop any legacy temp roots (from stack-alloc fields) + frame pop *)
            if init_body_ctx.gc_local_count > 0 then
              init_epilogue := [TCSGCPop init_body_ctx.gc_local_count];
            if has_gc_slots then
              init_epilogue := !init_epilogue @ [TCSGCFramePop frame_name];
            let init_func = {
              fd_name = Printf.sprintf "%s_init" class_name;
              fd_ret = TCVoid;
              fd_args = { fa_name = "this"; fa_type = TCFibClass class_name } :: tc_args;
              fd_body = !init_prologue @ init_body_stmts @ !init_epilogue;
              fd_static = false;
              fd_inline = false;
              fd_attrs = [];
            } in
            (* === _new function (GCFrame-based) ===
               Always create a GCFrame that includes 'this' so the pointer
               stays valid if GC evacuates the object during _init.
               _init pushes its own frame and updates its copy of 'this',
               but without rooting 'this' here the _new local would go
               stale after nursery evacuation. *)
            let gc_param_args = List.filter (fun (v, _) ->
              needs_gc_root (tc_type_of v.v_type)
            ) filtered_args in
            (* Allocate 'this' — mature or nursery depending on fiber capture analysis *)
            let alloc_func = if escape_result.this_needs_mature then
              "gc_alloc_mature_object_with_class"
            else
              "gc_alloc_object_with_class"
            in
            (* Allocate into _gc.this so the GCFrame tracks the pointer *)
            let alloc_stmt = TCSGCFrameAssign ("_gc", "this",
              mk_expr (TCERaw (Printf.sprintf "%s(sizeof(%s), &%s_class)"
                alloc_func class_name class_name)) (TCFibClass class_name)) in
            let this_tc = TCFibClass class_name in
            let gc_this_expr = mk_expr (TCEDot (mk_expr (TCELocal "_gc") TCVoid, "this")) this_tc in
            let arg_names = List.map (fun (v, _) ->
              let tc = tc_type_of v.v_type in
              let vname = ident v.v_name in
              if needs_gc_root tc then
                mk_expr (TCEDot (mk_expr (TCELocal "_gc") TCVoid, vname)) tc
              else
                mk_expr (TCELocal vname) tc
            ) filtered_args in
            let init_call = TCSExpr (mk_expr (TCECall (
              TCTFunc (Printf.sprintf "%s_init" class_name),
              gc_this_expr :: arg_names
            )) TCVoid) in
            (* Build GCFrame slots: always 'this' + any GC-typed params *)
            let new_frame_slots = ref [] in
            let new_param_inits = ref [] in
            (* 'this' slot — initialized to NULL, assigned after alloc *)
            new_frame_slots := ("this", this_tc) :: !new_frame_slots;
            List.iter (fun (v, _) ->
              let tc = tc_type_of v.v_type in
              let vname = ident v.v_name in
              new_frame_slots := (vname, tc) :: !new_frame_slots;
              new_param_inits := (vname, mk_expr (TCELocal vname) tc) :: !new_param_inits
            ) gc_param_args;
            let new_frame_info = {
              gfi_name = "_gc";
              gfi_slots = List.rev_map (fun (name, typ) ->
                let init = try Some (List.assoc name !new_param_inits) with Not_found -> None in
                { gfs_name = name; gfs_type = typ; gfs_init = init }
              ) !new_frame_slots;
            } in
            let new_prologue = [TCSGCCtx; TCSGCFrameDecl new_frame_info] in
            let new_epilogue = [TCSGCFramePop "_gc"] in
            let return_this = TCSReturn (Some gc_this_expr) in
            let new_func = {
              fd_name = Printf.sprintf "%s_new" class_name;
              fd_ret = TCFibClass class_name;
              fd_args = (if tc_args = [] then [] else tc_args);
              fd_body = new_prologue @ [alloc_stmt; init_call] @ new_epilogue @ [return_this];
              fd_static = false;
              fd_inline = false;
              fd_attrs = [];
            } in
            Some (init_func, new_func)
          end
      | _ -> None)
