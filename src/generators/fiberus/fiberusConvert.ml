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

(* Global counters - simple and avoids all context propagation issues *)
let global_closure_counter = ref 0
let global_spawn_counter = ref 0

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

(* Coerce an expression to a target type (boxing/unboxing as needed) *)
let coerce_to_type expr target_tc =
  if expr.ctype = target_tc then expr
  else if target_tc = TCFibDynamic && expr.ctype <> TCFibDynamic then
    (* Box to FibDynamic *)
    mk_expr (TCEBox (expr, box_kind_of_type expr.ctype)) TCFibDynamic
  else if expr.ctype = TCFibDynamic && target_tc <> TCFibDynamic then
    (* Unbox from FibDynamic *)
    mk_expr (TCEUnbox (expr, target_tc)) target_tc
  else if (expr.ctype = TCInt32 || expr.ctype = TCInt64) && (target_tc = TCFloat64 || target_tc = TCFloat32) then
    (* Numeric promotion: Int -> Float *)
    mk_expr (TCECast (target_tc, expr)) target_tc
  else if (expr.ctype = TCFloat64 || expr.ctype = TCFloat32) && (target_tc = TCInt32 || target_tc = TCInt64) then
    (* Numeric truncation: Float -> Int *)
    mk_expr (TCECast (target_tc, expr)) target_tc
  else
    (* Other type conversions - just return as-is for now *)
    expr

(* Box all arguments to FibDynamic for use in _fib_dyn_call_N *)
let box_args_for_dynamic_call args =
  List.map (fun arg ->
    if arg.ctype = TCFibDynamic then arg
    else mk_expr (TCEBox (arg, box_kind_of_type arg.ctype)) TCFibDynamic
  ) args

(* Wrap a TCEDynamicCall result with TCEUnbox if the expected return type is not Dynamic/Void *)
let unwrap_dynamic_result dyn_call result_tc =
  if result_tc = TCFibDynamic || result_tc = TCVoid then dyn_call
  else { (mk_expr (TCEUnbox (dyn_call, result_tc)) result_tc) with cpos = dyn_call.cpos; pending_stmts = dyn_call.pending_stmts }

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
  
  (* Object/array allocations *)
  | TCENew _ -> true
  | TCECall (TCTFunc "fib_array_new", _) -> true
  | TCECall (TCTFunc "fib_anon_new", _) -> true
  | TCEAnonObject _ -> true
  | TCEArrayDecl _ -> true
  
  (* Method calls that may allocate (conservatively assume they do if returning GC type) *)
  | TCECall _ when needs_gc_root_tc e.ctype -> true
  | TCEVtableCall _ when needs_gc_root_tc e.ctype -> true
  
  (* Boxing allocates *)
  | TCEBox _ -> true
  
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
  | TCEStringEq _ | TCEStringLength _ -> false
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
    
    if in_frame then begin
      let c = match ctx with Some c -> c | None -> assert false in
      (* GCFrame mode: register slot, declare local, assign to frame *)
      gc_frame_add_slot c tmp_name tmp_type;
      (* Declare local variable *)
      let var_decl = TCSVar {
        vd_name = tmp_name;
        vd_type = tmp_type;
        vd_init = Some e;
        vd_static = false;
        vd_const = false; vd_volatile = false;
      } in
      (* Assign to frame slot for GC visibility *)
      let frame_assign = TCSGCFrameAssign (c.gc_frame_name, tmp_name, mk_expr (TCELocal tmp_name) tmp_type) in
      (* Reference through frame slot so GC updates are visible *)
      let tmp_ref = gc_frame_ref c tmp_name tmp_type in
      (* No gc_roots left on legacy stack — frame handles it *)
      (tmp_ref, [var_decl; frame_assign], 0)
    end else begin
      (* Legacy mode: push/pop *)
      let var_decl = TCSVar {
        vd_name = tmp_name;
        vd_type = tmp_type;
        vd_init = Some e;
        vd_static = false;
        vd_const = false; vd_volatile = false;
      } in
      let cleanup_stmts = 
        if e.gc_roots > 0 then [TCSGCPop e.gc_roots]
        else []
      in
      let gc_push = TCSGCPush (mk_expr (TCELocal tmp_name) tmp_type) in
      let tmp_ref = mk_expr (TCELocal tmp_name) tmp_type in
      (tmp_ref, [var_decl] @ cleanup_stmts @ [gc_push], 1)
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
      let final = make_final e1 e2 in
      { final with 
        pending_stmts = e1.pending_stmts @ e2.pending_stmts @ final.pending_stmts }
    end else begin
      let final_expr = make_final e1' e2' in
      let result_type = final_expr.ctype in
      let result_needs_gc = needs_gc_root_tc result_type in
      let result_name = gen_gc_temp_name () in
      let result_var = TCSVar {
        vd_name = result_name;
        vd_type = result_type;
        vd_init = Some final_expr;
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
      let pending = e1_pending @ e2_pending @ stmts1 @ stmts2 @ frame_stmts in
      mk_expr_lifted_gc (TCELocal result_name) result_type pending 0
    end
  end else begin
    (* Legacy mode: push/pop *)
    if total_input_roots = 0 then begin
      let final = make_final e1 e2 in
      { final with 
        gc_roots = e1.gc_roots + e2.gc_roots;
        pending_stmts = e1.pending_stmts @ e2.pending_stmts @ final.pending_stmts }
    end else begin
      let final_expr = make_final e1' e2' in
      let result_type = final_expr.ctype in
      let result_needs_gc = needs_gc_root_tc result_type in
      let result_name = gen_gc_temp_name () in
      let result_var = TCSVar {
        vd_name = result_name;
        vd_type = result_type;
        vd_init = Some final_expr;
        vd_static = false;
        vd_const = false; vd_volatile = false;
      } in
      let gc_pop = TCSGCPop total_input_roots in
      let pending = 
        if result_needs_gc then
          let result_gc_push = TCSGCPush (mk_expr (TCELocal result_name) result_type) in
          e1_pending @ e2_pending @ stmts1 @ stmts2 @ [result_var; gc_pop; result_gc_push]
        else
          e1_pending @ e2_pending @ stmts1 @ stmts2 @ [result_var; gc_pop]
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
      let final = make_call args in
      { final with 
        pending_stmts = collect_pending args @ final.pending_stmts }
    end else begin
      let final_expr = make_call args' in
      let result_type = final_expr.ctype in
      let result_needs_gc = needs_gc_root_tc result_type in
      let result_name = gen_gc_temp_name () in
      let result_var = TCSVar {
        vd_name = result_name;
        vd_type = result_type;
        vd_init = Some final_expr;
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
      let pending = non_extracted_pending @ all_stmts @ frame_stmts in
      mk_expr_lifted_gc (TCELocal result_name) result_type pending 0
    end
  end else begin
    (* Legacy mode *)
    if total_roots = 0 then begin
      let final = make_call args in
      { final with 
        gc_roots = sum_gc_roots args;
        pending_stmts = collect_pending args @ final.pending_stmts }
    end else begin
      let final_expr = make_call args' in
      let result_type = final_expr.ctype in
      let result_needs_gc = needs_gc_root_tc result_type in
      let result_name = gen_gc_temp_name () in
      let result_var = TCSVar {
        vd_name = result_name;
        vd_type = result_type;
        vd_init = Some final_expr;
        vd_static = false;
        vd_const = false; vd_volatile = false;
      } in
      let gc_pop = TCSGCPop total_roots in
      let pending = 
        if result_needs_gc then
          let result_gc_push = TCSGCPush (mk_expr (TCELocal result_name) result_type) in
          non_extracted_pending @ all_stmts @ [result_var; gc_pop; result_gc_push]
        else
          non_extracted_pending @ all_stmts @ [result_var; gc_pop]
      in
      let result_roots = if result_needs_gc then 1 else 0 in
      mk_expr_lifted_gc (TCELocal result_name) result_type pending result_roots
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
      let final = make_final e in
      { final with 
        pending_stmts = e.pending_stmts @ final.pending_stmts }
    end else begin
      let c = match ctx with Some c -> c | None -> assert false in
      let tmp_name = gen_gc_temp_name () in
      let tmp_type = e.ctype in
      gc_frame_add_slot c tmp_name tmp_type;
      let var_decl = TCSVar {
        vd_name = tmp_name;
        vd_type = tmp_type;
        vd_init = Some e;
        vd_static = false;
        vd_const = false; vd_volatile = false;
      } in
      let frame_assign = TCSGCFrameAssign (c.gc_frame_name, tmp_name, mk_expr (TCELocal tmp_name) tmp_type) in
      (* Reference through frame slot so GC updates are visible *)
      let tmp_ref = gc_frame_ref c tmp_name tmp_type in
      let final_expr = make_final tmp_ref in
      let result_type = final_expr.ctype in
      let result_needs_gc = needs_gc_root_tc result_type in
      if not result_needs_gc then begin
        let result_name = gen_gc_temp_name () in
        let result_var = TCSVar {
          vd_name = result_name;
          vd_type = result_type;
          vd_init = Some final_expr;
          vd_static = false;
          vd_const = false; vd_volatile = false;
        } in
        let pending = e.pending_stmts @ [var_decl; frame_assign; result_var] in
        mk_expr_lifted_gc (TCELocal result_name) result_type pending 0
      end else begin
        let result_name = gen_gc_temp_name () in
        gc_frame_add_slot c result_name result_type;
        let result_var = TCSVar {
          vd_name = result_name;
          vd_type = result_type;
          vd_init = Some final_expr;
          vd_static = false;
          vd_const = false; vd_volatile = false;
        } in
        let result_frame_assign = TCSGCFrameAssign (c.gc_frame_name, result_name, mk_expr (TCELocal result_name) result_type) in
        let pending = e.pending_stmts @ [var_decl; frame_assign; result_var; result_frame_assign] in
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
    (* No extraction needed - just apply make_final directly *)
    let final = make_final e in
    { final with 
      pending_stmts = e.pending_stmts @ final.pending_stmts;
      gc_roots = e.gc_roots }
  end else begin
    (* Expression yields a volatile GC pointer that must be rooted before use.
     * We directly create a rooted temp variable, bypassing extract_if_allocating
     * which would check is_allocating_expr (wrong check for this case). *)
    let tmp_name = gen_gc_temp_name () in
    let tmp_type = e.ctype in
    
    (* Create variable declaration to capture the volatile expression *)
    let var_decl = TCSVar {
      vd_name = tmp_name;
      vd_type = tmp_type;
      vd_init = Some e;
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
    let result_type = final_expr.ctype in
    
    (* Check if result also needs rooting *)
    let result_needs_gc = needs_gc_root_tc result_type in
    
    if not result_needs_gc then begin
      (* Result is not a GC type - compute result, then pop input root *)
      let result_name = gen_gc_temp_name () in
      let result_var = TCSVar {
        vd_name = result_name;
        vd_type = result_type;
        vd_init = Some final_expr;
        vd_static = false;
        vd_const = false; vd_volatile = false;
      } in
      let gc_pop = TCSGCPop 1 in  (* Pop the one root we pushed *)
      let pending = e.pending_stmts @ [var_decl] @ cleanup_stmts @ [gc_push; result_var; gc_pop] in
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
        vd_init = Some final_expr;
        vd_static = false;
        vd_const = false; vd_volatile = false;
      } in
      
      (* Push result root, keep input root - caller pops both *)
      let result_gc_push = TCSGCPush (mk_expr (TCELocal result_name) result_type) in
      
      let pending = e.pending_stmts @ [var_decl] @ cleanup_stmts @ [gc_push; result_var; result_gc_push] in
      
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
      let vtype = tc_type_of v.v_type in
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
      (* Take max of gc_roots from both branches (conservative but safe) *)
      let gc_roots = max then_expr_raw.gc_roots else_expr_raw.gc_roots in
      (* Strip pending_stmts from branch expressions - they'll be propagated to the result.
       * We can't have pending_stmts inside a C ternary expression. *)
      let then_expr_clean = { then_expr with pending_stmts = [] } in
      let else_expr_clean = { else_expr with pending_stmts = [] } in
      let result = mk_expr_pos_gc (TCETernary (cond_expr, then_expr_clean, else_expr_clean)) result_tc pos gc_roots in
      (* IMPORTANT: Propagate pending_stmts from condition AND both branches.
       * All temp variables must be declared before the ternary expression. *)
      { result with 
        pending_stmts = cond_expr_raw.pending_stmts @ then_expr_raw.pending_stmts @ else_expr_raw.pending_stmts @ result.pending_stmts;
        gc_roots = cond_expr_raw.gc_roots + gc_roots }
  
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
  
  (* Function expression - create a closure *)
  | TFunction f ->
      (* Find free variables that need to be captured *)
      let free_vars = FiberusClosure.find_free_vars f in
      let closure_name = fresh_closure_name ctx in
      let impl_name = closure_name ^ "_impl" in
      let arg_count = List.length f.tf_args in
      
      (* Convert captured variables to (name, type) pairs *)
      let captures = List.map (fun v ->
        (ident v.v_name, tc_type_of v.v_type)
      ) free_vars in
      
      (* Convert the function body to C-AST with GCFrame tracking.
       * Closure bodies get their own GCFrame containing _closure, GC-typed
       * params, and GC-typed captures. The frame declaration, capture extraction,
       * and cleanup are included in cl_body so write_closure_impl just emits them. *)
      let ret_type = tc_type_of f.tf_type in
      let args = List.map (fun (v, _) ->
        { fa_name = ident v.v_name; fa_type = tc_type_of v.v_type }
      ) f.tf_args in
      let cl_captures_list = List.mapi (fun i (name, typ) ->
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
      } in
      let body_stmts = convert_stmt body_ctx f.tf_expr in
      let body_stmts = mark_volatile_for_try body_stmts in
      (* Build prologue: FIB_GC_CTX + GCFrame + capture extraction *)
      let prologue = ref [TCSGCCtx] in
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
      let closure_def = {
        cl_id = ctx.closure_counter - 1;  (* ID was incremented by fresh_closure_name *)
        cl_name = closure_name;
        cl_impl_name = impl_name;
        cl_args = args;
        cl_ret = ret_type;
        cl_captures = cl_captures_list;
        cl_body = full_body;
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
        mk_expr_pos (TCEAnonObject (fields, false)) TCFibDynamic pos
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
          (* Build compound literal: _stack_v = (ClassName){ ._obj.clazz = &ClassName_class, .f1 = a1, ... } *)
          let field_inits = match tc.cl_constructor with
            | Some cf ->
                (match cf.cf_expr with
                | Some { eexpr = TFunction f } ->
                    let filtered_args = filter_void_args f.tf_args in
                    let param_field_map = extract_param_field_mapping f in
                    let buf = Buffer.create 64 in
                    List.iter2 (fun (param_v, _) arg ->
                      let field_name = try List.assoc param_v.v_id param_field_map
                                       with Not_found -> param_v.v_name in
                      let carg = convert_expr ctx arg in
                      Buffer.add_string buf (Printf.sprintf ", .%s = %s" (ident field_name) (render_expr carg))
                    ) filtered_args args;
                    Buffer.contents buf
                | _ -> "")
            | None -> ""
          in
          let compound_lit = Printf.sprintf "_stack_%s = (%s){ ._obj.clazz = &%s_class%s }"
            name class_name class_name field_inits in
          mk_expr_pos (TCEComma [
            mk_expr (TCERaw compound_lit) result_type;
            mk_expr (TCELocal name) result_type
          ]) result_type pos
      | _ ->
          (* Fallback: regular assignment (shouldn't normally happen for stack-alloc vars) *)
          let e1_expr = convert_expr ctx e1 in
          let e2_expr = convert_expr ctx e2 in
          let assign = mk_expr_pos (TCEAssign (e1_expr, e2_expr)) e1_expr.ctype pos in
          { assign with
            pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts;
            gc_roots = e1_expr.gc_roots + e2_expr.gc_roots })
  
  (* Regular assignment with FibDynamic boxing if needed *)
  | OpAssign ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let rhs = box_if_needed e1_expr.ctype e2_expr in
      (* Propagate pending_stmts from both sides *)
      let assign = mk_expr_pos (TCEAssign (e1_expr, rhs)) e1_expr.ctype pos in
      { assign with 
        pending_stmts = e1_expr.pending_stmts @ rhs.pending_stmts @ assign.pending_stmts;
        gc_roots = e1_expr.gc_roots + rhs.gc_roots }
  
  (* Unsigned right shift assignment *)
  | OpAssignOp OpUShr ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let e1_ex = extract_fib_dynamic e1_expr TCInt32 in
      let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
      let unsigned = mk_expr (TCECast (TCUInt32, e1_ex)) TCUInt32 in
      let shifted = mk_expr (TCEBinop (TCOpShr, unsigned, e2_ex)) TCUInt32 in
      let result = mk_expr (TCECast (TCInt32, shifted)) TCInt32 in
      let final_result = 
        if e1_expr.ctype = TCFibDynamic then begin
          let boxed = mk_expr (TCECall (TCTFunc "fib_dynamic_int", [result])) TCFibDynamic in
          mk_expr_pos (TCEAssign (e1_expr, boxed)) TCFibDynamic pos
        end else
          mk_expr_pos (TCEAssign (e1_expr, result)) TCInt32 pos
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
  | OpAssignOp inner_op when (tc_type_of e1.Type.etype) = TCFibDynamic ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
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
  
  (* Regular compound assignment *)
  | OpAssignOp inner_op ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      let e2_ex = extract_fib_dynamic e2_expr e1_expr.ctype in
      let c_op = convert_binop inner_op in
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
        let sum = mk_expr (TCEBinop (c_op, save_ref, rhs_ref)) e1_expr.ctype in
        let assign = mk_expr_pos (TCEAssign (e1_expr, sum)) e1_expr.ctype pos in
        { assign with
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ e2_ex.pending_stmts @ [save_var; rhs_var] }
      end else begin
        let result = mk_expr_pos (TCEAssignOp (c_op, e1_expr, e2_ex)) e1_expr.ctype pos in
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
  
  (* FibDynamic null check: dyn == null -> fib_dynamic_is_null(dyn) *)
  | OpEq when is_null_compare ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let dyn_expr = if is_null_const e1 then e2_expr else e1_expr in
        let result = mk_expr_pos (TCECall (TCTFunc "fib_dynamic_is_null", [dyn_expr])) TCBool pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end else begin
        (* Regular null comparison *)
        let result = mk_expr_pos (TCEBinop (TCOpEq, e1_expr, e2_expr)) TCBool pos in
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end
  
  | OpNotEq when is_null_compare ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let dyn_expr = if is_null_const e1 then e2_expr else e1_expr in
        let is_null = mk_expr (TCECall (TCTFunc "fib_dynamic_is_null", [dyn_expr])) TCBool in
        let result = mk_expr_pos (TCEUnop (TCUNot, is_null)) TCBool pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end else begin
        let result = mk_expr_pos (TCEBinop (TCOpNeq, e1_expr, e2_expr)) TCBool pos in
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end
  
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
      let e1_ex = extract_fib_dynamic e1_expr TCInt32 in
      let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
      let unsigned = mk_expr_pos (TCECast (TCUInt32, e1_ex)) TCUInt32 pos in
      let shift = mk_expr_pos (TCEBinop (TCOpShr, unsigned, e2_ex)) TCUInt32 pos in
      let result = mk_expr_pos (TCECast (TCInt32, shift)) TCInt32 pos in
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
        let target_tc = if result_tc = TCFibDynamic then TCInt32 else result_tc in
        let e1_ex = extract_fib_dynamic e1_expr target_tc in
        let e2_ex = extract_fib_dynamic e2_expr target_tc in
        let c_op = convert_binop op in
        let result = mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) target_tc pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end else begin
        let c_op = convert_binop op in
        let result = mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) result_tc pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
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
        let result = mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCBool pos in
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
        let result = mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCBool pos in
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
  
  (* Bitwise operations - extract FibDynamic to int *)
  | (OpAnd | OpOr | OpXor | OpShl | OpShr) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let e1_ex = extract_fib_dynamic e1_expr TCInt32 in
        let e2_ex = extract_fib_dynamic e2_expr TCInt32 in
        let c_op = convert_binop op in
        let result = mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCInt32 pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end else begin
        let c_op = convert_binop op in
        let result = mk_expr_pos (TCEBinop (c_op, e1_expr, e2_expr)) result_tc pos in
        (* Propagate pending_stmts from both operands *)
        { result with 
          pending_stmts = e1_expr.pending_stmts @ e2_expr.pending_stmts @ result.pending_stmts;
          gc_roots = e1_expr.gc_roots + e2_expr.gc_roots }
      end
  
  (* Boolean operations - extract FibDynamic to bool *)
  | (OpBoolAnd | OpBoolOr) ->
      let e1_expr = convert_expr ctx e1 in
      let e2_expr = convert_expr ctx e2 in
      if e1_expr.ctype = TCFibDynamic || e2_expr.ctype = TCFibDynamic then begin
        let e1_ex = extract_fib_dynamic e1_expr TCBool in
        let e2_ex = extract_fib_dynamic e2_expr TCBool in
        let c_op = convert_binop op in
        let result = mk_expr_pos (TCEBinop (c_op, e1_ex, e2_ex)) TCBool pos in
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
      (* Convert the LHS field expression *)
      let lhs_expr = convert_expr ctx e1 in
      let rhs = box_if_needed lhs_tc val_expr in
      (* Check if write barrier needed - object pointers need barriers *)
      let needs_barrier = is_instance_field && needs_write_barrier_tc rhs_tc in
      if needs_barrier then begin
        (* Emit: (FIBRIX_WRITE_BARRIER(obj, value), obj->field = value) *)
        let barrier = mk_expr (TCECall (TCTMacro "FIBRIX_WRITE_BARRIER", [obj_expr; rhs])) TCVoid in
        let assign = mk_expr (TCEAssign (lhs_expr, rhs)) lhs_tc in
        let result = mk_expr_pos (TCEComma [barrier; assign]) lhs_tc pos in
        (* Propagate pending_stmts from all sub-expressions *)
        { result with 
          pending_stmts = obj_expr.pending_stmts @ lhs_expr.pending_stmts @ rhs.pending_stmts @ result.pending_stmts;
          gc_roots = obj_expr.gc_roots + lhs_expr.gc_roots + rhs.gc_roots }
      end else begin
        let result = mk_expr_pos (TCEAssign (lhs_expr, rhs)) lhs_tc pos in
        (* Propagate pending_stmts from sub-expressions *)
        { result with 
          pending_stmts = lhs_expr.pending_stmts @ rhs.pending_stmts @ result.pending_stmts;
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
      convert_tvar_stmt ctx v init_opt
  | TBlock exprs ->
      (* Nested block - flatten into statements *)
      List.concat_map (convert_expr_as_stmt ctx) exprs
  | TIf (cond, ethen, eelse_opt) ->
      let cond_expr = convert_expr ctx cond in
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
      ctx.loop_depth <- ctx.loop_depth + 1;
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
      ctx.loop_depth <- ctx.loop_depth - 1;
      let is_do_while = (flag = DoWhile) in
      [TCSWhile (cond_expr, body_with_pop, is_do_while)]
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
      (* Emit pending_stmts before throw to ensure temp variables are declared *)
      let pending_as_stmts = exc_expr.pending_stmts in
      pending_as_stmts @ [TCSThrow boxed_expr]
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
      (* Check if this is a static METHOD used as a value (not a call).
         The Haxe AST uses FStatic for both static var access and static method-as-value
         (unlike instance methods, which get FClosure). We detect method-as-value when
         the result type is a closure/function type. *)
      (match cf.cf_kind with
      | Method _ when result_tc = TCFibClosure || result_tc = TCFibDynamic ->
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
          let thunk = {
            mth_thunk_name = thunk_name;
            mth_dyn_thunk_name = dyn_thunk_name;
            mth_is_static = true;
            mth_class_name = class_name;
            mth_method_name = method_name;
            mth_args = arg_types;
            mth_ret_type = ret_type;
          } in
          Hashtbl.replace ctx.method_thunks thunk_name thunk;
          mk_expr_pos (TCEMethodClosure {
            mc_thunk_name = thunk_name;
            mc_dyn_thunk_name = dyn_thunk_name;
            mc_is_static = true;
            mc_arg_count = arg_count;
            mc_obj = None;
          }) TCFibClosure pos
      | _ ->
          (* Regular static field/variable access *)
          mk_expr_pos (TCEStatic (class_name, ident cf.cf_name)) result_tc pos)
  
  (* Instance field - special cases for Array.length and String.length *)
  | FInstance (c, _, cf) ->
      (* Array.length -> fib_*_array_length() *)
      if FiberusBuiltins.is_array_type obj.Type.etype && cf.cf_name = "length" then begin
        let arr_kind = get_array_kind obj.Type.etype in
        (* Wrap with GC-safe extraction if array is volatile *)
        wrap_single_gc_extraction_ctx (Some ctx) (fun safe_arr ->
          (* If object came from dynamic field, need to convert from FibDynamic first *)
          let arr_expr = 
            if is_dynamic_field_expr obj then
              mk_expr (TCECall (TCTFunc "fib_dynamic_to_array", [safe_arr])) (TCFibArray TCArrGeneric)
            else
              safe_arr
          in
          mk_expr_pos (TCEArrayLength (arr_expr, arr_kind)) TCInt32 pos
        ) obj_expr
      end
      (* String.length -> fib_string_length() *)
      else if FiberusBuiltins.is_string_type obj.Type.etype && cf.cf_name = "length" then begin
        (* Wrap with GC-safe extraction if string is volatile *)
        wrap_single_gc_extraction_ctx (Some ctx) (fun safe_str ->
          (* If object came from dynamic field, need to convert from FibDynamic first *)
          let str_expr = 
            if is_dynamic_field_expr obj then
              mk_expr (TCECall (TCTFunc "fib_dynamic_extract_string", [safe_str])) TCFibString
            else
              safe_str
          in
          mk_expr_pos (TCEStringLength str_expr) TCInt32 pos
        ) obj_expr
      end
      else begin
        (* Regular instance field access - use GC-safe extraction if obj is volatile.
         * This ensures that if obj came from an array element access or method call,
         * the intermediate pointer is rooted before we dereference it. *)
        let needs_cast = match obj.Type.etype with
          | Type.TInst (obj_class, _) -> obj_class.cl_path <> c.cl_path
          | _ -> false
        in
        wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
          if needs_cast then begin
            (* Cast to parent class type for inherited field access *)
            let class_name = flat_path c.cl_path in
            let cast_expr = mk_expr (TCECast (TCFibClass class_name, safe_obj)) (TCFibClass class_name) in
            mk_expr_pos (TCEArrow (cast_expr, ident cf.cf_name)) result_tc pos
          end else
            mk_expr_pos (TCEArrow (safe_obj, ident cf.cf_name)) result_tc pos
        ) obj_expr
      end
  
  (* Enum field *)
  | FEnum (e, ef) ->
      let enum_name = flat_path e.e_path in
      mk_expr_pos (TCEEnumConst (enum_name, ident ef.ef_name)) result_tc pos
  
  (* Anonymous/dynamic field access - always returns FibDynamic *)
  (* Wrap with GC-safe extraction since obj may be volatile *)
  | FAnon cf ->
      let field_name = mk_raw_string cf.cf_name in
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Access via fib_field_get returns FibDynamic, regardless of declared type *)
        mk_expr_pos (TCECall (TCTFunc "fib_field_get", [safe_obj; field_name])) TCFibDynamic pos
      ) obj_expr
  
  | FDynamic name ->
      let field_name = mk_raw_string name in
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        mk_expr_pos (TCECall (TCTFunc "fib_field_get", [safe_obj; field_name])) TCFibDynamic pos
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
      (* Register the thunk for later generation *)
      let thunk = {
        mth_thunk_name = thunk_name;
        mth_dyn_thunk_name = dyn_thunk_name;
        mth_is_static = is_static;
        mth_class_name = class_name;
        mth_method_name = method_name;
        mth_args = arg_types;
        mth_ret_type = ret_type;
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
      (* Instance method reference on dynamic object - just access the field *)
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        mk_expr_pos (TCEArrow (safe_obj, ident cf.cf_name)) result_tc pos
      ) obj_expr

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
      (* For specialized arrays, pop returns the element type (e.g., int32_t for FibIntArray),
         not the Haxe result_tc which may be Null<T>/Dynamic *)
      let elem_tc = element_type_of_array_kind arr_kind in
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "pop"), [arr_expr])) elem_tc pos in
      if is_specialized then call
      else mk_expr_pos (TCEUnbox (call, result_tc)) result_tc pos
  
  | "shift" ->
      (* For specialized arrays, shift returns the element type *)
      let elem_tc = element_type_of_array_kind arr_kind in
      let call = mk_expr_pos (TCECall (TCTFunc (prefix ^ "shift"), [arr_expr])) elem_tc pos in
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
      mk_expr_pos (TCECall (TCTFunc "fib_string_char_at_str", [str_expr; idx_expr])) TCFibString pos
  
  | "charCodeAt" ->
      let idx_expr = arg_or_int_default 0 0 in
      mk_expr_pos (TCECall (TCTFunc "fib_string_char_code_at", [str_expr; idx_expr])) TCInt32 pos
  
  | "substr" ->
      let start_expr = arg_or_int_default 0 0 in
      let len_expr = arg_or_int_default 1 (-1) in
      mk_expr_pos (TCECall (TCTFunc "fib_string_substr", [str_expr; start_expr; len_expr])) TCFibString pos
  
  | "substring" ->
      let start_expr = arg_or_int_default 0 0 in
      let end_expr = arg_or_int_default 1 (-1) in
      mk_expr_pos (TCECall (TCTFunc "fib_string_substring", [str_expr; start_expr; end_expr])) TCFibString pos
  
  | "indexOf" ->
      let needle_expr = arg_or_string_default 0 "" in
      let start_expr = arg_or_int_default 1 0 in
      (* Wrap with GC extraction to protect allocating string arguments *)
      wrap_call_with_gc_extraction_ctx (Some ctx)
        (fun args -> mk_expr_pos (TCECall (TCTFunc "fib_string_index_of", args)) TCInt32 pos)
        [str_expr; needle_expr; start_expr]
  
  | "lastIndexOf" ->
      let needle_expr = arg_or_string_default 0 "" in
      let start_expr = arg_or_int_default 1 (-1) in
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
      
      (* Convert captured variables to (name, type) pairs *)
      let captures = List.map (fun v ->
        (ident v.v_name, tc_type_of (Type.follow v.v_type))
      ) free_vars in
      
      (* Convert function body with fiber_spawn context and GCFrame tracking.
       * Same pattern as regular closures — build GCFrame in the conversion phase. *)
      let args = List.map (fun (v, _) ->
        { fa_name = ident v.v_name; fa_type = tc_type_of (Type.follow v.v_type) }
      ) f.tf_args in
      let ret_type = tc_type_of (Type.follow f.tf_type) in
      let cl_captures_list = List.mapi (fun i (name, typ) ->
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
    else if (arg_expr.ctype = TCInt32 || arg_expr.ctype = TCInt64) && (param_tc = TCFloat64 || param_tc = TCFloat32) then
      (* Numeric promotion: Int -> Float *)
      mk_expr (TCECast (param_tc, arg_expr)) param_tc
    else if (arg_expr.ctype = TCFloat64 || arg_expr.ctype = TCFloat32) && (param_tc = TCInt32 || param_tc = TCInt64) then
      (* Numeric truncation: Float -> Int *)
      mk_expr (TCECast (param_tc, arg_expr)) param_tc
    else
      arg_expr
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
  (* String.fromCharCode(code) -> fib_string_from_char_code(code) *)
  | TField (_, FStatic ({ cl_path = ([], "String") }, { cf_name = "fromCharCode" })) ->
      let coerced_args = coerce_args arg_exprs [TCInt32] in
      let args_pending = collect_pending coerced_args in
      let call = mk_expr_pos (TCECall (TCTFunc "fib_string_from_char_code", coerced_args)) result_tc pos in
      { call with pending_stmts = args_pending @ call.pending_stmts }

  (* Static method call *)
  | TField (_, FStatic (c, cf)) ->
      let class_name = flat_path c.cl_path in
      let method_name = ident cf.cf_name in
      let param_types = get_param_tc_types cf.cf_type in
      let coerced_args = coerce_args arg_exprs param_types in
      (* Collect pending_stmts from arguments *)
      let args_pending = collect_pending coerced_args in
      let call = mk_expr_pos (TCECall (TCTMethod (class_name, method_name), coerced_args)) result_tc pos in
      { call with pending_stmts = args_pending @ call.pending_stmts }
  
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
  
  (* Map method call (IntMap, StringMap, Int64Map, ObjectMap) - wrap with GC-safe extraction *)
  | TField (map, FInstance (_, _, cf)) when FiberusBuiltins.map_kind_of_type map.Type.etype <> None ->
      let map_expr = convert_expr ctx map in
      let kind = match FiberusBuiltins.map_kind_of_type map.Type.etype with Some k -> k | None -> FiberusBuiltins.MapInt in
      let value_type = get_map_value_type map.Type.etype kind in
      wrap_single_gc_extraction_ctx (Some ctx) (fun safe_map ->
        convert_map_call ctx safe_map args arg_exprs kind cf.cf_name value_type result_tc pos
      ) map_expr
  
  (* Instance method call *)
  | TField (obj, FInstance (c, _, cf)) ->
      let obj_expr = convert_expr ctx obj in
      let class_name = flat_path c.cl_path in
      let method_name = ident cf.cf_name in
      let param_types = get_param_tc_types cf.cf_type in
      let coerced_args = coerce_args arg_exprs param_types in
      let is_interface_call = FiberusVtable.is_interface c in
      (* Collect pending_stmts from arguments - these must be emitted before the call *)
      let args_pending = collect_pending coerced_args in
      
      (* Wrap the method call generation with GC-safe extraction of the object.
       * This ensures that if the object came from an array element access or
       * method call, it's rooted before we evaluate arguments or call the method. *)
      let call_result = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Check if this needs vtable dispatch *)
        match ctx.vtable_ctx with
        | Some vtctx ->
            if is_interface_call then begin
              (* Interface calls ALWAYS need vtable dispatch *)
              match FiberusVtable.get_interface_slot vtctx c cf with
              | Some slot ->
                  (* Interface calls use FibObject as this type since we don't know concrete class *)
                  mk_expr_pos (TCEVtableCall {
                    obj = safe_obj;
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
                    obj = safe_obj;
                    slot = slot_info.FiberusVtable.slot_index;
                    this_type = TCFibClass class_name;
                    ret_type = result_tc;
                    args = coerced_args;
                  }) result_tc pos
              | None ->
                  (* Direct call *)
                  mk_expr_pos (TCECall (TCTMethod (class_name, method_name), safe_obj :: coerced_args)) result_tc pos
            end
        | None ->
            (* No vtable context - direct call *)
            mk_expr_pos (TCECall (TCTMethod (class_name, method_name), safe_obj :: coerced_args)) result_tc pos
      ) obj_expr in
      (* Prepend arguments' pending_stmts to ensure temp vars are declared before call *)
      { call_result with pending_stmts = args_pending @ call_result.pending_stmts }
  
  (* Constructor call - TNew handles this, but might appear as call too *)
  | TField (_, FEnum (e, ef)) ->
      let enum_name = flat_path e.e_path in
      let constr_name = ident ef.ef_name in
      (* Collect pending_stmts from arguments *)
      let args_pending = collect_pending arg_exprs in
      let call = mk_expr_pos (TCEEnumConstruct (enum_name, constr_name, arg_exprs)) (TCFibEnum enum_name) pos in
      { call with pending_stmts = args_pending @ call.pending_stmts }
  
  (* Dynamic/anonymous field call - wrap with GC-safe extraction *)
  | TField (obj, FAnon cf) ->
      let obj_expr = convert_expr ctx obj in
      let field_name = mk_raw_string cf.cf_name in
      (* Collect pending_stmts from arguments *)
      let args_pending = collect_pending arg_exprs in
      let boxed_args = box_args_for_dynamic_call arg_exprs in
      let call_result = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        (* Get closure from dynamic field, then call it *)
        let closure = mk_expr (TCECall (TCTFunc "fib_dynamic_get_field", [safe_obj; field_name])) TCFibClosure in
        let dyn_call = mk_expr_pos (TCEDynamicCall { closure; args = boxed_args }) TCFibDynamic pos in
        unwrap_dynamic_result dyn_call result_tc
      ) obj_expr in
      { call_result with pending_stmts = args_pending @ call_result.pending_stmts }
  
  | TField (obj, FDynamic name) ->
      let obj_expr = convert_expr ctx obj in
      let field_name = mk_raw_string name in
      (* Collect pending_stmts from arguments *)
      let args_pending = collect_pending arg_exprs in
      let boxed_args = box_args_for_dynamic_call arg_exprs in
      let call_result = wrap_single_gc_extraction_ctx (Some ctx) (fun safe_obj ->
        let closure = mk_expr (TCECall (TCTFunc "fib_dynamic_get_field", [safe_obj; field_name])) TCFibClosure in
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
              (* Get parent constructor parameter types *)
              let param_types = match parent_c.cl_constructor with
                | Some cf -> get_param_tc_types cf.cf_type
                | None -> []
              in
              let coerced_args = coerce_args arg_exprs param_types in
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
          (* Get formal parameter types from callee's Haxe type for correct fn pointer cast.
             This is critical for optional params: ?Int has formal type Null<Int> -> TCFibDynamic
             in the closure impl, but the actual arg may be TCInt32. Using formal types ensures
             the function pointer cast matches the closure's actual C signature. *)
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
  let vtype = tc_type_of v.v_type in
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
            (* Coerce arguments to parameter types *)
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
          (* No initializer - just declare the variable *)
          let var_stmt = TCSVar { vd_name = name; vd_type = vtype; vd_init = None; vd_static = false; vd_const = false; vd_volatile = false } in
          let gc_stmts = gc_push_if_needed ctx name vtype in
          var_stmt :: gc_stmts
      | Some init_e ->
          (* Convert the initializer expression *)
          let cexpr = convert_expr ctx init_e in
          (* Coerce to variable type if needed *)
          let coerced = coerce_to_type cexpr vtype in
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
      ctx.loop_depth <- ctx.loop_depth + 1;
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
      ctx.loop_depth <- ctx.loop_depth - 1;
      let is_do_while = (flag = DoWhile) in
      [TCSWhile (cond_expr, body_with_pop, is_do_while)]
  
  (* Return statement - with GC root cleanup when inside a converted function. *)
  | TReturn expr_opt ->
      if ctx.in_gc_frame then begin
        (* GCFrame path: pop any legacy temp roots (from stack-alloc field tracking),
         * then emit GC_FRAME_POP before return. *)
        let has_frame_slots = ctx.gc_frame_slots <> [] in
        let temp_root_pop = if ctx.gc_local_count > 0 then [TCSGCPop ctx.gc_local_count] else [] in
        let frame_pop = if has_frame_slots then [TCSGCFramePop ctx.gc_frame_name] else [] in
        let cleanup = temp_root_pop @ frame_pop in
        let needs_cleanup = cleanup <> [] in
        match expr_opt with
        | None ->
            cleanup @ [TCSReturn None]
        | Some inner ->
            let inner_expr = convert_expr ctx inner in
            let cexpr = match ctx.current_ret_type with
              | Some ret_tc -> coerce_to_type inner_expr ret_tc
              | None -> inner_expr
            in
            let has_pending = cexpr.pending_stmts <> [] in
            if not needs_cleanup && not has_pending then
              [TCSReturn (Some cexpr)]
            else if not has_pending then begin
              (* Simple: evaluate, cleanup, return.
               * For non-void returns with GC types, save to temp first because
               * the return value might be a frame slot reference that becomes invalid
               * after frame pop. *)
              let ret_type = cexpr.ctype in
              if needs_gc_root_tc ret_type then begin
                let stmts = ref [] in
                stmts := !stmts @ [TCSVar {
                  vd_name = "__ret"; vd_type = ret_type;
                  vd_init = Some cexpr;
                  vd_static = false; vd_const = false; vd_volatile = false }];
                stmts := !stmts @ cleanup;
                stmts := !stmts @ [TCSReturn (Some (mk_expr (TCELocal "__ret") ret_type))];
                [TCSBlock !stmts]
              end else begin
                cleanup @ [TCSReturn (Some cexpr)]
              end
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
        (* Legacy path — function prologue handled by gen_function in genfiberus.ml *)
        let ret_expr = match expr_opt with
          | None -> None
          | Some inner ->
              let inner_expr = convert_expr ctx inner in
              match ctx.current_ret_type with
              | Some ret_tc -> Some (coerce_to_type inner_expr ret_tc)
              | None -> Some inner_expr
        in
        [TCSReturn ret_expr]
      end else begin
        (* Legacy C-AST function path — we own the GC cleanup *)
        let total_to_pop = ctx.gc_local_count in
        match expr_opt with
        | None ->
            if total_to_pop > 0 then
              [TCSGCPop total_to_pop; TCSReturn None]
            else
              [TCSReturn None]
        | Some inner ->
            let inner_expr = convert_expr ctx inner in
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
            if is_simple && all_to_pop = 0 && not has_pending then
              [TCSReturn (Some cexpr)]
            else if is_simple && expr_gc_roots = 0 && not has_pending then begin
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
              if all_to_pop > 0 then
                stmts := !stmts @ [TCSGCPop all_to_pop];
              stmts := !stmts @ [TCSReturn (Some (mk_expr (TCELocal "__ret") ret_type))];
              [TCSBlock !stmts]
            end
      end
  
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
      (* Emit pending_stmts before throw to ensure temp variables are declared *)
      let pending_as_stmts = exc_expr.pending_stmts in
      pending_as_stmts @ [TCSThrow boxed_expr]
  
  (* Try/catch *)
  | TTry (body, catches) ->
      let body_stmts = convert_stmt ctx body in
      let catch_blocks = List.map (fun (v, catch_body) ->
        let ct = tc_type_of v.v_type in
        let ck = match ct with
          | TCFibDynamic -> TCCatchDynamic
          | TCInt32 -> TCCatchInt
          | TCFloat64 -> TCCatchFloat
          | TCBool -> TCCatchBool
          | TCFibString -> TCCatchString
          | TCFibClass name -> TCCatchObject name
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
        (* Integer/enum switch - use C switch *)
        let cond_expr = convert_expr ctx sw.switch_subject in
        let case_blocks = List.map (fun case ->
          let value_exprs = List.map (convert_expr ctx) case.case_patterns in
          let body_stmts = convert_stmt ctx case.case_expr in
          (value_exprs, body_stmts)
        ) sw.switch_cases in
        let default_stmts = Option.map (convert_stmt ctx) sw.switch_default in
        [TCSSwitch { sw_expr = cond_expr; sw_cases = case_blocks; sw_default = default_stmts }]
      end
  
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
  let func_name = Printf.sprintf "%s_%s" class_name name in
  (* Run escape analysis *)
  let escape_result = analyze_function func in
  (* Set up GCFrame-based body context.
   * We register param slots upfront, then the body conversion adds more slots
   * as it encounters GC-typed locals and expression temps.
   * After body conversion, we know ALL slots and prepend the frame declaration. *)
  let frame_name = "_gc" in
  let frame_rooted_vars = Hashtbl.create 16 in
  let param_inits = ref [] in
  (* Collect GC-typed parameters as initial frame slots *)
  let initial_slots = ref [] in
  List.iter (fun (v, _) ->
    let tc = tc_type_of v.v_type in
    let vname = ident v.v_name in
    if needs_gc_root tc then begin
      initial_slots := (vname, tc) :: !initial_slots;
      Hashtbl.replace frame_rooted_vars vname ();
      param_inits := (vname, mk_expr (TCELocal vname) tc) :: !param_inits
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
  (* Propagate closures and counters back to caller's context *)
  ctx.closures <- body_ctx.closures @ ctx.closures;
  ctx.closure_counter <- body_ctx.closure_counter;
  ctx.spawn_counter <- body_ctx.spawn_counter;
  (* Build prologue: FIB_GC_CTX + GCFrame declaration *)
  let prologue = ref [] in
  prologue := [TCSGCCtx];
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

(* Check if constructor body needs GC context (allocations or GC pointer locals) *)
let rec ctor_needs_gc_context (e : texpr) =
  match e.eexpr with
  | TNew _ -> true
  | TCall ({ eexpr = TField (_, FStatic (_, cf)) }, _) when cf.cf_name = "new" -> true
  | TVar (v, _) when needs_gc_root (tc_type_of v.v_type) -> true
  | _ ->
      let found = ref false in
      Type.iter (fun e -> if ctor_needs_gc_context e then found := true) e;
      !found

(* Convert a Haxe constructor to two C-AST function definitions:
   1. ClassName_init(this, args) — initializes fields on existing object
   2. ClassName_new(args) — allocates and calls _init
   Returns None for empty constructors or simple constructors (handled in header).
   This replaces gen_constructor in genfiberus.ml. *)
let convert_constructor ctx (c : tclass) =
  let class_name = match ctx.current_class_name with
    | Some n -> n | None -> flat_path c.cl_path in
  match c.cl_constructor with
  | None -> None
  | Some cf ->
      (match cf.cf_expr with
      | Some { eexpr = TFunction func } ->
          if FiberusGenClass.is_simple_constructor func then
            None  (* Simple constructors generated inline in header *)
          else begin
            let filtered_args = filter_void_args func.tf_args in
            let tc_args = List.map (fun (v, _) ->
              { fa_name = ident v.v_name; fa_type = tc_type_of v.v_type }
            ) filtered_args in
            let escape_result = analyze_function func in
            let init_needs_gc_ctx = ctor_needs_gc_context func.tf_expr in
            (* === _init function (GCFrame-based) === *)
            let frame_name = "_gc" in
            let frame_rooted_vars = Hashtbl.create 16 in
            let param_inits = ref [] in
            let initial_slots = ref [] in
            if init_needs_gc_ctx then begin
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
              param_inits := ("this", mk_expr (TCELocal "this") this_tc) :: !param_inits
            end;
            let init_body_ctx = {
              ctx with
              current_ret_type = None;
              gc_local_count = 0;
              func_gc_root_count = 0;
              gc_frame_name = frame_name;
              gc_frame_slots = List.rev !initial_slots;
              gc_frame_rooted_vars = frame_rooted_vars;
              in_gc_frame = init_needs_gc_ctx;
              fiber_mature_vars = escape_result.fiber_mature_vars;
              stack_alloc_vars = escape_result.stack_allocatable;
              last_line = 0;  (* Reset for fresh FIBLINE dedup per function *)
              has_stack_frame = false;  (* _init has no FIB_STACKFRAME *)
            } in
            let init_body_stmts = convert_stmt init_body_ctx func.tf_expr in
            let init_body_stmts = mark_volatile_for_try init_body_stmts in
            ctx.closures <- init_body_ctx.closures @ ctx.closures;
            ctx.closure_counter <- init_body_ctx.closure_counter;
            ctx.spawn_counter <- init_body_ctx.spawn_counter;
            let init_prologue = ref [] in
            let init_epilogue = ref [] in
            if init_needs_gc_ctx then begin
              init_prologue := [TCSGCCtx];
              let frame_info = gc_frame_build_info_with_inits init_body_ctx !param_inits in
              let has_gc_slots = frame_info.gfi_slots <> [] in
              if has_gc_slots then
                init_prologue := !init_prologue @ [TCSGCFrameDecl frame_info];
              (* Pop any legacy temp roots (from stack-alloc fields) + frame pop *)
              if init_body_ctx.gc_local_count > 0 then
                init_epilogue := [TCSGCPop init_body_ctx.gc_local_count];
              if has_gc_slots then
                init_epilogue := !init_epilogue @ [TCSGCFramePop frame_name]
            end;
            let init_func = {
              fd_name = Printf.sprintf "%s_init" class_name;
              fd_ret = TCVoid;
              fd_args = { fa_name = "this"; fa_type = TCFibClass class_name } :: tc_args;
              fd_body = !init_prologue @ init_body_stmts @ !init_epilogue;
              fd_static = false;
              fd_inline = false;
              fd_attrs = [];
            } in
            (* === _new function (GCFrame-based) === *)
            let gc_param_args = List.filter (fun (v, _) ->
              needs_gc_root (tc_type_of v.v_type)
            ) filtered_args in
            let has_gc_params = gc_param_args <> [] in
            (* Allocate 'this' — mature or nursery depending on fiber capture analysis *)
            let alloc_func = if escape_result.this_needs_mature then
              "gc_alloc_mature_object_with_class"
            else
              "gc_alloc_object_with_class"
            in
            let alloc_stmt = TCSVar {
              vd_name = "this"; vd_type = TCFibClass class_name;
              vd_init = Some (mk_expr (TCERaw (Printf.sprintf "%s(sizeof(%s), &%s_class)"
                alloc_func class_name class_name)) (TCFibClass class_name));
              vd_static = false; vd_const = false; vd_volatile = false;
            } in
            let arg_names = List.map (fun (v, _) ->
              let tc = tc_type_of v.v_type in
              let vname = ident v.v_name in
              if has_gc_params && needs_gc_root tc then
                mk_expr (TCEDot (mk_expr (TCELocal "_gc") TCVoid, vname)) tc
              else
                mk_expr (TCELocal vname) tc
            ) filtered_args in
            let init_call = TCSExpr (mk_expr (TCECall (
              TCTFunc (Printf.sprintf "%s_init" class_name),
              mk_expr (TCELocal "this") (TCFibClass class_name) :: arg_names
            )) TCVoid) in
            let new_prologue = ref [] in
            let new_epilogue = ref [] in
            if has_gc_params then begin
              (* _new function uses a small GCFrame to protect params during alloc *)
              new_prologue := [TCSGCCtx];
              let new_frame_rooted = Hashtbl.create 8 in
              let new_frame_slots = ref [] in
              let new_param_inits = ref [] in
              List.iter (fun (v, _) ->
                let tc = tc_type_of v.v_type in
                let vname = ident v.v_name in
                new_frame_slots := (vname, tc) :: !new_frame_slots;
                Hashtbl.replace new_frame_rooted vname ();
                new_param_inits := (vname, mk_expr (TCELocal vname) tc) :: !new_param_inits
              ) gc_param_args;
              let new_frame_info = {
                gfi_name = "_gc";
                gfi_slots = List.rev_map (fun (name, typ) ->
                  let init = try Some (List.assoc name !new_param_inits) with Not_found -> None in
                  { gfs_name = name; gfs_type = typ; gfs_init = init }
                ) !new_frame_slots;
              } in
              new_prologue := !new_prologue @ [TCSGCFrameDecl new_frame_info];
              new_epilogue := [TCSGCFramePop "_gc"]
            end;
            let return_this = TCSReturn (Some (mk_expr (TCELocal "this") (TCFibClass class_name))) in
            let new_func = {
              fd_name = Printf.sprintf "%s_new" class_name;
              fd_ret = TCFibClass class_name;
              fd_args = (if tc_args = [] then [] else tc_args);
              fd_body = !new_prologue @ [alloc_stmt; init_call] @ !new_epilogue @ [return_this];
              fd_static = false;
              fd_inline = false;
              fd_attrs = [];
            } in
            Some (init_func, new_func)
          end
      | _ -> None)
