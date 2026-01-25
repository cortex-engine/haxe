(*
 * FiberusContext - Generator context and state management
 *
 * This module defines the generator context that carries state through
 * the code generation process. It tracks:
 * - Class ID assignment
 * - Vtable information
 * - Current generation state (class, function, etc.)
 * - GC root tracking
 * - Closure generation
 *)

open Globals
open FiberusAst

(* Method thunk information for methods used as values *)
type method_thunk = {
  mt_is_static: bool;
  mt_class_path: path;
  mt_method_name: string;
  mt_arg_types: (string * Type.t) list;
  mt_ret_type: Type.t;
}

(* Generator context *)
type ctx = {
  (* Compiler context *)
  com: Gctx.t;
  
  (* Debug level: 0=none, 1=trace, 2=line *)
  debug_level: int;
  
  (* Class management *)
  mutable class_id_counter: int;
  class_ids: (path, int) Hashtbl.t;
  mutable vtable_ctx: FiberusVtable.vtable_context option;
  
  (* Current generation state *)
  mutable current_class: Type.tclass option;
  mutable current_func: string option;
  mutable current_ret_type: Type.t option;
  
  (* GC root tracking *)
  mutable gc_root_count: int;
  mutable has_gc_ctx: bool;
  
  (* Loop tracking for yield point insertion *)
  mutable loop_depth: int;
  
  (* Closure generation *)
  mutable closure_counter: int;
  mutable closures: tc_closure list;
  mutable in_closure_impl: bool;
  mutable in_fiber_spawn: bool;
  
  (* Escape analysis results *)
  mutable stack_alloc_vars: (int, Type.tclass) Hashtbl.t;
  
  (* Method thunks for methods used as values *)
  method_thunks: (string, method_thunk) Hashtbl.t;
  
  (* Local variable types for tracking *)
  local_types: (int, string) Hashtbl.t;
  
  (* Temp variable counter *)
  mutable temp_counter: int;
  
  (* Last emitted line for debug tracking *)
  mutable last_line: int;
}

(* Create a new generator context *)
let create com =
  (* Determine debug level:
     0 = no stack tracking
     1 = function-level stack trace (FIBERUS_STACK_TRACE)
     2 = line-level tracking (FIBERUS_STACK_LINE) *)
  let tracy_enabled = Gctx.raw_defined com "FIBERUS_TRACY" in
  let debug_level =
    if Gctx.defined com Define.Debug then 2
    else if com.debug then 1
    else if tracy_enabled then 1
    else 0
  in
  {
    com = com;
    debug_level = debug_level;
    class_id_counter = 100;  (* Reserve 0-99 for built-in classes *)
    class_ids = Hashtbl.create 64;
    vtable_ctx = None;
    current_class = None;
    current_func = None;
    current_ret_type = None;
    gc_root_count = 0;
    has_gc_ctx = false;
    loop_depth = 0;
    closure_counter = 0;
    closures = [];
    in_closure_impl = false;
    in_fiber_spawn = false;
    stack_alloc_vars = Hashtbl.create 16;
    method_thunks = Hashtbl.create 16;
    local_types = Hashtbl.create 32;
    temp_counter = 0;
    last_line = 0;
  }

(* Get or assign a unique class ID *)
let get_class_id ctx path =
  try Hashtbl.find ctx.class_ids path
  with Not_found ->
    let id = ctx.class_id_counter in
    ctx.class_id_counter <- ctx.class_id_counter + 1;
    Hashtbl.add ctx.class_ids path id;
    id

(* Generate a fresh temporary variable name *)
let fresh_temp ctx =
  ctx.temp_counter <- ctx.temp_counter + 1;
  "_hx_tmp" ^ string_of_int ctx.temp_counter

(* Generate a fresh closure name *)
let fresh_closure_name ctx =
  let id = ctx.closure_counter in
  ctx.closure_counter <- ctx.closure_counter + 1;
  "_closure_" ^ string_of_int id

(* Execute a function within a function context *)
let with_function ctx func_name ret_type f =
  let old_func = ctx.current_func in
  let old_ret = ctx.current_ret_type in
  let old_gc_count = ctx.gc_root_count in
  let old_has_gc = ctx.has_gc_ctx in
  let old_loop = ctx.loop_depth in
  let old_line = ctx.last_line in
  
  ctx.current_func <- Some func_name;
  ctx.current_ret_type <- Some ret_type;
  ctx.gc_root_count <- 0;
  ctx.has_gc_ctx <- false;
  ctx.loop_depth <- 0;
  ctx.last_line <- 0;
  
  let result = f () in
  
  ctx.current_func <- old_func;
  ctx.current_ret_type <- old_ret;
  ctx.gc_root_count <- old_gc_count;
  ctx.has_gc_ctx <- old_has_gc;
  ctx.loop_depth <- old_loop;
  ctx.last_line <- old_line;
  
  result

(* Execute a function within a class context *)
let with_class ctx c f =
  let old_class = ctx.current_class in
  let old_closures = ctx.closures in
  let old_closure_counter = ctx.closure_counter in
  let old_stack_vars = ctx.stack_alloc_vars in
  
  ctx.current_class <- Some c;
  ctx.closures <- [];
  ctx.stack_alloc_vars <- Hashtbl.create 16;
  
  let result = f () in
  
  let closures = ctx.closures in
  ctx.current_class <- old_class;
  ctx.closures <- old_closures;
  ctx.closure_counter <- old_closure_counter;
  ctx.stack_alloc_vars <- old_stack_vars;
  
  (result, closures)

(* Execute a function within a loop context *)
let with_loop ctx f =
  ctx.loop_depth <- ctx.loop_depth + 1;
  let result = f () in
  ctx.loop_depth <- ctx.loop_depth - 1;
  result

(* Check if we're in a loop (for yield point insertion) *)
let in_loop ctx =
  ctx.loop_depth > 0

(* Push a GC root *)
let push_gc_root ctx =
  ctx.gc_root_count <- ctx.gc_root_count + 1

(* Pop GC roots and return how many were popped *)
let pop_gc_roots ctx count =
  ctx.gc_root_count <- ctx.gc_root_count - count

(* Get current GC root count *)
let gc_root_count ctx =
  ctx.gc_root_count

(* Register a closure *)
let register_closure ctx closure =
  ctx.closures <- closure :: ctx.closures

(* Get all registered closures *)
let get_closures ctx =
  List.rev ctx.closures

(* Register a method thunk *)
let register_method_thunk ctx name thunk =
  Hashtbl.replace ctx.method_thunks name thunk

(* Get all method thunks *)
let get_method_thunks ctx =
  Hashtbl.fold (fun name thunk acc -> (name, thunk) :: acc) ctx.method_thunks []

(* Check if a variable should be stack-allocated *)
let is_stack_allocated ctx var_id =
  Hashtbl.mem ctx.stack_alloc_vars var_id

(* Get stack-allocated class for a variable *)
let get_stack_alloc_class ctx var_id =
  Hashtbl.find_opt ctx.stack_alloc_vars var_id

(* Set escape analysis results *)
let set_stack_alloc_vars ctx vars =
  ctx.stack_alloc_vars <- vars

(* Clear local type tracking for a new function *)
let clear_local_types ctx =
  Hashtbl.clear ctx.local_types

(* Record a local variable's C type *)
let record_local_type ctx var_id c_type =
  Hashtbl.replace ctx.local_types var_id c_type

(* Get a local variable's recorded C type *)
let get_local_type ctx var_id =
  Hashtbl.find_opt ctx.local_types var_id
