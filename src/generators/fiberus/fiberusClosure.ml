(*
 * FiberusClosure - Closure analysis and representation
 *
 * This module handles closure analysis including:
 * - Finding free variables (captured variables) in closures
 * - Representing closure metadata
 * - Pre-scanning for nested closures
 *
 * Code generation for closures is handled by the main generator,
 * but this module provides the analysis infrastructure.
 *)

open Type

(* ============================================================================
 * Closure Representation
 * ============================================================================ *)

(* Information about a closure *)
type closure_info = {
  cl_name: string;                    (* Closure name, e.g., "_closure_42" *)
  cl_impl_name: string;               (* Implementation function name, e.g., "_closure_42_impl" *)
  cl_func: tfunc;                     (* The function definition *)
  cl_captured: tvar list;             (* Captured variables from outer scope *)
  cl_is_fiber_spawn: bool;            (* True if this is a Fiber.spawn closure *)
}

(* Closure collection context for pre-scanning *)
type closure_context = {
  mutable counter: int;               (* Counter for generating unique names *)
  mutable closures: closure_info list; (* Collected closures *)
  mutable in_impl_phase: bool;        (* True during implementation generation *)
}

(* ============================================================================
 * Free Variable Analysis
 * ============================================================================ *)

(* Find free variables in a function (variables used but not defined locally).
   These are the variables that need to be captured by the closure. *)
let find_free_vars (f : tfunc) : tvar list =
  (* Variables defined as function parameters *)
  let bound = Hashtbl.create 16 in
  List.iter (fun (v, _) -> Hashtbl.add bound v.v_id ()) f.tf_args;
  (* Track locally defined variables *)
  let local = Hashtbl.create 16 in
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
          Hashtbl.add local v.v_id ();
          scan catch_e;
          Hashtbl.remove local v.v_id
        ) catches
    | TFunction inner_f ->
        (* Scan nested function bodies too - we need to capture any variables
           they use from our scope so we can pass them to the inner closure *)
        let inner_bound = Hashtbl.create 16 in
        List.iter (fun (v, _) -> Hashtbl.add inner_bound v.v_id ()) inner_f.tf_args;
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
              scan_inner try_e;
              List.iter (fun (v, catch_e) ->
                Hashtbl.add inner_bound v.v_id ();
                scan_inner catch_e;
                Hashtbl.remove inner_bound v.v_id
              ) catches
          | TFunction f2 ->
              (* Recurse into deeper nested functions *)
              List.iter (fun (v, _) -> Hashtbl.add inner_bound v.v_id ()) f2.tf_args;
              Type.iter scan_inner f2.tf_expr
          | _ ->
              Type.iter scan_inner e
        in
        scan_inner inner_f.tf_expr
    | _ ->
        Type.iter scan e
  in
  scan f.tf_expr;
  !free

(* Check if a function body uses TConst TThis *)
let uses_this (f : tfunc) : bool =
  let found = ref false in
  let rec scan e =
    if not !found then
      match e.eexpr with
      | TConst TThis -> found := true
      | _ -> Type.iter scan e
  in
  scan f.tf_expr;
  !found

(* ============================================================================
 * Closure Context Management
 * ============================================================================ *)

(* Create a new closure context *)
let create_context () : closure_context = {
  counter = 0;
  closures = [];
  in_impl_phase = false;
}

(* Generate a unique closure name and increment counter *)
let next_closure_name (ctx : closure_context) : string * string =
  let name = Printf.sprintf "_closure_%d" ctx.counter in
  let impl_name = name ^ "_impl" in
  ctx.counter <- ctx.counter + 1;
  (name, impl_name)

(* Register a closure for later generation *)
let register_closure (ctx : closure_context) (f : tfunc) ~is_fiber_spawn : closure_info =
  let (name, impl_name) = next_closure_name ctx in
  let captured = find_free_vars f in
  let info = {
    cl_name = name;
    cl_impl_name = impl_name;
    cl_func = f;
    cl_captured = captured;
    cl_is_fiber_spawn = is_fiber_spawn;
  } in
  if not ctx.in_impl_phase then
    ctx.closures <- info :: ctx.closures;
  info

(* ============================================================================
 * Nested Closure Pre-Scanning
 * ============================================================================ *)

(* Scan an expression tree to find all nested closures.
   This is done before code generation to ensure all closures
   are forward-declared before they're used. *)
let prescan_closures (ctx : closure_context) (e : texpr) : unit =
  let rec scan expr =
    match expr.eexpr with
    | TFunction f ->
        (* Found a closure - register it and scan its body for more *)
        let _info = register_closure ctx f ~is_fiber_spawn:false in
        scan f.tf_expr
    | TCall ({ eexpr = TField (_, FStatic ({ cl_path = (["fiberus"], "Fiber") }, { cf_name = "spawn" })) }, [arg])
    | TCall ({ eexpr = TField (_, FStatic ({ cl_path = (["fiberus"], "Fiber") }, { cf_name = "spawnOn" })) }, [_; arg])
    | TCall ({ eexpr = TField (_, FStatic ({ cl_path = (["fiberus"], "Fiber") }, { cf_name = "spawnAny" })) }, [arg]) ->
        (* Fiber.spawn with closure argument *)
        (match arg.eexpr with
        | TFunction f ->
            let _info = register_closure ctx f ~is_fiber_spawn:true in
            scan f.tf_expr
        | _ -> Type.iter scan expr)
    | _ ->
        Type.iter scan expr
  in
  scan e

(* Get all collected closures in definition order *)
let get_closures (ctx : closure_context) : closure_info list =
  List.rev ctx.closures

(* Clear collected closures *)
let clear_closures (ctx : closure_context) : unit =
  ctx.closures <- []

(* Save and restore counter for nested closure handling *)
let save_counter (ctx : closure_context) : int =
  ctx.counter

let restore_counter (ctx : closure_context) (saved : int) : unit =
  ctx.counter <- saved

(* ============================================================================
 * Capture Type Utilities
 * ============================================================================ *)

(* Determine how a captured variable should be stored in FibDynamic.
   Returns the field name in FibDynamic.data union. *)
let capture_storage_field (v : tvar) : string =
  match follow v.v_type with
  | TAbstract ({ a_path = ([], "Int") }, []) -> "intVal"
  | TAbstract ({ a_path = ([], "Float") }, []) -> "floatVal"
  | TAbstract ({ a_path = ([], "Bool") }, []) -> "boolVal"
  | TInst ({ cl_path = ([], "String") }, []) -> "stringVal"
  | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "int64Val"
  | _ -> "ptrVal"

(* Determine if a captured variable type needs casting when retrieved *)
let capture_needs_cast (v : tvar) : bool =
  match follow v.v_type with
  | TAbstract ({ a_path = ([], "Int") }, []) -> false
  | TAbstract ({ a_path = ([], "Float") }, []) -> false
  | TAbstract ({ a_path = ([], "Bool") }, []) -> false
  | TInst ({ cl_path = ([], "String") }, []) -> false
  | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> false
  | _ -> true

(* ============================================================================
 * Dynamic Conversion Utilities
 * ============================================================================ *)

(* Get the function to convert a type TO FibDynamic for boxing *)
let box_to_dynamic_func (t : Type.t) : string =
  match follow t with
  | TAbstract ({ a_path = ([], "Int") }, []) -> "fib_dynamic_int"
  | TAbstract ({ a_path = ([], "Float") }, []) -> "fib_dynamic_float"
  | TAbstract ({ a_path = ([], "Bool") }, []) -> "fib_dynamic_bool"
  | TInst ({ cl_path = ([], "String") }, []) -> "fib_dynamic_string"
  | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "fib_dynamic_int64"
  | TInst ({ cl_path = ([], "Array") }, _) -> "fib_dynamic_array"
  | TFun _ -> "fib_dynamic_object"  (* Closures are objects *)
  | TDynamic _ -> ""  (* Already dynamic, no conversion needed *)
  | _ -> "fib_dynamic_object"

(* Get the function to convert FROM FibDynamic for unboxing *)
let unbox_from_dynamic_func (t : Type.t) : string =
  match follow t with
  | TAbstract ({ a_path = ([], "Int") }, []) -> "fib_dynamic_to_int"
  | TAbstract ({ a_path = ([], "Float") }, []) -> "fib_dynamic_to_float"
  | TAbstract ({ a_path = ([], "Bool") }, []) -> "fib_dynamic_to_bool"
  | TInst ({ cl_path = ([], "String") }, []) -> "fib_dynamic_to_string"
  | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "fib_dynamic_to_int64"
  | TInst ({ cl_path = ([], "Array") }, _) -> "fib_dynamic_to_array"
  | TFun _ -> "fib_dynamic_to_object"  (* Returns FibObject*, needs cast to FibClosure* *)
  | TDynamic _ -> ""  (* No conversion needed *)
  | _ -> "fib_dynamic_to_object"

(* Check if return type needs casting after unboxing *)
let unbox_needs_cast (t : Type.t) : bool =
  match follow t with
  | TAbstract ({ a_path = ([], "Int") }, []) -> false
  | TAbstract ({ a_path = ([], "Float") }, []) -> false
  | TAbstract ({ a_path = ([], "Bool") }, []) -> false
  | TInst ({ cl_path = ([], "String") }, []) -> false
  | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> false
  | TDynamic _ -> false
  | _ -> true  (* Object/array types need cast *)
