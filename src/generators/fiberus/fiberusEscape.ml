(*
 * FiberusEscape - Escape analysis for stack allocation optimization
 *
 * Determines which local variables holding newly allocated objects can be
 * stack-allocated instead of heap-allocated. A variable can be stack-allocated if:
 * 1. It's assigned directly from a TNew expression
 * 2. It has no super-class
 * 3. The object never "escapes" - i.e., it's never:
 *    - Stored in a field of another object
 *    - Stored in an array
 *    - Passed to a function call (except for field access on 'this')
 *    - Returned from the function
 *    - Captured by a closure
 *    - Thrown as an exception
 *
 * Stack-allocated objects:
 * - Don't need gc_alloc (allocated on C stack)
 * - Don't need gc_push_temp_root (stack is scanned conservatively)
 * - Are automatically freed when the function returns
 *)

open Ast
open Type

(* Check if a class is suitable for stack allocation (simple value-like class) *)
let can_stack_alloc_class (c : tclass) : bool =
  (* Must not have a custom destructor/mark function that needs special handling *)
  not (has_class_flag c CExtern) &&
  (* Must not be an interface *)
  not (has_class_flag c CInterface) &&
  (* Must not extend another class (so it has _obj directly, not _parent) *)
  (match c.cl_super with
  | None -> true
  | Some _ -> false)

(* Analyze a function and return a set of variable IDs that can be stack-allocated *)
let analyze_escapes (f : tfunc) : (int, tclass) Hashtbl.t =
  let stack_vars = Hashtbl.create 16 in
  let escaped_vars = Hashtbl.create 16 in
  
  (* Mark a variable as escaped *)
  let mark_escaped v_id =
    Hashtbl.replace escaped_vars v_id true;
    Hashtbl.remove stack_vars v_id
  in
  
  (* Check if an expression references a tracked variable *)
  let rec get_local_var_id e =
    match e.eexpr with
    | TLocal v -> Some v.v_id
    | TParenthesis e -> get_local_var_id e
    | _ -> None
  in
  
  (* Mark variable as escaped if it's a tracked allocation *)
  let mark_if_tracked e =
    match get_local_var_id e with
    | Some v_id when Hashtbl.mem stack_vars v_id -> mark_escaped v_id
    | _ -> ()
  in
  
  (* Recursively analyze an expression for escapes *)
  let rec analyze e =
    match e.eexpr with
    (* Track new allocations assigned to local variables *)
    | TVar (v, Some { eexpr = TNew (c, _, args) }) when can_stack_alloc_class c ->
        (* Only track if not already escaped *)
        if not (Hashtbl.mem escaped_vars v.v_id) then
          Hashtbl.replace stack_vars v.v_id c;
        (* Analyze constructor arguments - they might reference tracked vars *)
        List.iter analyze args
    
    (* Reassignment to a tracked variable - the NEW value might escape *)
    | TBinop (OpAssign, { eexpr = TLocal v }, ({ eexpr = TNew (c, _, args) })) 
        when can_stack_alloc_class c ->
        (* If reassigning, keep tracking if it's still a direct TNew *)
        if not (Hashtbl.mem escaped_vars v.v_id) then
          Hashtbl.replace stack_vars v.v_id c;
        List.iter analyze args
    
    (* Assignment to field - RHS escapes *)
    | TBinop (OpAssign, { eexpr = TField _ }, rhs) ->
        mark_if_tracked rhs;
        analyze rhs
    
    (* Assignment to array - RHS escapes *)
    | TBinop (OpAssign, { eexpr = TArray _ }, rhs) ->
        mark_if_tracked rhs;
        analyze rhs
    
    (* Return - value escapes *)
    | TReturn (Some e) ->
        mark_if_tracked e;
        analyze e
    
    (* Throw - value escapes *)
    | TThrow e ->
        mark_if_tracked e;
        analyze e
    
    (* Function call - all arguments escape (conservative) *)
    (* Exception: field access on tracked var is OK (e.g., val.i) *)
    | TCall (func, args) ->
        (* The function itself might be a tracked var (if it's a closure field) *)
        analyze func;
        (* All arguments escape *)
        List.iter (fun arg ->
          mark_if_tracked arg;
          analyze arg
        ) args
    
    (* Closure/function expression - captured variables escape *)
    | TFunction tf ->
        (* Any variable used in the closure body that's from outer scope escapes *)
        let rec find_captures e =
          match e.eexpr with
          | TLocal v ->
              (* If this variable is tracked, it's being captured - mark escaped *)
              if Hashtbl.mem stack_vars v.v_id then
                mark_escaped v.v_id
          | _ -> Type.iter find_captures e
        in
        find_captures tf.tf_expr
    
    (* Field access is OK - we're just reading from the object *)
    | TField (obj, _) ->
        analyze obj
    
    (* Array access is OK for reading *)
    | TArray (arr, idx) ->
        analyze arr;
        analyze idx
    
    (* Default: recurse into sub-expressions *)
    | _ ->
        Type.iter analyze e
  in
  
  (* Analyze the function body *)
  analyze f.tf_expr;
  
  (* Return only non-escaped variables *)
  stack_vars

(* Check if a variable can be stack allocated based on escape analysis results *)
let is_stack_allocatable (stack_vars : (int, tclass) Hashtbl.t) (v : tvar) : bool =
  Hashtbl.mem stack_vars v.v_id

(* Get the class for a stack-allocatable variable *)
let get_stack_alloc_class (stack_vars : (int, tclass) Hashtbl.t) (v : tvar) : tclass option =
  try Some (Hashtbl.find stack_vars v.v_id)
  with Not_found -> None

(* Filter void-typed arguments from a function argument list *)
let filter_void_args args =
  let is_void_type t =
    match follow t with
    | TAbstract ({ a_path = ([], "Void") }, []) -> true
    | _ -> false
  in
  List.filter (fun (v, _) -> not (is_void_type v.v_type)) args

(* Extract parameter-to-field mapping from a simple constructor body.
   Returns a list of (param_var_id, field_name) pairs.
   
   This is used to optimize constructors that simply assign parameters to fields,
   allowing direct initialization instead of separate assignment statements. *)
let extract_param_field_mapping (f : tfunc) : (int * string) list =
  let mappings = ref [] in
  let filtered_args = filter_void_args f.tf_args in
  let param_ids = List.map (fun (v, _) -> v.v_id) filtered_args in
  let rec find_mapping e =
    match e.eexpr with
    | TBlock el -> List.iter find_mapping el
    | TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, 
              { eexpr = TLocal param_v })
    | TParenthesis { eexpr = TBinop (OpAssign, 
              { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, 
              { eexpr = TLocal param_v }) } ->
        (* Found: this.field = param *)
        if List.mem param_v.v_id param_ids then
          mappings := (param_v.v_id, cf.cf_name) :: !mappings
    | _ -> ()
  in
  find_mapping f.tf_expr;
  !mappings

(* Result type for escape analysis of a function *)
type escape_result = {
  stack_allocatable : (int, tclass) Hashtbl.t;  (* var_id -> class that can be stack allocated *)
  param_field_map : (int * string) list;        (* param_id -> field_name for constructor optimization *)
}

(* Perform full escape analysis on a function *)
let analyze_function (f : tfunc) : escape_result =
  {
    stack_allocatable = analyze_escapes f;
    param_field_map = extract_param_field_mapping f;
  }
