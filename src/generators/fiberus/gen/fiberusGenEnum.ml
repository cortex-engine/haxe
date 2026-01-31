(*
 * FiberusGenEnum - Enum structure and constructor generation
 *
 * This module handles generation of C struct definitions and constructor
 * functions for Haxe enums. It provides:
 * - Enum struct generation
 * - Constructor function generation
 * - Constant enum values
 * - Parameter boxing for enum params
 *)

open Globals
open Type
open FiberusAst
open FiberusStrings
open FiberusTypeUtils

(* ============================================================================
 * Enum Constructor Analysis
 * ============================================================================ *)

(* Information about an enum constructor *)
type enum_constr_info = {
  eci_name: string;              (* Constructor name *)
  eci_index: int;                (* Enum index *)
  eci_params: (string * tc_type * Type.t) list;  (* name, C type, Haxe type *)
  eci_has_params: bool;          (* Has parameters (needs function) *)
}

(* Check if a type is void *)
let is_void_type (t : Type.t) : bool =
  match follow t with
  | TAbstract ({ a_path = ([], "Void") }, []) -> true
  | _ -> false

(* Get enum constructor info *)
let get_enum_constr_info (ef : tenum_field) : enum_constr_info =
  match ef.ef_type with
  | TFun (args, _) ->
      let filtered_params = List.filter_map (fun (name, _, t) ->
        if is_void_type t then None
        else Some (ident name, tc_type_of t, t)
      ) args in
      {
        eci_name = ef.ef_name;
        eci_index = ef.ef_index;
        eci_params = filtered_params;
        eci_has_params = filtered_params <> [];
      }
  | _ ->
      {
        eci_name = ef.ef_name;
        eci_index = ef.ef_index;
        eci_params = [];
        eci_has_params = false;
      }

(* Get all constructors for an enum *)
let get_enum_constructors (e : tenum) : enum_constr_info list =
  let constrs = ref [] in
  PMap.iter (fun _ ef ->
    constrs := get_enum_constr_info ef :: !constrs
  ) e.e_constrs;
  (* Sort by index for consistent output *)
  List.sort (fun a b -> compare a.eci_index b.eci_index) !constrs

(* ============================================================================
 * Enum Info
 * ============================================================================ *)

(* Complete information about an enum *)
type enum_info = {
  ei_name: string;               (* Flat enum name *)
  ei_path: path;                 (* Haxe path *)
  ei_constructors: enum_constr_info list;
  ei_max_params: int;            (* Maximum number of params in any constructor *)
}

(* Build enum info *)
let build_enum_info (e : tenum) : enum_info =
  let constrs = get_enum_constructors e in
  let max_params = List.fold_left (fun acc ci ->
    max acc (List.length ci.eci_params)
  ) 0 constrs in
  {
    ei_name = flat_path e.e_path;
    ei_path = e.e_path;
    ei_constructors = constrs;
    ei_max_params = max_params;
  }

(* ============================================================================
 * C-AST Generation
 * ============================================================================ *)

(* Generate enum struct definition *)
let gen_enum_def (info : enum_info) : tc_enum_def =
  let constrs = List.map (fun ci ->
    {
      ec_name = ci.eci_name;
      ec_index = ci.eci_index;
      ec_params = List.map (fun (name, tc_t, _) -> (name, tc_t)) ci.eci_params;
    }
  ) info.ei_constructors in
  {
    ed_name = info.ei_name;
    ed_constrs = constrs;
    ed_max_params = info.ei_max_params;
  }

(* ============================================================================
 * Boxing Utilities for Enum Parameters
 * ============================================================================ *)

(* Get the appropriate boxing expression for an enum parameter *)
let box_enum_param (param_name : string) (tc_t : tc_type) : tc_expr =
  let param_ref = mk_expr (TCELocal param_name) tc_t in
  match tc_t with
  | TCInt32 ->
      mk_expr (TCEBox (param_ref, TCBoxInt)) TCFibDynamic
  | TCInt64 ->
      mk_expr (TCEBox (param_ref, TCBoxInt64)) TCFibDynamic
  | TCFloat64 | TCFloat32 ->
      mk_expr (TCEBox (param_ref, TCBoxFloat)) TCFibDynamic
  | TCBool ->
      mk_expr (TCEBox (param_ref, TCBoxBool)) TCFibDynamic
  | TCFibString ->
      mk_expr (TCEBox (param_ref, TCBoxString)) TCFibDynamic
  | TCFibArray _ ->
      mk_expr (TCEBox (param_ref, TCBoxArray)) TCFibDynamic
  | TCFibClosure ->
      mk_expr (TCEBox (param_ref, TCBoxClosure)) TCFibDynamic
  | TCFibObject | TCFibClass _ ->
      mk_expr (TCEBox (param_ref, TCBoxObject)) TCFibDynamic
  | TCFibEnum _enum_name ->
      (* Enum struct - use fib_dynamic_enum with address and size *)
      mk_expr (TCECall (TCTFunc "fib_dynamic_enum", [
          mk_expr (TCEAddrOf param_ref) (TCPointer tc_t);
          mk_expr (TCESizeOf tc_t) TCSizeT;
        ])) TCFibDynamic
  | TCFibDynamic ->
      param_ref  (* Already FibDynamic *)
  | _ ->
      (* Default: treat as object pointer *)
      mk_expr (TCEBox (param_ref, TCBoxObject)) TCFibDynamic

(* ============================================================================
 * Constructor Function Generation
 * ============================================================================ *)

(* Generate constructor function definition for enum with parameters *)
let gen_enum_constructor_func (info : enum_info) (ci : enum_constr_info) : tc_func_def =
  let enum_type = TCFibEnum info.ei_name in
  
  (* Function arguments *)
  let args = List.map (fun (name, tc_t, _) ->
    { fa_name = name; fa_type = tc_t }
  ) ci.eci_params in
  
  (* Function body *)
  let body = 
    (* Declare result: EnumName _e = { .index = N }; *)
    let decl_stmt = TCSVar {
      vd_name = "_e";
      vd_type = enum_type;
      vd_init = Some (mk_expr (TCERaw (Printf.sprintf "{ .index = %d }" ci.eci_index)) enum_type);
      vd_static = false;
      vd_const = false;
    } in
    
    (* Assign each parameter: _e.params[i] = box(param); *)
    let assign_stmts = List.mapi (fun i (name, tc_t, _) ->
      let boxed = box_enum_param name tc_t in
      let local_e = mk_expr (TCELocal "_e") enum_type in
      let param_access = mk_expr (TCEEnumParam (local_e, i)) TCFibDynamic in
      TCSExpr (mk_expr (TCEAssign (param_access, boxed)) TCFibDynamic)
    ) ci.eci_params in
    
    (* Return _e; *)
    let return_stmt = TCSReturn (Some (mk_expr (TCELocal "_e") enum_type)) in
    
    [decl_stmt] @ assign_stmts @ [return_stmt]
  in
  
  {
    fd_name = info.ei_name ^ "_" ^ ci.eci_name;
    fd_ret = enum_type;
    fd_args = args;
    fd_body = body;
    fd_static = false;  (* Not static - needs to be visible *)
    fd_inline = false;
    fd_attrs = [];
  }

(* Generate constant for enum without parameters *)
let gen_enum_const_decl (info : enum_info) (ci : enum_constr_info) : tc_decl =
  let enum_type = TCFibEnum info.ei_name in
  TCDVar {
    vd_name = info.ei_name ^ "_" ^ ci.eci_name;
    vd_type = enum_type;
    vd_init = Some (mk_expr (TCERaw (Printf.sprintf "{ .index = %d }" ci.eci_index)) enum_type);
    vd_static = false;
    vd_const = true;
  }

(* ============================================================================
 * Full Enum Generation
 * ============================================================================ *)

(* Generate all declarations for an enum *)
let gen_enum_decls (info : enum_info) : tc_decl list =
  (* Struct definition *)
  let struct_decl = TCDEnum (gen_enum_def info) in
  
  (* Constructor functions and constants *)
  let constr_decls = List.map (fun ci ->
    if ci.eci_has_params then
      TCDFunc (gen_enum_constructor_func info ci)
    else
      gen_enum_const_decl info ci
  ) info.ei_constructors in
  
  struct_decl :: constr_decls

(* ============================================================================
 * Enum Parameter Access Helpers
 * ============================================================================ *)

(* Get unboxing expression for enum parameter access *)
let unbox_enum_param (enum_expr : tc_expr) (param_idx : int) (target_type : tc_type) : tc_expr =
  let param_access = mk_expr_pos (TCEEnumParam (enum_expr, param_idx)) TCFibDynamic enum_expr.cpos in
  mk_expr_pos (TCEUnbox (param_access, target_type)) target_type enum_expr.cpos

(* Check if type is an enum struct type *)
let is_enum_type (t : tc_type) : bool =
  match t with
  | TCFibEnum _ -> true
  | _ -> false
