(*
 * FiberusGenClass - Class structure and metadata generation
 *
 * This module handles generation of C struct definitions and class metadata
 * for Haxe classes. It provides:
 * - Struct field collection
 * - FibClass metadata structure generation
 * - Constructor analysis (simple vs complex)
 * - GC marking function detection
 * - Vtable structure generation
 *)

open Globals
open Type
open FiberusAst
open FiberusStrings
open FiberusTypeUtils

(* ============================================================================
 * Class Field Analysis
 * ============================================================================ *)

(* Information about a class field for struct generation *)
type struct_field_info = {
  sfi_name: string;              (* C field name *)
  sfi_type: tc_type;             (* C type *)
  sfi_haxe_type: Type.t;         (* Original Haxe type *)
  sfi_needs_gc: bool;            (* Needs GC marking *)
  sfi_is_dynamic_method: bool;   (* Is a dynamic method (function pointer) *)
}

(* Get instance fields for a class (not inherited ones) *)
let get_instance_fields (c : tclass) : struct_field_info list =
  List.filter_map (fun cf ->
    match cf.cf_kind with
    | Var _ ->
        let tc_t = tc_type_of cf.cf_type in
        Some {
          sfi_name = ident cf.cf_name;
          sfi_type = tc_t;
          sfi_haxe_type = cf.cf_type;
          sfi_needs_gc = needs_gc_root tc_t;
          sfi_is_dynamic_method = false;
        }
    | Method MethDynamic ->
        (* Dynamic methods are stored as function pointers *)
        Some {
          sfi_name = ident cf.cf_name;
          sfi_type = TCPointer TCVoid;  (* void* for dynamic function *)
          sfi_haxe_type = cf.cf_type;
          sfi_needs_gc = false;
          sfi_is_dynamic_method = true;
        }
    | _ -> None
  ) c.cl_ordered_fields

(* Get fields that need GC marking *)
let get_gc_fields (c : tclass) : struct_field_info list =
  List.filter (fun sfi -> sfi.sfi_needs_gc) (get_instance_fields c)

(* Check if class needs a mark function *)
let needs_mark_function (c : tclass) : bool =
  get_gc_fields c <> []

(* ============================================================================
 * Static Field Analysis
 * ============================================================================ *)

(* Information about a static field *)
type static_field_info = {
  stfi_name: string;             (* Full C name: ClassName_fieldName *)
  stfi_short_name: string;       (* Just the field name *)
  stfi_type: tc_type;            (* C type *)
  stfi_haxe_type: Type.t;        (* Original Haxe type *)
  stfi_has_init: bool;           (* Has initializer expression *)
  stfi_needs_runtime_init: bool; (* Needs runtime initialization (not compile-time constant) *)
  stfi_is_function: bool;        (* Is a static function (not a variable) *)
}

(* Check if an expression is a compile-time constant *)
let rec is_compile_time_constant (e : texpr) : bool =
  match e.eexpr with
  | TConst (TInt _ | TFloat _ | TBool _ | TNull) -> true
  | TConst (TString _) -> false  (* Strings need runtime alloc *)
  | TConst TThis -> false
  | TConst TSuper -> false
  | TParenthesis e -> is_compile_time_constant e
  | TUnop (_, _, e) -> is_compile_time_constant e
  | TBinop (_, e1, e2) -> is_compile_time_constant e1 && is_compile_time_constant e2
  | TCast (e, _) -> is_compile_time_constant e
  | _ -> false

(* Get static fields for a class *)
let get_static_fields (c : tclass) : static_field_info list =
  let class_name = flat_path c.cl_path in
  List.filter_map (fun cf ->
    match cf.cf_kind with
    | Var _ ->
        let is_func = match cf.cf_expr with
          | Some { eexpr = TFunction _ } -> true
          | _ -> false
        in
        if is_func then None  (* Skip function expressions *)
        else
          let needs_runtime = match cf.cf_expr with
            | Some e -> not (is_compile_time_constant e)
            | None -> false
          in
          Some {
            stfi_name = class_name ^ "_" ^ ident cf.cf_name;
            stfi_short_name = ident cf.cf_name;
            stfi_type = tc_type_of cf.cf_type;
            stfi_haxe_type = cf.cf_type;
            stfi_has_init = cf.cf_expr <> None;
            stfi_needs_runtime_init = needs_runtime;
            stfi_is_function = false;
          }
    | _ -> None
  ) c.cl_ordered_statics

(* Get static fields that need runtime initialization *)
let get_runtime_init_fields (c : tclass) : static_field_info list =
  List.filter (fun stfi -> stfi.stfi_needs_runtime_init) (get_static_fields c)

(* Check if class needs a __boot function *)
let needs_boot_function (c : tclass) : bool =
  get_runtime_init_fields c <> []

(* ============================================================================
 * Constructor Analysis
 * ============================================================================ *)

(* Check if a constructor is "simple" - just assigns parameters to fields *)
let is_simple_constructor (f : tfunc) : bool =
  (* A simple constructor:
     1. Has no complex expressions (calls, allocations, etc.)
     2. Only does field assignments from parameters or constants
     3. Has no control flow
     4. All arguments are primitive types (no GC roots needed) *)
  let dominated_by_simple_assigns = ref true in
  let rec check_expr e =
    match e.eexpr with
    | TBlock el -> List.iter check_expr el
    | TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance _) }, value) ->
        (* this.field = value - check if value is simple *)
        check_simple_value value
    | TParenthesis e -> check_expr e
    | TConst _ -> ()  (* Constants are fine *)
    | TLocal _ -> ()  (* Local vars (params) are fine *)
    | _ -> dominated_by_simple_assigns := false
  and check_simple_value e =
    match e.eexpr with
    | TConst _ -> ()
    | TLocal _ -> ()
    | TParenthesis e -> check_simple_value e
    | TUnop (_, _, e) -> check_simple_value e
    | TBinop (_, e1, e2) -> check_simple_value e1; check_simple_value e2
    | TCast (e, _) -> check_simple_value e
    | _ -> dominated_by_simple_assigns := false
  in
  check_expr f.tf_expr;
  (* Check all arguments are primitive types (no GC roots needed) *)
  let all_args_primitive = List.for_all (fun (v, _) ->
    let tc_t = tc_type_of v.v_type in
    not (needs_gc_root tc_t)
  ) f.tf_args in
  all_args_primitive && !dominated_by_simple_assigns

(* Extract parameter-to-field mapping from constructor *)
let get_constructor_field_mapping (f : tfunc) : (string * string) list =
  (* Returns list of (param_name, field_name) pairs *)
  let mappings = ref [] in
  let rec find_mapping e =
    match e.eexpr with
    | TBlock el -> List.iter find_mapping el
    | TBinop (OpAssign, { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, 
              { eexpr = TLocal param_v })
    | TParenthesis { eexpr = TBinop (OpAssign, 
              { eexpr = TField ({ eexpr = TConst TThis }, FInstance (_, _, cf)) }, 
              { eexpr = TLocal param_v }) } ->
        mappings := (ident param_v.v_name, ident cf.cf_name) :: !mappings
    | _ -> ()
  in
  find_mapping f.tf_expr;
  List.rev !mappings

(* ============================================================================
 * C-AST Structure Generation
 * ============================================================================ *)

(* Generate struct definition for a class *)
let gen_struct_def (c : tclass) : tc_struct_def =
  let class_name = flat_path c.cl_path in
  let parent = match c.cl_super with
    | Some (parent_c, _) -> Some (flat_path parent_c.cl_path)
    | None -> None
  in
  let fields = get_instance_fields c in
  let tc_fields = List.map (fun sfi ->
    let comment = if sfi.sfi_is_dynamic_method then Some "dynamic function" else None in
    {
      sf_name = sfi.sfi_name;
      sf_type = if sfi.sfi_is_dynamic_method then TCPointer TCVoid else sfi.sfi_type;
      sf_comment = comment;
    }
  ) fields in
  {
    sd_name = class_name;
    sd_parent = parent;
    sd_fields = tc_fields;
  }

(* Generate class metadata structure *)
let gen_class_meta (c : tclass) (class_id : int) (vtable_size : int) : tc_class_meta =
  let class_name = flat_path c.cl_path in
  let super_name = match c.cl_super with
    | Some (parent_c, _) -> Some (flat_path parent_c.cl_path)
    | None -> None
  in
  let mark_func = if needs_mark_function c then Some (class_name ^ "_mark") else None in
  {
    cm_name = s_type_path c.cl_path;
    cm_class_id = class_id;
    cm_instance_size = "sizeof(" ^ class_name ^ ")";
    cm_super = super_name;
    cm_mark_func = mark_func;
    cm_vtable_size = vtable_size;
  }

(* ============================================================================
 * Mark Function Generation
 * ============================================================================ *)

(* Generate mark function body statements *)
let gen_mark_function_body (c : tclass) : tc_stmt list =
  let class_name = flat_path c.cl_path in
  let gc_fields = get_gc_fields c in
  if gc_fields = [] then []
  else
    let cast_stmt = TCSVar {
      vd_name = "this";
      vd_type = TCPointer (TCStruct class_name);
      vd_init = Some {
        cexpr = TCECast (TCPointer (TCStruct class_name), 
                         { cexpr = TCELocal "obj"; ctype = TCPointer TCFibObject; cpos = null_pos });
        ctype = TCPointer (TCStruct class_name);
        cpos = null_pos;
      };
      vd_static = false;
      vd_const = false;
    } in
    let mark_stmts = List.map (fun sfi ->
      TCSExpr {
        cexpr = TCECall (TCTFunc "gc_mark_object", [
          { cexpr = TCELocal "ctx"; ctype = TCPointer (TCStruct "MarkContext"); cpos = null_pos };
          { cexpr = TCEField (
              { cexpr = TCELocal "this"; ctype = TCPointer (TCStruct class_name); cpos = null_pos },
              sfi.sfi_name
            ); ctype = sfi.sfi_type; cpos = null_pos }
        ]);
        ctype = TCVoid;
        cpos = null_pos;
      }
    ) gc_fields in
    cast_stmt :: mark_stmts

(* Generate mark function definition *)
let gen_mark_function (c : tclass) : tc_func_def option =
  if not (needs_mark_function c) then None
  else
    let class_name = flat_path c.cl_path in
    Some {
      fd_name = class_name ^ "_mark";
      fd_ret = TCVoid;
      fd_args = [
        { fa_name = "obj"; fa_type = TCPointer TCFibObject };
        { fa_name = "ctx"; fa_type = TCPointer (TCStruct "MarkContext") };
      ];
      fd_body = gen_mark_function_body c;
      fd_static = true;
      fd_inline = false;
      fd_attrs = [];
    }

(* ============================================================================
 * Vtable Generation Utilities
 * ============================================================================ *)

(* Information about a vtable entry *)
type vtable_entry_info = {
  vei_slot: int;
  vei_method_name: string;
  vei_impl_class: string;     (* Class that implements this method *)
  vei_impl_func: string;      (* Full function name: ClassName_methodName *)
}

(* Find which class implements a method (walks up inheritance chain) *)
let find_method_impl (c : tclass) (method_name : string) : tclass =
  let rec find cls =
    if List.exists (fun cf -> 
      cf.cf_name = method_name && 
      match cf.cf_kind with Method _ -> true | _ -> false
    ) cls.cl_ordered_fields then
      cls
    else match cls.cl_super with
      | Some (parent, _) -> find parent
      | None -> cls  (* Fallback to original class *)
  in
  find c

(* Convert vtable methods to vtable entry info *)
let make_vtable_entries (c : tclass) (vtable_methods : (int * string * tclass_field) list) : vtable_entry_info list =
  List.map (fun (slot, method_name, _cf) ->
    let impl_class = find_method_impl c method_name in
    let impl_class_name = flat_path impl_class.cl_path in
    {
      vei_slot = slot;
      vei_method_name = method_name;
      vei_impl_class = impl_class_name;
      vei_impl_func = impl_class_name ^ "_" ^ ident method_name;
    }
  ) vtable_methods

(* Generate C-AST vtable entries *)
let gen_vtable_entries (entries : vtable_entry_info list) (vtable_size : int) : tc_vtable_entry list =
  (* Create slot-indexed list *)
  let slot_array = Array.make vtable_size None in
  List.iter (fun entry ->
    if entry.vei_slot < vtable_size then
      slot_array.(entry.vei_slot) <- Some entry
  ) entries;
  (* Convert to list *)
  Array.to_list (Array.mapi (fun slot opt ->
    match opt with
    | Some entry -> {
        ve_slot = slot;
        ve_method_name = entry.vei_method_name;
        ve_impl_name = entry.vei_impl_func;
      }
    | None -> {
        ve_slot = slot;
        ve_method_name = "";
        ve_impl_name = "NULL";
      }
  ) slot_array)

(* ============================================================================
 * Method Analysis
 * ============================================================================ *)

(* Information about a method *)
type method_info = {
  mi_name: string;               (* Method name *)
  mi_full_name: string;          (* Full C function name *)
  mi_is_static: bool;
  mi_is_virtual: bool;           (* In vtable *)
  mi_args: (string * tc_type) list;  (* Arg name, type pairs *)
  mi_ret_type: tc_type;
  mi_haxe_type: Type.t;
}

(* Get method info from class field *)
let get_method_info (c : tclass) (cf : tclass_field) (is_static : bool) : method_info option =
  match cf.cf_kind with
  | Method _ ->
      let class_name = flat_path c.cl_path in
      let args, ret = match follow cf.cf_type with
        | TFun (args, ret) ->
            let tc_args = List.filter_map (fun (name, _, t) ->
              match follow t with
              | TAbstract ({ a_path = ([], "Void") }, []) -> None
              | _ -> Some (ident name, tc_type_of t)
            ) args in
            (tc_args, tc_type_of ret)
        | _ -> ([], TCVoid)
      in
      Some {
        mi_name = cf.cf_name;
        mi_full_name = class_name ^ "_" ^ ident cf.cf_name;
        mi_is_static = is_static;
        mi_is_virtual = not is_static && not (has_class_field_flag cf CfFinal);
        mi_args = args;
        mi_ret_type = ret;
        mi_haxe_type = cf.cf_type;
      }
  | _ -> None

(* Get all methods from a class *)
let get_all_methods (c : tclass) : method_info list =
  let static_methods = List.filter_map (fun cf ->
    get_method_info c cf true
  ) c.cl_ordered_statics in
  let instance_methods = List.filter_map (fun cf ->
    get_method_info c cf false
  ) c.cl_ordered_fields in
  static_methods @ instance_methods

(* ============================================================================
 * Class Summary
 * ============================================================================ *)

(* Complete information about a class for code generation *)
type class_info = {
  ci_name: string;                 (* Flat class name *)
  ci_path: path;                   (* Haxe path *)
  ci_class_id: int;
  ci_parent: string option;        (* Parent class name *)
  ci_struct: tc_struct_def;
  ci_static_fields: static_field_info list;
  ci_instance_fields: struct_field_info list;
  ci_methods: method_info list;
  ci_has_constructor: bool;
  ci_simple_constructor: bool;
  ci_needs_mark: bool;
  ci_needs_boot: bool;
  ci_vtable_size: int;
}

(* Build complete class info *)
let build_class_info (c : tclass) (class_id : int) (vtable_size : int) : class_info =
  let has_ctor = c.cl_constructor <> None in
  let simple_ctor = match c.cl_constructor with
    | Some cf -> (match cf.cf_expr with
        | Some { eexpr = TFunction f } -> is_simple_constructor f
        | _ -> true)
    | None -> true
  in
  {
    ci_name = flat_path c.cl_path;
    ci_path = c.cl_path;
    ci_class_id = class_id;
    ci_parent = (match c.cl_super with Some (p, _) -> Some (flat_path p.cl_path) | None -> None);
    ci_struct = gen_struct_def c;
    ci_static_fields = get_static_fields c;
    ci_instance_fields = get_instance_fields c;
    ci_methods = get_all_methods c;
    ci_has_constructor = has_ctor;
    ci_simple_constructor = simple_ctor;
    ci_needs_mark = needs_mark_function c;
    ci_needs_boot = needs_boot_function c;
    ci_vtable_size = vtable_size;
  }
