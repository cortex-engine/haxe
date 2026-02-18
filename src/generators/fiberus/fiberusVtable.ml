(*
 * FiberusVtable - Virtual method dispatch for Fiberus
 *
 * This module handles vtable (virtual method table) generation for
 * polymorphic method dispatch. When a method is called through a base
 * class or interface reference, the actual method implementation is
 * looked up at runtime via the vtable.
 *
 * Vtable Slot Assignment:
 * - Each virtual method is assigned a unique slot index
 * - Override methods inherit their parent's slot
 * - Interface methods get slots from the interface definition
 * - Slots are assigned globally per method signature
 *)

open Globals
open Ast
open Type

(*
 * Method key for vtable slot assignment.
 * Format: "defining_class.method_name" or "interface.method_name"
 *)
type method_key = string

(*
 * Information about a vtable slot.
 *)
type slot_info = {
  slot_index : int;           (* Index in the vtable array *)
  method_name : string;       (* Original method name *)
  defining_path : path;       (* Class/interface that defines this slot *)
  return_type : Type.t;       (* Return type for cast generation *)
  arg_types : Type.t list;    (* Argument types for cast generation *)
}

(*
 * Vtable information for a single class.
 *)
type class_vtable = {
  cv_path : path;                               (* Class path *)
  cv_slots : (method_key, slot_info) Hashtbl.t; (* Method -> slot mapping *)
  cv_size : int;                                (* Total number of slots *)
  cv_methods : (int, method_key * tclass_field) Hashtbl.t; (* Slot -> method info *)
}

(*
 * Global vtable context built during analysis.
 *)
type vtable_context = {
  (* All class vtables *)
  vtables : (path, class_vtable) Hashtbl.t;
  (* Global slot counter for new methods *)
  mutable next_slot : int;
  (* Interface slot mappings: interface_path.method -> slot *)
  interface_slots : (method_key, int) Hashtbl.t;
}

(*
 * Create an empty vtable context.
 *)
let create_context () = {
  vtables = Hashtbl.create 64;
  next_slot = 0;
  interface_slots = Hashtbl.create 32;
}

(*
 * Generate a method key for slot assignment.
 *)
let method_key (c : tclass) (cf : tclass_field) : method_key =
  let path_str = s_type_path c.cl_path in
  path_str ^ "." ^ cf.cf_name

(*
 * Generate an interface method key.
 *)
let interface_method_key (iface : tclass) (cf : tclass_field) : method_key =
  let path_str = s_type_path iface.cl_path in
  path_str ^ "." ^ cf.cf_name

(*
 * Check if a method is an instance method (not static, not inline).
 *)
let is_instance_method (cf : tclass_field) : bool =
  match cf.cf_kind with
  | Method m when m <> MethDynamic ->
    not (has_class_field_flag cf CfStatic) &&
    not (has_meta Meta.Inline cf.cf_meta)
  | _ -> false

(*
 * Check if a class is an interface.
 *)
let is_interface (c : tclass) : bool =
  has_class_flag c CInterface

(*
 * Get method parameter types.
 *)
let get_method_types (cf : tclass_field) : Type.t list * Type.t =
  match follow cf.cf_type with
  | TFun (args, ret) -> (List.map (fun (_, _, t) -> t) args, ret)
  | _ -> ([], t_dynamic)

(*
 * Find if a method overrides a parent class method.
 * Returns Some parent_class if override found, None otherwise.
 *)
let rec find_override_parent (c : tclass) (method_name : string) : tclass option =
  match c.cl_super with
  | None -> None
  | Some (parent, _) ->
    if List.exists (fun cf -> cf.cf_name = method_name && is_instance_method cf) 
       parent.cl_ordered_fields then
      Some parent
    else
      find_override_parent parent method_name

(*
 * Find the root class that defines a method (for slot assignment).
 *)
let rec find_defining_class (c : tclass) (method_name : string) : tclass =
  match find_override_parent c method_name with
  | Some parent -> find_defining_class parent method_name
  | None -> c

(*
 * Check if a method needs virtual dispatch.
 * A method needs virtual dispatch if:
 * 1. It overrides a parent class method, OR
 * 2. It could be overridden by a subclass (we treat all non-final instance methods as virtual)
 *)
let needs_virtual_dispatch (c : tclass) (cf : tclass_field) : bool =
  (* Skip extern classes *)
  if has_class_flag c CExtern then false
  (* Skip interfaces (they don't have implementations) *)
  else if is_interface c then false
  (* Must be an instance method *)
  else if not (is_instance_method cf) then false
  (* Skip final methods *)
  else if has_meta Meta.Final cf.cf_meta then false
  (* All other instance methods are virtual *)
  else true

(*
 * Collect all interfaces implemented by a class (including inherited).
 * Recursively follows interface-extends-interface chains (e.g. IChild extends IParent1).
 *)
let collect_interfaces (c : tclass) : tclass list =
  let seen = Hashtbl.create 16 in
  let result = ref [] in
  let rec collect_from_class cls =
    (* Direct interfaces *)
    List.iter (fun (iface, _) ->
      if not (Hashtbl.mem seen iface.cl_path) then begin
        Hashtbl.add seen iface.cl_path true;
        result := iface :: !result;
        (* Recursively collect parent interfaces of this interface *)
        collect_from_class iface
      end
    ) cls.cl_implements;
    (* Parent class *)
    (match cls.cl_super with
     | Some (parent, _) -> collect_from_class parent
     | None -> ())
  in
  collect_from_class c;
  List.rev !result

(*
 * Assign slots to interface methods.
 *)
let assign_interface_slots (ctx : vtable_context) (iface : tclass) : unit =
  List.iter (fun cf ->
    if is_instance_method cf then begin
      let key = interface_method_key iface cf in
      if not (Hashtbl.mem ctx.interface_slots key) then begin
        Hashtbl.add ctx.interface_slots key ctx.next_slot;
        ctx.next_slot <- ctx.next_slot + 1
      end
    end else begin
      (* Property getters/setters: interface Var fields with AccCall need slots *)
      (match cf.cf_kind with
      | Var { v_read = AccCall; _ } ->
        let key = s_type_path iface.cl_path ^ ".get_" ^ cf.cf_name in
        if not (Hashtbl.mem ctx.interface_slots key) then begin
          Hashtbl.add ctx.interface_slots key ctx.next_slot;
          ctx.next_slot <- ctx.next_slot + 1
        end
      | _ -> ());
      (match cf.cf_kind with
      | Var { v_write = AccCall; _ } ->
        let key = s_type_path iface.cl_path ^ ".set_" ^ cf.cf_name in
        if not (Hashtbl.mem ctx.interface_slots key) then begin
          Hashtbl.add ctx.interface_slots key ctx.next_slot;
          ctx.next_slot <- ctx.next_slot + 1
        end
      | _ -> ())
    end
  ) iface.cl_ordered_fields

(*
 * Build vtable for a single class.
 * Must be called after parent class vtables are built.
 *)
let build_class_vtable (ctx : vtable_context) (c : tclass) : class_vtable =
  let slots = Hashtbl.create 16 in
  let methods = Hashtbl.create 16 in
  
  (* Start with parent's vtable if any *)
  let start_slot = match c.cl_super with
    | Some (parent, _) ->
      (match Hashtbl.find_opt ctx.vtables parent.cl_path with
       | Some parent_vt ->
         (* Copy all parent slots *)
         Hashtbl.iter (fun key info ->
           Hashtbl.add slots key info;
           Hashtbl.add methods info.slot_index (key, 
             (* Find if we override this method *)
             match List.find_opt (fun cf -> cf.cf_name = info.method_name) c.cl_ordered_fields with
             | Some cf -> cf
              | None -> 
                (* Use ancestor's field - walk up the hierarchy *)
                let rec find_in_ancestors cls =
                  match List.find_opt (fun cf -> cf.cf_name = info.method_name) cls.cl_ordered_fields with
                  | Some cf -> cf
                  | None ->
                    (match cls.cl_super with
                     | Some (grandparent, _) -> find_in_ancestors grandparent
                     | None -> raise Not_found)
                in
                find_in_ancestors parent
           )
         ) parent_vt.cv_slots;
         parent_vt.cv_size
       | None -> 0)
    | None -> 0
  in
  
  let next_slot = ref start_slot in
  
  (* Process interface methods first *)
  let interfaces = collect_interfaces c in
  (* Helper: assign an interface slot for a method name, finding the implementation in class *)
  let assign_iface_method iface method_name =
    (* Build a synthetic key for the interface method *)
    let ikey = s_type_path iface.cl_path ^ "." ^ method_name in
    let slot = match Hashtbl.find_opt ctx.interface_slots ikey with
      | Some s -> s
      | None ->
        let s = ctx.next_slot in
        ctx.next_slot <- ctx.next_slot + 1;
        Hashtbl.add ctx.interface_slots ikey s;
        s
    in
    (* Find implementing method in class or its ancestors *)
    let rec find_method_in_hierarchy cls =
      match List.find_opt (fun cf -> cf.cf_name = method_name && is_instance_method cf) cls.cl_ordered_fields with
      | Some cf -> Some cf
      | None ->
        match cls.cl_super with
        | Some (parent, _) -> find_method_in_hierarchy parent
        | None -> None
    in
    match find_method_in_hierarchy c with
    | Some cf ->
      let (arg_types, ret_type) = get_method_types cf in
      let info = {
        slot_index = slot;
        method_name = cf.cf_name;
        defining_path = iface.cl_path;
        return_type = ret_type;
        arg_types = arg_types;
      } in
      Hashtbl.replace slots ikey info;
      Hashtbl.replace methods slot (ikey, cf);
      if slot >= !next_slot then next_slot := slot + 1
    | None ->
      (* No implementation found - still ensure vtable is large enough for the slot *)
      if slot >= !next_slot then next_slot := slot + 1
  in
  List.iter (fun iface ->
    List.iter (fun icf ->
      if is_instance_method icf then
        assign_iface_method iface icf.cf_name
      else begin
        (* Handle property getters/setters: interface Var fields with AccCall
           accessor need their get_X/set_X methods assigned vtable slots *)
        (match icf.cf_kind with
        | Var { v_read = AccCall; _ } ->
          assign_iface_method iface ("get_" ^ icf.cf_name)
        | _ -> ());
        (match icf.cf_kind with
        | Var { v_write = AccCall; _ } ->
          assign_iface_method iface ("set_" ^ icf.cf_name)
        | _ -> ())
      end
    ) iface.cl_ordered_fields
  ) interfaces;
  
  (* Process class methods *)
  List.iter (fun cf ->
    if needs_virtual_dispatch c cf then begin
      let defining_class = find_defining_class c cf.cf_name in
      let key = method_key defining_class cf in
      
      (* Check if slot already assigned (from parent or interface) *)
      let slot = match Hashtbl.find_opt slots key with
        | Some info -> info.slot_index
        | None ->
          (* Check interface slots *)
          let iface_key = List.fold_left (fun acc iface ->
            if acc <> None then acc
            else
              let ik = interface_method_key iface cf in
              if Hashtbl.mem ctx.interface_slots ik then Some ik else None
          ) None interfaces in
          match iface_key with
          | Some ik ->
            Hashtbl.find ctx.interface_slots ik
          | None ->
            (* New slot *)
            let s = !next_slot in
            next_slot := !next_slot + 1;
            s
      in
      
      let (arg_types, ret_type) = get_method_types cf in
      let info = {
        slot_index = slot;
        method_name = cf.cf_name;
        defining_path = defining_class.cl_path;
        return_type = ret_type;
        arg_types = arg_types;
      } in
      Hashtbl.replace slots key info;
      Hashtbl.replace methods slot (key, cf)
    end
  ) c.cl_ordered_fields;
  
  let vt = {
    cv_path = c.cl_path;
    cv_slots = slots;
    cv_size = !next_slot;
    cv_methods = methods;
  } in
  Hashtbl.add ctx.vtables c.cl_path vt;
  vt

(*
 * Sort classes by inheritance order (parents before children).
 *)
let sort_by_inheritance (classes : tclass list) : tclass list =
  let visited = Hashtbl.create 64 in
  let result = ref [] in
  
  let rec visit c =
    if not (Hashtbl.mem visited c.cl_path) then begin
      Hashtbl.add visited c.cl_path true;
      (* Visit parent first *)
      (match c.cl_super with
       | Some (parent, _) -> visit parent
       | None -> ());
      (* Visit implemented interfaces *)
      List.iter (fun (iface, _) -> visit iface) c.cl_implements;
      result := c :: !result
    end
  in
  List.iter visit classes;
  List.rev !result

(*
 * Build vtables for all classes in the program.
 *)
let build_all_vtables (types : Type.module_type list) : vtable_context =
  let ctx = create_context () in
  
  (* Collect all classes and interfaces *)
  let classes = ref [] in
  let interfaces = ref [] in
  List.iter (function
    | TClassDecl c when not (has_class_flag c CExtern) &&
        (match c.cl_kind with
         | KAbstractImpl a ->
           (match Type.follow a.a_this with TInst _ -> false | _ -> true)
         | _ -> true) ->
      if is_interface c then
        interfaces := c :: !interfaces
      else
        classes := c :: !classes
    | _ -> ()
  ) types;
  
  (* Assign interface slots first *)
  List.iter (assign_interface_slots ctx) !interfaces;
  
  (* Sort classes by inheritance and build vtables *)
  let sorted = sort_by_inheritance !classes in
  List.iter (fun c -> ignore (build_class_vtable ctx c)) sorted;
  
  ctx

(*
 * Get vtable slot for a method call.
 * Returns None if method doesn't need virtual dispatch.
 *)
let get_vtable_slot (ctx : vtable_context) (c : tclass) (cf : tclass_field) : slot_info option =
  match Hashtbl.find_opt ctx.vtables c.cl_path with
  | None -> None
  | Some vt ->
    (* Find the defining class for this method *)
    let defining = find_defining_class c cf.cf_name in
    let key = method_key defining cf in
    Hashtbl.find_opt vt.cv_slots key

(*
 * Get vtable slot for an interface method call.
 *)
let get_interface_slot (ctx : vtable_context) (iface : tclass) (cf : tclass_field) : int option =
  let key = interface_method_key iface cf in
  Hashtbl.find_opt ctx.interface_slots key

(*
 * Check if a class has any virtual methods (needs a vtable).
 *)
let class_needs_vtable (ctx : vtable_context) (c : tclass) : bool =
  match Hashtbl.find_opt ctx.vtables c.cl_path with
  | None -> false
  | Some vt -> vt.cv_size > 0

(*
 * Get vtable size for a class.
 *)
let get_vtable_size (ctx : vtable_context) (c : tclass) : int =
  match Hashtbl.find_opt ctx.vtables c.cl_path with
  | None -> 0
  | Some vt -> vt.cv_size

(*
 * Get all methods in a class's vtable, sorted by slot index.
 *)
let get_vtable_methods (ctx : vtable_context) (c : tclass) : (int * string * tclass_field) list =
  match Hashtbl.find_opt ctx.vtables c.cl_path with
  | None -> []
  | Some vt ->
    let methods = Hashtbl.fold (fun slot (_, cf) acc ->
      (slot, cf.cf_name, cf) :: acc
    ) vt.cv_methods [] in
    List.sort (fun (a, _, _) (b, _, _) -> compare a b) methods

(*
 * Get IMap interface method slot assignments.
 * Returns a list of (method_name, slot_index) pairs for all IMap methods
 * that have been assigned interface slots in this build.
 * Returns empty list if IMap is not present or has no slots.
 *)
let get_imap_slots (ctx : vtable_context) : (string * int) list =
  let imap_path = "haxe.IMap" in
  let methods = ["get"; "set"; "exists"; "remove"; "keys"; "iterator";
                 "keyValueIterator"; "copy"; "toString"; "clear"; "size"] in
  List.filter_map (fun mname ->
    let key = imap_path ^ "." ^ mname in
    match Hashtbl.find_opt ctx.interface_slots key with
    | Some slot -> Some (mname, slot)
    | None -> None
  ) methods
