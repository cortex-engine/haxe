(*
 * FiberusTypeUtils - Type mapping and utilities
 *
 * This module handles conversion between Haxe types and C-AST types,
 * including:
 * - Haxe type to tc_type conversion
 * - tc_type to C string representation
 * - Type predicates (is_primitive, needs_gc_root, etc.)
 * - Boxing/unboxing helpers
 *)

open Type
open FiberusAst
open FiberusStrings

(* ============================================================================
 * Haxe Type to C-AST Type Conversion
 * ============================================================================ *)

(* Convert a Haxe type to a C-AST type *)
let rec tc_type_of t =
  match t with
  | TAbstract ({ a_path = ([], "Void") }, []) -> TCVoid
  | TAbstract ({ a_path = ([], "Int") }, []) -> TCInt32
  | TAbstract ({ a_path = ([], "Float") }, []) -> TCFloat64
  | TAbstract ({ a_path = ([], "Bool") }, []) -> TCBool
  | TAbstract ({ a_path = ([], "Null") }, [inner]) ->
      (* Nullable primitives need FibDynamic to hold null *)
      (match follow inner with
      | TAbstract ({ a_path = ([], "Int") }, [])
      | TAbstract ({ a_path = ([], "Float") }, [])
      | TAbstract ({ a_path = ([], "Bool") }, []) -> TCFibDynamic
      | _ -> tc_type_of inner)
  | TInst ({ cl_path = ([], "String") }, []) -> TCFibString
  | TInst ({ cl_path = ([], "Array") }, [elem_t]) ->
      (* Specialized arrays for primitive types *)
      (match follow elem_t with
      | TAbstract ({ a_path = ([], "Int") }, []) -> TCFibArray TCArrInt
      | TAbstract ({ a_path = ([], "Float") }, []) -> TCFibArray TCArrFloat
      | TAbstract ({ a_path = ([], "Bool") }, []) -> TCFibArray TCArrBool
      | TAbstract ({ a_path = (["fiberus"], "UInt8") }, []) -> TCFibArray TCArrUInt8
      | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> TCFibArray TCArrInt64
      | TAbstract ({ a_path = (["fiberus"], "UInt64") }, []) -> TCFibArray TCArrUInt64
      | TAbstract ({ a_path = (["fiberus"], "Float32") }, []) -> TCFibArray TCArrFloat32
      | _ -> TCFibArray TCArrGeneric)
  | TInst ({ cl_path = ([], "Array") }, _) -> TCFibArray TCArrGeneric
  (* Hash map types *)
  | TInst ({ cl_path = (["haxe"; "ds"], "IntMap") }, _) -> TCFibIntMap
  | TInst ({ cl_path = (["haxe"; "ds"], "StringMap") }, _) -> TCFibStringMap
  | TInst ({ cl_path = (["haxe"; "ds"], "Int64Map") }, _) -> TCFibInt64Map
  | TInst ({ cl_path = (["haxe"; "ds"], "ObjectMap") }, _) -> TCFibObjectMap
  | TInst ({ cl_kind = KTypeParameter _ }, _) ->
      (* Type parameter T, K, V etc -> generic value *)
      TCFibDynamic
  | TInst (c, params) ->
      (* Check if any type parameter is unresolved *)
      let has_type_param = List.exists (fun p ->
        match follow p with
        | TMono { tm_type = None } -> true
        | TInst ({ cl_kind = KTypeParameter _ }, _) -> true
        | _ -> false
      ) params in
      if has_type_param then TCFibDynamic
      else TCFibClass (flat_path c.cl_path)
  | TEnum (e, _) -> TCFibEnum (flat_path e.e_path)
  | TDynamic _ -> TCFibDynamic
  | TFun _ -> TCFibClosure
  | TAnon _ -> TCFibDynamic
  | TMono r -> (match r.tm_type with None -> TCFibDynamic | Some t -> tc_type_of t)
  | TType (td, tl) -> tc_type_of (apply_typedef td tl)
  | TAbstract (a, tl) ->
      (match a.a_path with
      | ([], name) when String.length name = 1 && name.[0] >= 'A' && name.[0] <= 'Z' ->
          (* Single uppercase letter likely a type parameter *)
          TCFibDynamic
      | (["haxe"; "io"], "BytesData") -> TCFibBytesData
      (* Fiberus native types *)
      | (["fiberus"], "Char") -> TCChar
      | (["fiberus"], "Int8") -> TCInt8
      | (["fiberus"], "Int16") -> TCInt16
      | (["fiberus"], "Int32") -> TCInt32
      | (["fiberus"], "Int64") -> TCInt64
      | (["fiberus"], "UInt8") -> TCUInt8
      | (["fiberus"], "UInt16") -> TCUInt16
      | (["fiberus"], "UInt32") -> TCUInt32
      | (["fiberus"], "UInt64") -> TCUInt64
      | (["fiberus"], "Float32") -> TCFloat32
      | (["fiberus"], "Float64") -> TCFloat64
      | (["fiberus"], "SizeT") -> TCSizeT
      | (["fiberus"], "AtomicInt") -> TCAtomicInt
      | _ -> tc_type_of (Abstract.get_underlying_type a tl))
  | TLazy f -> tc_type_of (lazy_type f)

(* Convert a tvar to tc_type *)
let tc_type_of_tvar v =
  tc_type_of v.v_type

(* ============================================================================
 * C-AST Type to String Conversion
 * ============================================================================ *)

(* Convert tc_type to C string representation *)
let rec tc_type_to_string = function
  | TCVoid -> "void"
  | TCBool -> "bool"
  | TCChar -> "char"
  | TCInt8 -> "int8_t"
  | TCInt16 -> "int16_t"
  | TCInt32 -> "int32_t"
  | TCInt64 -> "int64_t"
  | TCUInt8 -> "uint8_t"
  | TCUInt16 -> "uint16_t"
  | TCUInt32 -> "uint32_t"
  | TCUInt64 -> "uint64_t"
  | TCSizeT -> "size_t"
  | TCFloat32 -> "float"
  | TCFloat64 -> "double"
  | TCAtomicInt -> "_Atomic int"
  | TCPointer t -> tc_type_to_string t ^ "*"
  | TCConstPointer t -> "const " ^ tc_type_to_string t ^ "*"
  | TCFibDynamic -> "FibDynamic"
  | TCFibString -> "FibString*"
  | TCFibArray TCArrGeneric -> "FibArray*"
  | TCFibArray TCArrInt -> "FibIntArray*"
  | TCFibArray TCArrFloat -> "FibFloatArray*"
  | TCFibArray TCArrBool -> "FibBoolArray*"
  | TCFibArray TCArrUInt8 -> "FibUInt8Array*"
  | TCFibArray TCArrInt64 -> "FibInt64Array*"
  | TCFibArray TCArrUInt64 -> "FibUInt64Array*"
  | TCFibArray TCArrFloat32 -> "FibFloat32Array*"
  | TCFibClosure -> "FibClosure*"
  | TCFibObject -> "FibObject*"
  | TCFibClass name -> name ^ "*"
  | TCFibEnum name -> name
  | TCFibIntMap -> "FibIntMap*"
  | TCFibStringMap -> "FibStringMap*"
  | TCFibInt64Map -> "FibInt64Map*"
  | TCFibObjectMap -> "FibObjectMap*"
  | TCFibBytesData -> "FibBytesData*"
  | TCStruct name -> "struct " ^ name
  | TCUnion name -> "union " ^ name
  | TCFuncPtr (args, ret) ->
      let args_str = String.concat ", " (List.map tc_type_to_string args) in
      Printf.sprintf "%s (*)(%s)" (tc_type_to_string ret) args_str
  | TCRaw s -> s

(* Generate type declaration with name *)
let tc_type_with_name typ name =
  match typ with
  | TCFuncPtr (args, ret) ->
      (* Function pointer: ret_type ( *name )(args) *)
      let args_str = String.concat ", " (List.map tc_type_to_string args) in
      Printf.sprintf "%s (*%s)(%s)" (tc_type_to_string ret) name args_str
  | _ ->
      Printf.sprintf "%s %s" (tc_type_to_string typ) name

(* Generate function pointer cast expression *)
let tc_func_ptr_cast ret_type arg_types =
  let args_with_closure = TCFibClosure :: arg_types in
  let args_str = String.concat ", " (List.map tc_type_to_string args_with_closure) in
  Printf.sprintf "(%s (*)(%s))" (tc_type_to_string ret_type) args_str

(* ============================================================================
 * Type Predicates
 * ============================================================================ *)

(* Check if type is void *)
let is_void = function
  | TCVoid -> true
  | _ -> false

(* Check if type is a primitive *)
let is_primitive = function
  | TCVoid | TCBool | TCChar
  | TCInt8 | TCInt16 | TCInt32 | TCInt64
  | TCUInt8 | TCUInt16 | TCUInt32 | TCUInt64
  | TCSizeT | TCFloat32 | TCFloat64 | TCAtomicInt -> true
  | _ -> false

(* Check if type is a pointer type *)
let is_pointer = function
  | TCPointer _ | TCConstPointer _
  | TCFibString | TCFibClosure | TCFibObject | TCFibClass _
  | TCFibArray _ | TCFibIntMap | TCFibStringMap | TCFibInt64Map | TCFibObjectMap
  | TCFibBytesData -> true
  | _ -> false

(* Check if type is a class pointer *)
let is_class_pointer = function
  | TCFibClass _ -> true
  | _ -> false

(* Check if type is FibDynamic *)
let is_fib_dynamic = function
  | TCFibDynamic -> true
  | _ -> false

(* Check if type is an enum struct *)
let is_enum_struct = function
  | TCFibEnum _ -> true
  | _ -> false

(* Check if type needs GC root registration *)
let rec needs_gc_root = function
  | TCFibString | TCFibClosure | TCFibObject | TCFibClass _
  | TCFibArray _ | TCFibDynamic
  | TCFibIntMap | TCFibStringMap | TCFibInt64Map | TCFibObjectMap
  | TCFibBytesData -> true
  | TCPointer inner -> needs_gc_root inner
  | _ -> false

(* Check if type needs write barrier for GC - object pointers need barriers *)
let needs_write_barrier_tc = function
  | TCFibString | TCFibArray _ | TCFibClass _ | TCFibClosure 
  | TCFibObject | TCFibIntMap | TCFibStringMap 
  | TCFibInt64Map | TCFibObjectMap | TCFibBytesData -> true
  | TCPointer _ -> true
  | _ -> false

(* Check if Haxe type needs GC root *)
let haxe_type_needs_gc_root t =
  needs_gc_root (tc_type_of t)

(* Check if type is String *)
let is_string_type t =
  match follow t with
  | TInst ({ cl_path = ([], "String") }, []) -> true
  | _ -> false

(* Check if type is Dynamic *)
let is_dynamic_type t =
  match follow t with
  | TDynamic _ -> true
  | TAnon _ -> true
  | TMono { tm_type = None } -> true
  | TAbstract ({ a_path = ([], "Dynamic") }, _) -> true
  | TType ({ t_path = ([], "Dynamic") }, _) -> true
  | _ -> false

(* Check if type is Array *)
let is_array_type t =
  match follow t with
  | TInst ({ cl_path = ([], "Array") }, _) -> true
  | _ -> false

(* Check if type is an enum *)
let is_enum_type t =
  match follow t with
  | TEnum _ -> true
  | _ -> false

(* ============================================================================
 * Array Utilities
 * ============================================================================ *)

(* Get array kind from Haxe type *)
let get_array_kind t =
  match follow t with
  | TInst ({ cl_path = ([], "Array") }, [elem_t]) ->
      (match follow elem_t with
      | TAbstract ({ a_path = ([], "Int") }, []) -> TCArrInt
      | TAbstract ({ a_path = ([], "Float") }, []) -> TCArrFloat
      | TAbstract ({ a_path = ([], "Bool") }, []) -> TCArrBool
      | TAbstract ({ a_path = (["fiberus"], "UInt8") }, []) -> TCArrUInt8
      | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> TCArrInt64
      | TAbstract ({ a_path = (["fiberus"], "UInt64") }, []) -> TCArrUInt64
      | TAbstract ({ a_path = (["fiberus"], "Float32") }, []) -> TCArrFloat32
      | _ -> TCArrGeneric)
  | _ -> TCArrGeneric

(* Get array element type *)
let get_array_elem_type t =
  match follow t with
  | TInst ({ cl_path = ([], "Array") }, [elem_t]) -> tc_type_of elem_t
  | _ -> TCFibDynamic

(* Get array function prefix for specialized arrays *)
let array_kind_prefix = function
  | TCArrGeneric -> "fib_array_"
  | TCArrInt -> "fib_int_array_"
  | TCArrFloat -> "fib_float_array_"
  | TCArrBool -> "fib_bool_array_"
  | TCArrUInt8 -> "fib_uint8_array_"
  | TCArrInt64 -> "fib_int64_array_"
  | TCArrUInt64 -> "fib_uint64_array_"
  | TCArrFloat32 -> "fib_float32_array_"

(* Get C element type for array kind (for compound literals) *)
let array_kind_c_elem_type = function
  | TCArrGeneric -> "FibDynamic"
  | TCArrInt -> "int32_t"
  | TCArrFloat -> "double"
  | TCArrBool -> "uint8_t"
  | TCArrUInt8 -> "uint8_t"
  | TCArrInt64 -> "int64_t"
  | TCArrUInt64 -> "uint64_t"
  | TCArrFloat32 -> "float"

(* ============================================================================
 * Boxing/Unboxing Utilities
 * ============================================================================ *)

(* Get box kind for a C-AST type *)
let box_kind_of_type = function
  | TCInt32 -> TCBoxInt
  | TCInt64 -> TCBoxInt64
  | TCFloat64 | TCFloat32 -> TCBoxFloat
  | TCBool -> TCBoxBool
  | TCFibString -> TCBoxString
  | TCFibArray _ -> TCBoxArray
  | TCFibObject | TCFibClass _ -> TCBoxObject
  | TCFibClosure -> TCBoxClosure
  | TCFibEnum name -> TCBoxEnum name
  | TCFibDynamic -> TCBoxDynamic
  | _ -> TCBoxDynamic

(* Get FibDynamic field suffix for unboxing *)
let fib_dynamic_field_suffix = function
  | TCInt32 -> ".data.intVal"
  | TCInt64 -> ".data.int64Val"
  | TCFloat64 | TCFloat32 -> ".data.floatVal"
  | TCBool -> ".data.boolVal"
  | TCFibString -> ".data.stringVal"
  | TCFibObject -> ".data.objectVal"
  | TCFibClass _ -> ".data.objectVal"
  | TCFibArray _ -> ".data.arrayVal"
  | TCPointer _ -> ".data.ptrVal"
  | _ -> ""

(* Get boxing function name *)
let box_func_name = function
  | TCBoxInt -> "fib_dynamic_int"
  | TCBoxInt64 -> "fib_dynamic_int64"
  | TCBoxFloat -> "fib_dynamic_float"
  | TCBoxBool -> "fib_dynamic_bool"
  | TCBoxString -> "fib_dynamic_string"
  | TCBoxArray -> "fib_dynamic_array"
  | TCBoxObject -> "fib_dynamic_object"
  | TCBoxClosure -> "fib_dynamic_object"
  | TCBoxEnum _ -> "fib_dynamic_enum"
  | TCBoxDynamic -> ""
  | TCBoxNull -> "fib_dynamic_null"

(* Get unboxing function name *)
let unbox_func_name = function
  | TCInt32 -> "fib_dynamic_to_int"
  | TCInt64 -> "fib_dynamic_to_int64"
  | TCFloat64 | TCFloat32 -> "fib_dynamic_to_float"
  | TCBool -> "fib_dynamic_to_bool"
  | TCFibString -> "fib_dynamic_to_string"
  | TCFibArray _ -> "fib_dynamic_to_array"
  | TCFibObject | TCFibClass _ -> "fib_dynamic_to_object"
  | TCFibEnum _ -> "fib_dynamic_to_ptr"  (* Returns void*, needs cast and deref *)
  | _ -> ""

(* Check if unboxing to this type needs special enum handling *)
let unbox_is_enum = function
  | TCFibEnum _ -> true
  | _ -> false

(* ============================================================================
 * Map Utilities
 * ============================================================================ *)

(* Get map value type suffix for operations *)
let map_value_suffix typ =
  match typ with
  | TCInt32 -> "_int"
  | TCInt64 -> "_int64"
  | TCFloat64 | TCFloat32 -> "_float"
  | TCFibString -> "_string"
  | _ -> "_dynamic"

(* ============================================================================
 * Conversion from Old Style
 * ============================================================================ *)

(* Convert old-style string type to tc_type (for gradual migration) *)
let tc_type_of_string s =
  match s with
  | "void" -> TCVoid
  | "bool" -> TCBool
  | "char" -> TCChar
  | "int8_t" -> TCInt8
  | "int16_t" -> TCInt16
  | "int32_t" -> TCInt32
  | "int64_t" -> TCInt64
  | "uint8_t" -> TCUInt8
  | "uint16_t" -> TCUInt16
  | "uint32_t" -> TCUInt32
  | "uint64_t" -> TCUInt64
  | "size_t" -> TCSizeT
  | "float" -> TCFloat32
  | "double" -> TCFloat64
  | "_Atomic int" -> TCAtomicInt
  | "FibDynamic" -> TCFibDynamic
  | "FibString*" -> TCFibString
  | "FibArray*" -> TCFibArray TCArrGeneric
  | "FibIntArray*" -> TCFibArray TCArrInt
  | "FibFloatArray*" -> TCFibArray TCArrFloat
  | "FibBoolArray*" -> TCFibArray TCArrBool
  | "FibUInt8Array*" -> TCFibArray TCArrUInt8
  | "FibInt64Array*" -> TCFibArray TCArrInt64
  | "FibUInt64Array*" -> TCFibArray TCArrUInt64
  | "FibFloat32Array*" -> TCFibArray TCArrFloat32
  | "FibClosure*" -> TCFibClosure
  | "FibObject*" -> TCFibObject
  | "FibIntMap*" -> TCFibIntMap
  | "FibStringMap*" -> TCFibStringMap
  | "FibInt64Map*" -> TCFibInt64Map
  | "FibObjectMap*" -> TCFibObjectMap
  | "FibBytesData*" -> TCFibBytesData
  | s when String.length s > 0 && s.[String.length s - 1] = '*' ->
      TCFibClass (String.sub s 0 (String.length s - 1))
  | s -> TCRaw s

(* Check if a C type string ends with asterisk (is pointer) *)
let is_c_pointer_string s =
  String.length s > 1 && s.[String.length s - 1] = '*'

(* Check if type string is a class pointer (not built-in) *)
let is_class_pointer_string s =
  is_c_pointer_string s &&
  s <> "FibString*" && s <> "FibArray*" && s <> "FibDynamic*" &&
  s <> "FibClosure*" && s <> "FibObject*"

(* ============================================================================
 * Function Type Utilities
 * ============================================================================ *)

(* Get parameter types from a function type *)
let get_param_types t =
  match follow t with
  | TFun (args, _) -> List.map (fun (_, _, t) -> t) args
  | _ -> []
