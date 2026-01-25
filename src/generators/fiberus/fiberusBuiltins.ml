(*
 * FiberusBuiltins - Builtin function and method mappings
 *
 * This module provides information about:
 * - Standard library function mappings to C runtime functions
 * - Builtin intrinsic functions
 * - Array, String, Map method mappings
 *
 * The actual code generation is handled by the main generator,
 * but this module provides the lookup tables and utilities.
 *)

open Type

(* ============================================================================
 * Builtin Intrinsics
 * ============================================================================ *)

(* Intrinsic functions that have special handling *)
type intrinsic =
  | ITrace                     (* trace() / haxe.Log.trace() *)
  | IFiberus                   (* __fiberus__("code") - raw code emission *)
  | IExceptionStack            (* __fiberus_get_exception_stack() *)
  | ICallStack                 (* __fiberus_get_call_stack() *)
  | IStdIsOfType               (* Std.isOfType / Std.is *)
  | IStdInt                    (* Std.int() *)
  | IStdString                 (* Std.string() *)
  | IFiberSpawn                (* Fiber.spawn() *)
  | IFiberSpawnOn              (* Fiber.spawnOn() *)
  | IFiberSpawnAny             (* Fiber.spawnAny() *)

(* Check if an expression is a call to an intrinsic *)
let get_intrinsic (e : texpr) : intrinsic option =
  match e.eexpr with
  | TIdent "__trace__" -> Some ITrace
  | TIdent "__fiberus__" -> Some IFiberus
  | TIdent "__fiberus_get_exception_stack" -> Some IExceptionStack
  | TIdent "__fiberus_get_call_stack" -> Some ICallStack
  | TField (_, FStatic ({ cl_path = (["haxe"], "Log") }, { cf_name = "trace" })) -> Some ITrace
  | TField (_, FStatic ({ cl_path = ([], "Std") }, { cf_name = ("isOfType" | "is") })) -> Some IStdIsOfType
  | TField (_, FStatic ({ cl_path = ([], "Std") }, { cf_name = "int" })) -> Some IStdInt
  | TField (_, FStatic ({ cl_path = ([], "Std") }, { cf_name = "string" })) -> Some IStdString
  | TField (_, FStatic ({ cl_path = ([], "Fiber") }, { cf_name = "spawn" })) -> Some IFiberSpawn
  | TField (_, FStatic ({ cl_path = ([], "Fiber") }, { cf_name = "spawnOn" })) -> Some IFiberSpawnOn
  | TField (_, FStatic ({ cl_path = ([], "Fiber") }, { cf_name = "spawnAny" })) -> Some IFiberSpawnAny
  | TField (_, FStatic ({ cl_path = (["fiberus"], "Fiber") }, { cf_name = "spawn" })) -> Some IFiberSpawn
  | TField (_, FStatic ({ cl_path = (["fiberus"], "Fiber") }, { cf_name = "spawnOn" })) -> Some IFiberSpawnOn
  | TField (_, FStatic ({ cl_path = (["fiberus"], "Fiber") }, { cf_name = "spawnAny" })) -> Some IFiberSpawnAny
  | _ -> None

(* ============================================================================
 * Array Method Mappings
 * ============================================================================ *)

(* Array methods and their corresponding C function suffixes *)
type array_method =
  | ArrPush | ArrPop | ArrShift | ArrUnshift
  | ArrInsert | ArrRemove | ArrRemoveAt
  | ArrIndexOf | ArrContains | ArrReverse
  | ArrSlice | ArrConcat | ArrJoin | ArrIterator
  | ArrLength | ArrResize | ArrGet | ArrSet

let array_method_of_name (name : string) : array_method option =
  match name with
  | "push" -> Some ArrPush
  | "pop" -> Some ArrPop
  | "shift" -> Some ArrShift
  | "unshift" -> Some ArrUnshift
  | "insert" -> Some ArrInsert
  | "remove" -> Some ArrRemove
  | "indexOf" -> Some ArrIndexOf
  | "contains" -> Some ArrContains
  | "reverse" -> Some ArrReverse
  | "slice" -> Some ArrSlice
  | "concat" -> Some ArrConcat
  | "join" -> Some ArrJoin
  | "iterator" -> Some ArrIterator
  | _ -> None

(* Get C function name for array method *)
let array_method_func (prefix : string) (method_ : array_method) : string =
  match method_ with
  | ArrPush -> prefix ^ "push"
  | ArrPop -> prefix ^ "pop"
  | ArrShift -> prefix ^ "shift"
  | ArrUnshift -> prefix ^ "unshift"
  | ArrInsert -> prefix ^ "insert"
  | ArrRemove -> prefix ^ "remove"
  | ArrRemoveAt -> prefix ^ "remove_at"
  | ArrIndexOf -> prefix ^ "index_of"
  | ArrContains -> prefix ^ "contains"
  | ArrReverse -> prefix ^ "reverse"
  | ArrSlice -> prefix ^ "slice"
  | ArrConcat -> prefix ^ "concat"
  | ArrJoin -> prefix ^ "join"
  | ArrIterator -> prefix ^ "iterator"
  | ArrLength -> prefix ^ "length"
  | ArrResize -> prefix ^ "resize"
  | ArrGet -> prefix ^ "get"
  | ArrSet -> prefix ^ "set"

(* ============================================================================
 * String Method Mappings
 * ============================================================================ *)

type string_method =
  | StrCharAt | StrCharCodeAt
  | StrSubstring | StrSubstr
  | StrIndexOf | StrLastIndexOf
  | StrSplit | StrToUpperCase | StrToLowerCase | StrTrim
  | StrLength

let string_method_of_name (name : string) : string_method option =
  match name with
  | "charAt" -> Some StrCharAt
  | "charCodeAt" -> Some StrCharCodeAt
  | "substring" | "substr" -> Some StrSubstring
  | "indexOf" -> Some StrIndexOf
  | "lastIndexOf" -> Some StrLastIndexOf
  | "split" -> Some StrSplit
  | "toUpperCase" -> Some StrToUpperCase
  | "toLowerCase" -> Some StrToLowerCase
  | "trim" -> Some StrTrim
  | "length" -> Some StrLength
  | _ -> None

let string_method_func (method_ : string_method) : string =
  match method_ with
  | StrCharAt -> "fib_string_char_at_str"
  | StrCharCodeAt -> "fib_string_char_code_at"
  | StrSubstring | StrSubstr -> "fib_string_substr"
  | StrIndexOf -> "fib_string_index_of"
  | StrLastIndexOf -> "fib_string_last_index_of"
  | StrSplit -> "fib_string_split"
  | StrToUpperCase -> "fib_string_to_upper"
  | StrToLowerCase -> "fib_string_to_lower"
  | StrTrim -> "fib_string_trim"
  | StrLength -> "fib_string_length"

(* ============================================================================
 * Map Method Mappings
 * ============================================================================ *)

type map_kind =
  | MapInt       (* IntMap *)
  | MapString    (* StringMap *)
  | MapInt64     (* Int64Map *)
  | MapObject    (* ObjectMap *)

type map_method =
  | MapSet | MapGet | MapExists | MapRemove
  | MapKeys | MapIterator | MapCopy | MapToString | MapClear | MapSize

let map_method_of_name (name : string) : map_method option =
  match name with
  | "set" -> Some MapSet
  | "get" -> Some MapGet
  | "exists" -> Some MapExists
  | "remove" -> Some MapRemove
  | "keys" -> Some MapKeys
  | "iterator" -> Some MapIterator
  | "copy" -> Some MapCopy
  | "toString" -> Some MapToString
  | "clear" -> Some MapClear
  | "size" -> Some MapSize
  | _ -> None

let map_kind_prefix (kind : map_kind) : string =
  match kind with
  | MapInt -> "fib_int_map_"
  | MapString -> "fib_string_map_"
  | MapInt64 -> "fib_int64_map_"
  | MapObject -> "fib_object_map_"

let map_method_func (kind : map_kind) (method_ : map_method) : string =
  let prefix = map_kind_prefix kind in
  match method_ with
  | MapSet -> prefix ^ "set"
  | MapGet -> prefix ^ "get"
  | MapExists -> prefix ^ "exists"
  | MapRemove -> prefix ^ "remove"
  | MapKeys -> prefix ^ "keys"
  | MapIterator -> prefix ^ "iterator"
  | MapCopy -> prefix ^ "copy"
  | MapToString -> prefix ^ "to_string"
  | MapClear -> prefix ^ "clear"
  | MapSize -> prefix ^ "size"

(* Get map kind from Haxe type *)
let map_kind_of_type (t : Type.t) : map_kind option =
  match follow t with
  | TInst ({ cl_path = (["haxe"; "ds"], "IntMap") }, _) -> Some MapInt
  | TInst ({ cl_path = (["haxe"; "ds"], "StringMap") }, _) -> Some MapString
  | TInst ({ cl_path = (["haxe"; "ds"], "Int64Map") }, _) -> Some MapInt64
  | TInst ({ cl_path = (["haxe"; "ds"], "ObjectMap") }, _) -> Some MapObject
  | _ -> None

(* ============================================================================
 * Type-to-String Conversion Functions
 * ============================================================================ *)

(* Get the appropriate fib_string_from_X function for a type *)
let string_from_type_func (t : Type.t) : string option =
  match follow t with
  | TAbstract ({ a_path = ([], "Int") }, []) -> Some "fib_string_from_int"
  | TAbstract ({ a_path = ([], "Float") }, []) -> Some "fib_string_from_float"
  | TAbstract ({ a_path = ([], "Bool") }, []) -> None  (* Ternary: x ? "true" : "false" *)
  | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> Some "fib_string_from_int64"
  | TInst ({ cl_path = ([], "String") }, []) -> None  (* Already a string *)
  | _ -> Some "fib_dynamic_to_string"  (* Dynamic conversion *)

(* ============================================================================
 * Value Suffixes for Map/Dynamic Operations
 * ============================================================================ *)

(* Get value type suffix for map set/get operations *)
let map_value_suffix (t : Type.t) : string =
  match follow t with
  | TAbstract ({ a_path = ([], "Int") }, []) -> "_int"
  | TAbstract ({ a_path = ([], "Float") }, []) -> "_float"
  | TInst ({ cl_path = ([], "String") }, []) -> "_string"
  | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> "_int64"
  | _ -> "_dynamic"

(* ============================================================================
 * Type Checking
 * ============================================================================ *)

(* Check if type is String *)
let is_string_type (t : Type.t) : bool =
  match follow t with
  | TInst ({ cl_path = ([], "String") }, []) -> true
  | _ -> false

(* Check if type is Array *)
let is_array_type (t : Type.t) : bool =
  match follow t with
  | TInst ({ cl_path = ([], "Array") }, _) -> true
  | _ -> false

(* Check if type is a Map *)
let is_map_type (t : Type.t) : bool =
  map_kind_of_type t <> None

(* Check if type is Dynamic *)
let is_dynamic_type (t : Type.t) : bool =
  match follow t with
  | TDynamic _ -> true
  | TAnon _ -> true
  | TMono { tm_type = None } -> true
  | TAbstract ({ a_path = ([], "Dynamic") }, _) -> true
  | TType ({ t_path = ([], "Dynamic") }, _) -> true
  | _ -> false

(* ============================================================================
 * Array Specialization
 * ============================================================================ *)

type array_specialization =
  | ArrGeneric
  | ArrInt
  | ArrFloat
  | ArrBool
  | ArrUInt8
  | ArrInt64
  | ArrUInt64
  | ArrFloat32

let array_specialization_of_type (t : Type.t) : array_specialization =
  match follow t with
  | TInst ({ cl_path = ([], "Array") }, [elem_t]) ->
      (match follow elem_t with
      | TAbstract ({ a_path = ([], "Int") }, []) -> ArrInt
      | TAbstract ({ a_path = ([], "Float") }, []) -> ArrFloat
      | TAbstract ({ a_path = ([], "Bool") }, []) -> ArrBool
      | TAbstract ({ a_path = (["fiberus"], "UInt8") }, []) -> ArrUInt8
      | TAbstract ({ a_path = (["fiberus"], "Int64") }, []) -> ArrInt64
      | TAbstract ({ a_path = (["fiberus"], "UInt64") }, []) -> ArrUInt64
      | TAbstract ({ a_path = (["fiberus"], "Float32") }, []) -> ArrFloat32
      | _ -> ArrGeneric)
  | _ -> ArrGeneric

let array_specialization_prefix (spec : array_specialization) : string =
  match spec with
  | ArrGeneric -> "fib_array_"
  | ArrInt -> "fib_int_array_"
  | ArrFloat -> "fib_float_array_"
  | ArrBool -> "fib_bool_array_"
  | ArrUInt8 -> "fib_uint8_array_"
  | ArrInt64 -> "fib_int64_array_"
  | ArrUInt64 -> "fib_uint64_array_"
  | ArrFloat32 -> "fib_float32_array_"

let is_specialized_array (spec : array_specialization) : bool =
  spec <> ArrGeneric
