(*
 * FiberusStrings - String and identifier utilities for Fiberus code generator
 *
 * This module provides utilities for:
 * - C keyword escaping
 * - Path/identifier formatting
 * - String escaping for C string literals
 *)

(* C keywords that need escaping - identifiers matching these get prefixed with _hx_ *)
let c_keywords =
  let h = Hashtbl.create 64 in
  List.iter (fun s -> Hashtbl.add h s ()) [
    (* C89 keywords *)
    "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do";
    "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if";
    "int"; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static";
    "struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"; "while";
    (* C99 keywords *)
    "inline"; "restrict"; "_Bool"; "_Complex"; "_Imaginary";
    (* C11 keywords *)
    "_Alignas"; "_Alignof"; "_Atomic"; "_Generic"; "_Noreturn"; "_Static_assert"; "_Thread_local";
    (* Common macros/builtins that should be avoided *)
    "bool"; "true"; "false"; "NULL";
    (* Fiberus runtime types that shouldn't be shadowed *)
    "FibObject"; "FibString"; "FibArray"; "FibDynamic"; "FibClosure";
    "FibClass"; "Fiber"; "Counter";
  ];
  h

(* Escape identifier if it's a C keyword *)
let ident s =
  if Hashtbl.mem c_keywords s then "_hx_" ^ s else s

(* Convert Haxe path to C identifier (simple form, no escaping) *)
let s_path (p, s) =
  match p with
  | [] -> s
  | _ -> String.concat "_" p ^ "_" ^ s

(* Convert Haxe path to flat C identifier with proper escaping.
 * Underscores in names are doubled to avoid collisions:
 * - my_Class -> my__Class
 * - pack.MyClass -> pack_MyClass
 * - my_pack.My_Class -> my__pack_My__Class
 *)
let flat_path path =
  let p, s = path in
  let escape str = String.concat "__" (ExtString.String.nsplit str "_") in
  match p with
  | [] -> escape s
  | _ -> String.concat "_" (List.map escape p) ^ "_" ^ escape s

(* Strip path to just filename for source references *)
let strip_file file =
  Filename.basename file

(* Escape string for C string literal *)
let escape_string s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c ->
    match c with
    | '\\' -> Buffer.add_string b "\\\\"
    | '"' -> Buffer.add_string b "\\\""
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | '\000' -> Buffer.add_string b "\\0"
    | c when Char.code c < 32 || Char.code c > 126 ->
        (* Non-printable characters as hex escapes *)
        Buffer.add_string b (Printf.sprintf "\\x%02x" (Char.code c))
    | c -> Buffer.add_char b c
  ) s;
  Buffer.contents b

(* Escape string for C string literal using Haxe's StringHelper (more complete) *)
let escape_string_haxe s =
  StringHelper.s_escape s

(* Generate a valid C identifier from an arbitrary string *)
let sanitize_ident s =
  let b = Buffer.create (String.length s) in
  String.iteri (fun i c ->
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' ||
       (i > 0 && c >= '0' && c <= '9') then
      Buffer.add_char b c
    else
      Buffer.add_string b (Printf.sprintf "_%02x" (Char.code c))
  ) s;
  let result = Buffer.contents b in
  if result = "" then "_empty" else ident result

(* Check if a string is a valid C identifier *)
let is_valid_c_ident s =
  if String.length s = 0 then false
  else
    let first = s.[0] in
    (first >= 'a' && first <= 'z') || (first >= 'A' && first <= 'Z') || first = '_' &&
    String.for_all (fun c ->
      (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' || (c >= '0' && c <= '9')
    ) s &&
    not (Hashtbl.mem c_keywords s)
