(*
 * FiberusError - Error handling utilities for Fiberus code generator
 *
 * Provides consistent error reporting during code generation.
 *)

open Globals

(* Error types for the Fiberus generator *)
type fiberus_error =
  | UnsupportedFeature of string
  | InternalError of string
  | TypeMismatch of string * string  (* expected, got *)
  | MissingImplementation of string
  | InvalidState of string

(* Format error message *)
let error_message = function
  | UnsupportedFeature feature ->
      Printf.sprintf "Fiberus does not support: %s" feature
  | InternalError msg ->
      Printf.sprintf "Internal generator error: %s" msg
  | TypeMismatch (expected, got) ->
      Printf.sprintf "Type mismatch: expected %s, got %s" expected got
  | MissingImplementation what ->
      Printf.sprintf "Missing implementation for: %s" what
  | InvalidState msg ->
      Printf.sprintf "Invalid generator state: %s" msg

(* Raise a generator error with position *)
let error err pos =
  Error.raise_typing_error (error_message err) pos

(* Raise a generator error without position *)
let error_no_pos err =
  failwith (error_message err)

(* Warning - doesn't halt compilation *)
let warning msg pos =
  Printf.eprintf "[Fiberus Warning] %s at %s\n%!" msg (s_type_path ([""], pos.pfile))

(* Debug output - only when FIBERUS_DEBUG is set *)
let debug_enabled = ref false

let set_debug enabled =
  debug_enabled := enabled

let debug fmt =
  Printf.ksprintf (fun msg ->
    if !debug_enabled then
      Printf.eprintf "[Fiberus Debug] %s\n%!" msg
  ) fmt

(* Assert with error message *)
let assert_msg cond msg pos =
  if not cond then
    error (InternalError msg) pos

(* Unreachable code marker *)
let unreachable msg =
  failwith (Printf.sprintf "Unreachable code in Fiberus generator: %s" msg)
