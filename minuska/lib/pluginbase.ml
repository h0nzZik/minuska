open Printf
open Sexplib.Std

type id = [ `Id of string ]

type builtin_repr = {
  br_kind : string ;
  br_value : string;
}

type groundterm =
  [ `GTb of builtin_repr
  | `GTerm of (id*(groundterm list))
  ]

type coqModuleName = 
| User_module of string
| Std_module of string
[@@deriving sexp]

(* Dsm.hai_klike *)
(* Dsm.pi_trivial) *)

module Extracted = Dsm

(* EOF *)
