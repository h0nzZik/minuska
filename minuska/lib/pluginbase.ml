open Printf
open Sexplib.Std
open Basics

type id = [ `Id of string ]

type groundterm =
  [ `GTb of BasicTypes.builtin_repr
  | `GTerm of (id*(groundterm list))
  ]

type coqModuleName = 
| User_module of string
| Std_module of string
[@@deriving sexp]

module Extracted = Dsm

(* EOF *)
