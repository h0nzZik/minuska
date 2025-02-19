open Base
open Core
open Printf
open Sexplib.Std

type coqModuleName = 
| User_module of string
| Std_module of string
[@@deriving sexp]



type primitiveValueAlgebraEntry = {
  pvae_coq_import : string ;
  pvae_coq_entity_name : string ;
  pvae_builtin_interface : Dsm.__ Dsm.builtinInterface ;
}

type programInfoEntry = {
  pie_coq_import : string ;
  pie_coq_entity_name : string ;
  pie_constructor : Dsm.__ -> (Dsm.__ Dsm.symbols) -> Dsm.__ -> ((Dsm.__, Dsm.__) Dsm.builtin) -> (Dsm.__, Dsm.__) Dsm.programInfo ;
  pie_table: (Dsm.string*Dsm.string) list ;
}

(* private stuff *)

let primitiveValueAlgebraEntries = Hashtbl.create 20

let programInfoEntries = Hashtbl.create 20

(* public interface *)

let add_user_primitive_value_algebra
  (primitive_value_algebra_name : string)
  (pvae : primitiveValueAlgebraEntry)
  =
  Hashtbl.add primitiveValueAlgebraEntries primitive_value_algebra_name pvae;
  ()

let add_user_program_info
  (program_info_name : string)
  (program_info_entry : programInfoEntry)
  =
  Hashtbl.add programInfoEntries program_info_name program_info_entry;
  ()


let get_primitive_value_algebra (primitive_value_algebra_name : coqModuleName) : primitiveValueAlgebraEntry =  
  match primitive_value_algebra_name with
  | Std_module name -> (
    let m = (
      match name with
      | "klike" -> Dsm.builtins_klike
      | "empty" -> Dsm.builtins_empty
      | _ -> failwith (sprintf "Unknown built-in algebra specified: '%s'" name)  
    ) in
    {
      pvae_coq_import = "Minuska.builtin."^name;
      pvae_builtin_interface = m;
      pvae_coq_entity_name = (sprintf "builtins_%s" name);
    }
  )
  | User_module name -> (
    Hashtbl.find primitiveValueAlgebraEntries name
  )

let get_pi (program_info_name : coqModuleName) : programInfoEntry
  =
  match program_info_name with
  | Std_module name ->(
    let m = (
      match name with
      | "trivial" -> Dsm.pi_trivial
      | _ -> failwith (sprintf "Unknown program info specified: '%s'" name)
    ) in
    ({ pie_constructor = (fst m); pie_table = (snd m); pie_coq_import = (sprintf "Minuska.pi.%s" name); pie_coq_entity_name = (sprintf "%s.MyProgramInfo" name)})
  )
  | User_module name -> (
      Hashtbl.find programInfoEntries name
  )
  
module Extracted = Dsm

(* EOF *)
