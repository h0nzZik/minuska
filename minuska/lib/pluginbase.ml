open Printf
open Sexplib.Std

type builtin =
  [ `BuiltinInt of int
  | `BuiltinString of string
  | `BuiltinBool of bool
  ]

type coqModuleName = 
| User_module of string
| Std_module of string
[@@deriving sexp]



type primitiveValueAlgebraEntry = {
  pvae_coq_import : string ;
  pvae_coq_entity_name : string ;
  pvae_builtin_interface : Dsm.__ Dsm.builtinInterface ;
  pvae_builtin_quote : builtin -> string ;
  pvae_builtin_inject : builtin -> ((string, Dsm.__) Dsm.builtin_value) option ;
  pvae_builtin_eject : (string, Dsm.__) Dsm.builtin_value -> builtin option ;
}

type programInfoEntry = {
  pie_coq_import : string ;
  pie_coq_entity_name : string ;
  pie_constructor : Dsm.__ -> (Dsm.__ Dsm.symbols) -> Dsm.__ -> Dsm.signature -> ((Dsm.__, Dsm.__) Dsm.model) -> (Dsm.__, Dsm.__) Dsm.programInfo ;
  pie_table: (string*string) list ;
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
      pvae_builtin_quote = (fun (b : builtin) -> (
        match name with
        | "klike" -> (
           match b with
           | `BuiltinInt n -> (sprintf "(bv_Z (%d)%%Z)" n)
           | `BuiltinBool b' -> (sprintf "(bv_bool %s)" (if b' then "true" else "false"))
           | `BuiltinString s -> (sprintf "(bv_str (\"%s\")%%str)" s)
        )
        | _ -> failwith (sprintf "Cannot represent given builtin using module '%s'" name)
      ));
      pvae_builtin_inject = (fun (b : builtin) -> (
        Stdlib.Obj.magic (
        match name with
        | "klike" -> (
          match b with
          | `BuiltinInt n -> (Option.some (Dsm.Bv_Z (Z.of_int n)))
          | `BuiltinBool b' -> (Option.some (Dsm.Bv_bool b'))
          | `BuiltinString s -> (Option.some (Dsm.Bv_str ((*Stringutils.explode*) s)))
        )
        | _ -> failwith (sprintf "Cannot represent given builtin using module '%s'" name)
      )));
      pvae_builtin_eject = (fun b -> (match (Stdlib.Obj.magic b) with
        | Dsm.Bv_Z z -> (Option.some (`BuiltinInt (Z.to_int z)))
        | Dsm.Bv_bool b' -> (Option.some (`BuiltinBool b'))
        | Dsm.Bv_str s -> (Option.some (`BuiltinString ((*Stringutils.implode*) s)))
      ));
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
