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


type coqIdent = string

type primitiveValueAlgebraEntry = {
  pvae_coq_import : coqIdent ;
  pvae_coq_entity_name : coqIdent ;
  pvae_builtin_interface : Dsm.__ Dsm.valueAlgebraInterface ;
  pvae_builtin_inject : builtin_repr -> ((string, Dsm.__) Dsm.builtin_value) option ;
  pvae_builtin_eject : (string, Dsm.__) Dsm.builtin_value -> builtin_repr option ;
  pvae_builtin_coq_quote : builtin_repr -> coqIdent
}


type hiddenAlgebraEntry = {
  hae_coq_import : coqIdent ;
  hae_coq_entity_name : coqIdent ;
  hae_interface : Dsm.__ Dsm.hiddenAlgebraInterface ;
}

type programInfoEntry = {
  pie_constructor :
    (string, Dsm.__) Dsm.programInfo ;
  pie_inject : string -> Dsm.__ option ;
}

(* private stuff *)

let primitiveValueAlgebraEntries = Hashtbl.create 20

(* public interface *)

let add_user_primitive_value_algebra
  (primitive_value_algebra_name : string)
  (pvae : primitiveValueAlgebraEntry)
  =
  Hashtbl.add primitiveValueAlgebraEntries primitive_value_algebra_name pvae;
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
      pvae_builtin_inject = (fun (b : builtin_repr) -> (
        Stdlib.Obj.magic (
        match name with
        | "klike" -> (
          match b.br_kind with
          | "int" -> (Option.some (Dsm.Bv_Z (Z.of_string (b.br_value))))
          | "bool" -> (
            match b.br_value with
            | "true" -> (Option.some (Dsm.Bv_bool true))
            | "false" -> (Option.some (Dsm.Bv_bool false))
            | _ -> failwith (sprintf "Unknown boolean value '%s': only 'true' and 'false' are allowed" b.br_value)
          )
          | "string" -> (Option.some (Dsm.Bv_str ((*Stringutils.explode*) b.br_value)))
          | _ -> failwith (sprintf "Unknown kind of builtins: '%s'" b.br_kind)
        )
        | _ -> failwith (sprintf "Cannot represent given builtin using module '%s'" name)
      )
      ));
      pvae_builtin_coq_quote = (fun (b : builtin_repr) -> (
        Stdlib.Obj.magic (
        match name with
        | "klike" -> (
          match b.br_kind with
          | "int" -> (sprintf "(bv_Z (%s)%%Z)" (b.br_value))
          | "bool" -> (
            match b.br_value with
            | "true" -> ("(bv_bool true)")
            | "false" -> ("(bv_bool false)")
            | _ -> failwith (sprintf "Unknown boolean value '%s': only 'true' and 'false' are allowed" b.br_value)
          )
          | "string" -> (sprintf "(bv_str \"%s\")" b.br_value)
          | _ -> failwith (sprintf "Unknown kind of builtins: '%s'" b.br_kind)
        )
        | _ -> failwith (sprintf "Cannot represent given builtin using module '%s'" name)
      )
      ));
      pvae_builtin_eject = (fun b -> (match (Stdlib.Obj.magic b) with
        | Dsm.Bv_Z z -> (Option.some ({br_kind="int"; br_value=(Z.to_string z);}))
        | Dsm.Bv_bool b' -> (Option.some ({br_kind="bool"; br_value=(if b' then "true" else "false");}))
        | Dsm.Bv_str s -> (Option.some (({br_kind="string"; br_value=s};)))
        | Dsm.Bv_list _ -> (Option.some {br_kind="list"; br_value="_"})
        | Dsm.Bv_pmap _ -> (Option.some {br_kind="map"; br_value="_"})
        (* | _ -> Option.none *)
      ));
    }
  )
  | User_module name -> (
    Hashtbl.find primitiveValueAlgebraEntries name
  )


let get_trivial_program_info signature builtins : programInfoEntry =
  { 
    pie_constructor = ((fst Dsm.pi_trivial) signature builtins);
    pie_inject = (fun s -> Obj.magic ((snd Dsm.pi_trivial) s));
  }

module Extracted = Dsm

(* EOF *)
