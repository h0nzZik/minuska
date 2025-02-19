open Core
open Libminuskapluginbase.Pluginbase
module Stringutils = Libminuskapluginbase.Stringutils

let () =
  printf "Hello, plugin: %n\n" (Z.to_int (Myalgebra.fancy_number));
  let builtins = Myalgebra.builtins_myalg in
  add_user_primitive_value_algebra "mybuiltins" {
    pvae_builtin_interface=builtins;
    pvae_coq_entity_name="builtins_myalg";
    pvae_coq_import="Myalgebra";
  };
  (*Minuska.Pluginbase.*)
  ()
