open Base
open Core
open Libminuskapluginbase
open Pluginbase
open Syntax

let main () =
  Libminuska.Miskeleton.main
    (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("(Std_module klike)"))))
    (get_pi (coqModuleName_of_sexp (Sexp.of_string ("(Std_module trivial)"))))
    Transform.parse
    Internal.langDefaults
    Internal.lang_Decls
  
let _ = main ()
