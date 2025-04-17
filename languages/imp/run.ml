open Core
open Libminuskapluginbase
open Pluginbase


let main () =
  Libminuska.Miskeleton.main
    (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("(Std_module klike)"))))
    (get_pi (coqModuleName_of_sexp (Sexp.of_string ("(Std_module trivial)"))))
    Imp.Transform.parse
    Imp.Internal.langDefaults
    Imp.Internal.lang_Decls
  
let _ = main ()
