open Core
open Libminuskapluginbase
open Pluginbase


let main () =
  Libminuska.Miskeleton.main
    (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("(Std_module klike)"))))
    Imp.Internal.chosen_builtins
    Imp.Transform.parse
    Imp.Internal.lang_interpreter
    Imp.Internal.lang_interpreter_ext
    Imp.Internal.lang_debug_info
  
let _ = main ()
