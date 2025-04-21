open Base
open Core
open Libminuskapluginbase
open Pluginbase
open Syntax

let main () =
  Libminuska.Miskeleton.main
    (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("(Std_module klike)"))))
    Internal.chosen_builtins
    Transform.parse
    Internal.lang_interpreter
    Internal.lang_interpreter_ext
    Internal.lang_debug_info
  
let _ = main ()
