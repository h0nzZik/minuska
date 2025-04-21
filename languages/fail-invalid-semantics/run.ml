open Core
open Printf
open Libminuskapluginbase
open Pluginbase

let main () =
  Libminuska.Miskeleton.main
    Internal.chosen_builtins
    (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("(Std_module klike)"))))
    (fun _ -> failwith "Parser not implemented.")
    Internal.lang_interpreter
    Internal.lang_interpreter_ext
    Internal.lang_debug_info
  
let _ = main ()
    
