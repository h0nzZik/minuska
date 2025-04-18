
open Core
open Printf

let main () =
  Libminuska.Miskeleton.main
    (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("(User_module mybuiltins)"))))
    Internal.chosen_builtins
    (fun _ -> failwith "Parser not implemented.")
    Internal.lang_interpreter
    Internal.lang_interpreter_ext
    Internal.lang_debug_info
  
let _ = main ()
    
