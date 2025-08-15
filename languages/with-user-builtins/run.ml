
open Core
open Printf

let main () =
  Libminuska.Miskeleton.main
    (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("(User_module mybuiltins)"))))
    ((fun () -> failwith "not implemented yet") ())
    (get_pi (coqModuleName_of_sexp (Sexp.of_string ("(User_module trivial)"))))
    (fun _ -> failwith "Parser not implemented.")
    Internal.langDefaults
    Internal.lang_Decls
  
let _ = main ()
    
