
      open Core
      open Printf

      let main () =
        Libminuska.Miskeleton.main
          Internal.chosen_builtins
          (fun _ -> failwith "Parser not implemented.")
          Internal.lang_interpreter
          Internal.lang_interpreter_ext
          Internal.lang_debug_info
        
      let _ = main ()
    