let main () =
  Libminuska.Miskeleton.main
    Internal.chosen_builtins
    Transform.parse
    Internal.lang_interpreter
    Internal.lang_interpreter_ext
    Internal.lang_debug_info
  
let _ = main ()
