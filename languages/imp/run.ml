open Core
open Printf

let main () =
  Libminuska.Miskeleton.main
    Imp.Internal.chosen_builtins
    Imp.Transform.parse
    Imp.Internal.lang_interpreter
    Imp.Internal.lang_interpreter_ext
    Imp.Internal.lang_debug_info
  
let _ = main ()
