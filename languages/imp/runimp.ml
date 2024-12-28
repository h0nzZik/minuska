open Core
open Printf

let main () =
  let iface = Imp.Internal.chosen_builtins in
  Libminuska.Miskeleton.main
    iface
    (Imp.Transform.parse)
    (Libminuska.Miskeleton.wrap_interpreter iface Imp.Internal.lang_interpreter)
    (Libminuska.Miskeleton.wrap_interpreter_ext iface Imp.Internal.lang_interpreter_ext)
    (Imp.Internal.lang_debug_info)
  
let _ = main ()
