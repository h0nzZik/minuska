open Core
open Printf


let main () =
  Libminuska.Miskeleton.main
    (Libminuska.Extracted.builtins_klike) (*TODO we should infer this semi-automatically*)
    (Imp.Transform.parse)
    (Imp.Internal.lang_interpreter)
    (* (fun a b -> Imp.Internal.lang_interpreter (Obj.magic a) b) *)
    (fun a b -> 
      let r = Imp.Internal.lang_interpreter_ext (Obj.magic a) b in
      match r with
      | Some v ->
        Some ((fst v), (Z.to_int (snd v)))
      | None -> None
    )
    (Imp.Internal.lang_debug_info)
  
let _ = main ()
