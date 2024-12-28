open Core
open Printf


let main () =
  let iface = (Libminuska.Extracted.builtins_klike) (*TODO we should infer this semi-automatically*) in
  Libminuska.Miskeleton.main
    iface
    (Imp.Transform.parse)
    (* (Imp.Internal.lang_interpreter) *)
    (fun a b -> Obj.magic (Imp.Internal.lang_interpreter (Obj.magic (Libminuska.Miskeleton.convert_groundterm iface a)) (Obj.magic b)))
    (fun a b -> 
      let r = Obj.magic (Imp.Internal.lang_interpreter_ext (Obj.magic (Libminuska.Miskeleton.convert_groundterm iface a)) (Obj.magic b)) in
      match r with
      | Some v ->
        Some ((fst v), (Z.to_int (snd v)))
      | None -> None
    )
    (Imp.Internal.lang_debug_info)
  
let _ = main ()
