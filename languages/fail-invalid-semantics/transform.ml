open Core

let convert_int (n : int) : Libminuska.Syntax.groundterm =
  `GTb ({br_kind="int"; br_value=(sprintf "%d" n)})
      
let parse (lexbuf : Lexing.lexbuf) : Libminuska.Syntax.groundterm =
  convert_int 42
    
