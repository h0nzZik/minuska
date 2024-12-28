open Core

let print_position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.option_aexpr Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
      raise (Invalid_argument ("Lexing problem at " ^ (print_position lexbuf) ^ ": " ^ msg))
  | Parser.Error ->
      raise (Invalid_argument ("Parsing problem at " ^ (print_position lexbuf) ^ "."))

let rec convert_aexp (e : Syntax.aexpr) : Libminuska.Syntax.groundterm =
  match e with
  | `AExprInt n -> (`GTb (`BuiltinInt n))
  | `AExprPlus (a, b) -> `GTerm(`Id "plus", [(convert_aexp a);(convert_aexp b)])
  | `AExprMinus (a, b) -> `GTerm(`Id "minus", [(convert_aexp a);(convert_aexp b)])
      
let parse (lexbuf : Lexing.lexbuf) : Libminuska.Syntax.groundterm =
  match parse_with_error lexbuf with
  | Some value -> convert_aexp value
  | None -> raise (Invalid_argument "Empty file?")
    