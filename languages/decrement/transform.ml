open Core

let print_position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.option_term Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
      raise (Invalid_argument ("Lexing problem at " ^ (print_position lexbuf) ^ ": " ^ msg))
  | Parser.Error ->
      raise (Invalid_argument ("Parsing problem at " ^ (print_position lexbuf) ^ "."))


let rec convert_term (e : Syntax.term) : (string, string Libminuska.Extracted.klikeBuiltinValue0) Libminuska.Extracted.termOver' =
  match e with
  | `Zero () -> Libminuska.Extracted.T_term ("zero", [])
  | `Succ x -> Libminuska.Extracted.T_term ("succ", [(convert_term x)])

let parse (lexbuf : Lexing.lexbuf) : (string, string Libminuska.Extracted.klikeBuiltinValue0) Libminuska.Extracted.termOver' =
  match parse_with_error lexbuf with
  | Some value -> convert_term value
  | None -> raise (Invalid_argument "Empty file?")
