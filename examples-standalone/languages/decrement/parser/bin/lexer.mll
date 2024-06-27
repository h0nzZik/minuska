{
open Parser

exception SyntaxError of string
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"


rule read =
  parse
  | white        { read lexbuf }
  | newline      { Lexing.new_line lexbuf; read lexbuf }
  | '('          { BRACKET_ROUND_LEFT }
  | ')'          { BRACKET_ROUND_RIGHT }
  | "zero"       { OP_ZERO }
  | "succ"       { OP_SUCC }
  | _            { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof          { EOF }
