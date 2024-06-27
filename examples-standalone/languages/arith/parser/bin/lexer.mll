{
open Parser

exception SyntaxError of string
}

let int = '-'? ['0'-'9'] ['0'-'9']*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"


rule read =
  parse
  | white        { read lexbuf }
  | newline      { Lexing.new_line lexbuf; read lexbuf }
  | int          { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | '('          { BRACKET_ROUND_LEFT }
  | ')'          { BRACKET_ROUND_RIGHT }
  | '+'          { OP_PLUS }
  | '-'          { OP_MINUS }
  | _            { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof          { EOF }
