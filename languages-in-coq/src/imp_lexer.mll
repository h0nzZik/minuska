{
open Lexing
open Parser

exception SyntaxError of string
}

let int = '-'? ['0'-'9'] ['0'-'9']*

let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*


rule read =
  parse
  | white    { read lexbuf }
  | newline  { next_line lexbuf; read lexbuf }
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | "true"   { TRUE }
  | "false"  { FALSE }
  | "and"    { AND }
  | "not"    { NOT }
  | ":="     { COLONEQ }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | '{'      { LEFT_CURLY_BRACK }
  | '}'      { RIGHT_CURLY_BRACK }
  | '('      { LEFT_ROUND_BRACK }
  | ')'      { RIGHT_ROUND_BRACK }
  | ':'      { COLON }
  | ','      { COMMA }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof      { EOF }
