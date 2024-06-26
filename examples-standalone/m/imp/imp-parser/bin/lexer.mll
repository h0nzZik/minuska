{
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
let id = ['a'-'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*


rule read =
  parse
  | white        { read lexbuf }
  | newline      { Lexing.new_line lexbuf; read lexbuf }
  | int          { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | '('          { BRACKET_ROUND_LEFT }
  | ')'          { BRACKET_ROUND_RIGHT }
  | "if"         { KEYWORD_IF }
  | "then"       { KEYWORD_THEN }
  | "else"       { KEYWORD_ELSE }
  | "fi"         { KEYWORD_FI }
  | "while"      { KEYWORD_WHILE }
  | "do"         { KEYWORD_DO }
  | "done"       { KEYWORD_DONE }
  | '+'          { OP_PLUS }
  | '-'          { OP_MINUS }
  | "and"        { OP_AND }
  | "or"         { OP_OR }
  | "!"          { OP_BANG }
  | "="          { OP_EQ }
  | "<="         { OP_LE }
  | "<"          { OP_LT }
  | ";"          { OP_SEMICOLON }
  | ":="         { OP_COLONEQ }

  | id           { ID (Lexing.lexeme lexbuf)  }
  | _            { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof          { EOF }
