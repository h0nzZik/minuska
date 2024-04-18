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
let var = ['A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*


rule read =
  parse
  | white        { read lexbuf }
  | newline  { Lexing.new_line lexbuf; read lexbuf }
  
  | '('          { BRACKET_ROUND_LEFT }
  | ')'          { BRACKET_ROUND_RIGHT }
  | '['          { BRACKET_SQUARE_LEFT }
  | ']'          { BRACKET_SQUARE_RIGHT }
  | "@value"      { KEYWORD_VALUE }
  | "@strictness" { KEYWORD_STRICTNESS }
  | "@frames"       { KEYWORD_FRAMES }
  | "@rule"       { KEYWORD_RULE }
  | "of_arity"         { KEYWORD_OF_ARITY }
  | "in"         { KEYWORD_IN }
  | "where"      { KEYWORD_WHERE }
  | "/"          { SLASH }
  | "=>"         { ARROW }
  | ";"          { SEMICOLON }
  | ":"          { COLON }
  | ':'          { COLON }
  | ','          { COMMA }

  | int          { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | id           { ID (Lexing.lexeme lexbuf)  }
  | var           { VAR (Lexing.lexeme lexbuf)  }

  | _            { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof          { EOF }
