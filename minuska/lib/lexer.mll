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
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | '('          { BRACKET_ROUND_LEFT }
  | ')'          { BRACKET_ROUND_RIGHT }
  | '['          { BRACKET_SQUARE_LEFT }
  | ']'          { BRACKET_SQUARE_RIGHT }
  | "@value"      { KEYWORD_VALUE }
  | "@strictness" { KEYWORD_STRICTNESS }
  | "@frames"       { KEYWORD_FRAMES }
  | "@rule"       { KEYWORD_RULE }
  | "@context"       { KEYWORD_CONTEXT }
  | "@builtin"       { KEYWORD_BUILTIN }
  | "@query"       { KEYWORD_QUERY }
  | "@true"       { KEYWORD_TRUE }
  | "@false"       { KEYWORD_FALSE }
  | "@and"       { KEYWORD_AND }
  | "@or"        { KEYWORD_OR }
  | "of_arity"         { KEYWORD_OF_ARITY }
  | "in"         { KEYWORD_IN }
  | "where"      { KEYWORD_WHERE }
  | "/"          { SLASH }
  | "=>"         { ARROW }
  (* | "\""         { QUOTE } *)
  | ";"          { SEMICOLON }
  | ":"          { COLON }
  | ':'          { COLON }
  | ','          { COMMA }
  | id           { ID (Lexing.lexeme lexbuf)  }
  | var           { VAR (Lexing.lexeme lexbuf)  }

  | _            { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof          { EOF }
(* from https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }