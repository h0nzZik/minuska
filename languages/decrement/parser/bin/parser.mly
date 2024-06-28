%token BRACKET_ROUND_LEFT
%token BRACKET_ROUND_RIGHT
%token OP_ZERO
%token OP_SUCC

%token EOF

%start <(Syntax.term option)> option_term
%{ open Syntax %}
%%

term:
  | OP_ZERO
    { `Zero () }
  | BRACKET_ROUND_LEFT
    OP_SUCC
    t = term
    BRACKET_ROUND_RIGHT
    { `Succ t }
  ;

option_term:
  | EOF { None }
  | t = term
    EOF
    { Some t }
  ;