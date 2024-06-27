%token <int> INT

%token BRACKET_ROUND_LEFT
%token BRACKET_ROUND_RIGHT
%token OP_PLUS
%token OP_MINUS

%token EOF

%start <(Syntax.aexpr option)> option_aexpr
%{ open Syntax %}
%%

aexpr:
  | x = INT
    { `AExprInt x }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    OP_PLUS
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `AExprPlus (a1,a2) }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    OP_MINUS
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `AExprMinus (a1,a2) }
  ;

option_aexpr:
  | EOF { None }
  | e = aexpr
    EOF
    { Some e }
  ;