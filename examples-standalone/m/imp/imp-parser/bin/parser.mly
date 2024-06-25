%token <bool> BOOL
%token <int> INT
%token <string> ID

%token BRACKET_ROUND_LEFT
%token BRACKET_ROUND_RIGHT
%token PLUS
%token MINUS
%token AND
%token OR
%token EQ
%token LE
%token LT
%token BANG
%token COLONEQ
%token SEMICOLON
%token IF
%token THEN
%token ELSE
%token FI

%token EOF



%start <(Syntax.program option)> option_program
%{ open Syntax %}
%%

aexpr:
  | x = INT
    { `AExprInt x }
  | x = ID
    { `AExprVar x }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    PLUS
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `AExprPlus (a1,a2) }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    MINUS
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `AExprMinus (a1,a2) }
  ;

bexpr:
  | BRACKET_ROUND_LEFT
    BANG
    b = bexpr
    BRACKET_ROUND_RIGHT
    { `BExprNeg b }
  | b = BOOL
    { `BExprBool b }
  | BRACKET_ROUND_LEFT
    b1 = bexpr
    AND
    b2 = bexpr
    BRACKET_ROUND_RIGHT
    { `BExprAnd (b1,b2) }
  | BRACKET_ROUND_LEFT
    b1 = bexpr
    OR
    b2 = bexpr
    BRACKET_ROUND_RIGHT
    { `BExprOr (b1,b2) }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    EQ
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `BExprEq (b1,b2) }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    LE
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `BExprLE (b1,b2) }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    LT
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `BExprLt (b1,b2) }
  ;

command:
  | IF
    b = bexpr
    THEN
    cs1 = commands
    ELSE
    cs2 = commands
    FI
    { `CmdIf (b, cs1, cs2) }
  | x = ID
    COLONEQ
    e = aexpr
    { `CmdAssign (x, e) }

commands:
  | cs = separated_list(SEMICOLON, command)
    { cs }
  ;

program:
  | cs = commands
    { cs }
  ;

option_program:
  | EOF { None }
  | p = program
    EOF
    { Some p }
  ;