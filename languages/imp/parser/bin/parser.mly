%token <bool> BOOL
%token <int> INT
%token <string> ID

%token BRACKET_ROUND_LEFT
%token BRACKET_ROUND_RIGHT
%token OP_PLUS
%token OP_MINUS
%token OP_AND
%token OP_OR
%token OP_EQ
%token OP_LE
%token OP_LT
%token OP_BANG
%token OP_COLONEQ
%token OP_SEMICOLON
%token KEYWORD_IF
%token KEYWORD_THEN
%token KEYWORD_ELSE
%token KEYWORD_FI
%token KEYWORD_WHILE
%token KEYWORD_DO
%token KEYWORD_DONE

%token EOF



%start <((Syntax.command list) option)> option_program
%{ open Syntax %}
%%

aexpr:
  | x = INT
    { `AExprInt x }
  | x = ID
    { `AExprVar (`Id x) }
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

bexpr:
  | BRACKET_ROUND_LEFT
    OP_BANG
    b = bexpr
    BRACKET_ROUND_RIGHT
    { `BExprNeg b }
  | b = BOOL
    { `BExprBool b }
  | BRACKET_ROUND_LEFT
    b1 = bexpr
    OP_AND
    b2 = bexpr
    BRACKET_ROUND_RIGHT
    { `BExprAnd (b1,b2) }
  | BRACKET_ROUND_LEFT
    b1 = bexpr
    OP_OR
    b2 = bexpr
    BRACKET_ROUND_RIGHT
    { `BExprOr (b1,b2) }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    OP_EQ
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `BExprEq (a1,a2) }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    OP_LE
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `BExprLe (a1,a2) }
  | BRACKET_ROUND_LEFT
    a1 = aexpr
    OP_LT
    a2 = aexpr
    BRACKET_ROUND_RIGHT
    { `BExprLt (a1,a2) }
  ;

command:
  | KEYWORD_IF
    cond = bexpr
    KEYWORD_THEN
    cs1 = commands
    KEYWORD_ELSE
    cs2 = commands
    KEYWORD_FI
    { `CmdIf (cond, cs1, cs2) }
  | x = ID
    OP_COLONEQ
    e = aexpr
    { `CmdAssign (`Id x, e) }
  | KEYWORD_WHILE
    cond = bexpr
    KEYWORD_DO
    cs = commands
    KEYWORD_DONE
    { `CmdWhile (cond,cs) }
  | e = aexpr
    { `CmdExpr e }

commands:
  | cs = separated_nonempty_list(OP_SEMICOLON, command)
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