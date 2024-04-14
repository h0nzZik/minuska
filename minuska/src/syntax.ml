type token =
  | ID of string
  | VAR of string
  | INT of int
  | KEYWORD_SYMBOLS
  | KEYWORD_VALUE
  | KEYWORD_STRICTNESS
  | KEYWORD_RULE
  | KEYWORD_OF
  | KEYWORD_ARITY
  | KEYWORD_IN
  | BRACKET_ROUND_LEFT
  | BRACKET_ROUND_RIGHT
  | BRACKET_SQUARE_LEFT
  | BRACKET_SQUARE_RIGHT
  | SLASH
  | ARROW
  | SEMICOLON
  | COLON
  | COMMA
  | EOF




type id = [ `Id of string ]

type var = [ `Var of string ]

type pattern = 
  [ `PVar of var
  | `PTerm of (id*(pattern list))
  ]

type groundterm = [ `GTerm of (id*(groundterm list)) ]

type expr =
  [ `EVar of var
  | `EGround of groundterm
  | `ECall of (id*(exprterm list)) 
  ]

type exprterm =
  [ `EExpr of expr
  | `ETerm of (id*(exprterm list))
  ]

type rule = 
  {
    lhs : pattern ;
    rhs : exprterm ;
    cond : expr ;
  }

type strictdecl =
  {
    symbol : id ;
    arity : int ;
    strict_places : int list ;
  }

type definition =
  {
    symbols    : (id list);
    value      : (var*expression) ;
    strictness : (strictdecl list) ;
    rules      : (rule list) ;
  }
