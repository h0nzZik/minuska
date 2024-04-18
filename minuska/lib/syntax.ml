type token =
  | ID of string
  | VAR of string
  | INT of int
  | KEYWORD_VALUE
  | KEYWORD_STRICTNESS
  | KEYWORD_RULE
  | KEYWORD_FRAMES
  | KEYWORD_OF_ARITY
  | KEYWORD_IN
  | KEYWORD_WHERE
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

type vari = [ `Var of string ]

type pattern = 
  [ `PVar of vari
  | `PTerm of (id*(pattern list))
  ]

type groundterm = [ `GTerm of (id*(groundterm list)) ]

type expr =
  [ `EVar of vari
  | `EGround of groundterm
  | `ECall of (id*(expr list)) 
  ]

type exprterm =
  [ `EExpr of expr
  | `ETerm of (id*(exprterm list))
  ]

type rule = 
  {
    frame : id option ;
    name : string ;
    lhs : pattern ;
    rhs : exprterm ;
    cond : expr ;
  }

type framedecl =
  {
    name : id ;
    var : vari ;
    pat : pattern ;
  }

type strictdecl =
  {
    symbol : id ;
    arity : int ;
    strict_places : int list ;
  }

type definition =
  {
    value      : (vari*expr) ;
    frames     : (framedecl list) ;
    strictness : (strictdecl list) ;
    rules      : (rule list) ;
  }
