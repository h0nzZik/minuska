type token =
  | ID of string
  | VAR of string
  | INT of int
  | KEYWORD_VALUE
  | KEYWORD_BUILTIN_INT
  | KEYWORD_BUILTIN_STRING
  | KEYWORD_STRICTNESS
  | KEYWORD_RULE
  | KEYWORD_FRAMES
  | KEYWORD_CONTEXT
  | KEYWORD_OF_ARITY
  | KEYWORD_IN
  | KEYWORD_TRUE
  | KEYWORD_FALSE
  | KEYWORD_AND
  | KEYWORD_OR
  | KEYWORD_WHERE
  | BRACKET_ROUND_LEFT
  | BRACKET_ROUND_RIGHT
  | BRACKET_SQUARE_LEFT
  | BRACKET_SQUARE_RIGHT
  | SLASH
  | ARROW
  | SEMICOLON
  | QUOTE
  | COLON
  | COMMA
  | EOF




type id = [ `Id of string ]

type vari = [ `Var of string ]

type pattern = 
  [ `PVar of vari
  | `PTerm of (id*(pattern list))
  ]

type builtin =
  [ `BuiltinInt of int
  | `BuiltinString of string
  | `BuiltinBool of bool
  | `BuiltinError
  | `OpaqueBuiltin
  ]

type groundterm =
  [ `GTb of builtin
  | `GTerm of (id*(groundterm list))
  ]

type expr =
  [ `EVar of vari
  | `EGround of groundterm
  | `ECall of (id*(expr list)) 
  ]

type condition =
  [ `CondAtomic of (id*(expr list)) 
  | `CondAnd of (condition*condition)
  | `CondOr of (condition*condition)
  | `CondTrue
  | `CondFalse
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
    cond : condition ;
  }

type framedecl =
  {
    name : id ;
    var : vari ;
    pat : pattern ;
  }

type contextdecl =
  {
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
    frames     : (framedecl list) ;
    value      : (vari*condition) ;
    context    : contextdecl ;
    strictness : (strictdecl list) ;
    rules      : (rule list) ;
  }
