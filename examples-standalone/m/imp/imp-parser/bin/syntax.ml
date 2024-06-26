type token =
  | ID of string
  | INT of int
  | BOOL of bool
  | BRACKET_ROUND_LEFT
  | BRACKET_ROUND_RIGHT
  | OP_PLUS
  | OP_MINUS
  | OP_EQ
  | OP_LE
  | OP_LT
  | OP_BANG
  | OP_AND
  | OP_OR
  | OP_COLONEQ
  | OP_SEMICOLON
  | KEYWORD_IF
  | KEYWORD_THEN
  | KEYWORD_ELSE
  | KEYWORD_FI
  | KEYWORD_AND
  | KEYWORD_OR
  | KEYWORD_WHILE
  | KEYWORD_DO
  | KEYWORD_DONE
  | EOF


type id = [ `Id of string ]

type aexpr =
  [ `AExprVar of id
  | `AExprInt of int
  | `AExprPlus of (aexpr*aexpr)
  | `AExprMinus of (aexpr*aexpr)
  ]

type bexpr =
  [ `BExprBool of bool
  | `BExprNeg of bexpr
  | `BExprAnd of (bexpr*bexpr)
  | `BExprOr of (bexpr*bexpr)
  | `BExprEq of (aexpr*aexpr)
  | `BExprLe of (aexpr*aexpr)
  | `BExprLt of (aexpr*aexpr)
  ]

type command =
  [ `CmdAssign of (id*aexpr)
  | `CmdIf of (bexpr*(command list)*(command list))
  | `CmdWhile of (bexpr*(command list))
  ]
