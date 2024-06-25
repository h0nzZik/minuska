type token =
  | ID of string
  | INT of int
  | BOOL of bool
  | BRACKET_ROUND_LEFT
  | BRACKET_ROUND_RIGHT
  | PLUS
  | MINUS
  | EQ
  | LE
  | LT
  | BANG
  | COLONEQ
  | SEMICOLON
  | IF
  | THEN
  | ELSE
  | FI
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
  ]
