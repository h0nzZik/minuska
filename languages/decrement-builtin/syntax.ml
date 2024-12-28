type token =
  | INT of int
  | BRACKET_ROUND_LEFT
  | BRACKET_ROUND_RIGHT
  | OP_PLUS
  | OP_MINUS
  | EOF

type aexpr =
  [ `AExprInt of int
  | `AExprPlus of (aexpr*aexpr)
  | `AExprMinus of (aexpr*aexpr)
  ]
