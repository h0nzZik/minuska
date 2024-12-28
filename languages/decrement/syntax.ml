type token =
  | INT of int
  | BRACKET_ROUND_LEFT
  | BRACKET_ROUND_RIGHT
  | OP_ZERO
  | OP_SUCC
  | EOF

type term =
  [ `Zero of unit
  | `Succ of term
  ]
