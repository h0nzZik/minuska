type token =
  | TRUE
  | FALSE
  | ID of string
  | INT of int
  | LEFT_CURLY_BRACK
  | RIGHT_CURLY_BRACK
  | LEFT_ROUND_BRACK
  | RIGHT_ROUND_BRACK
  | COMMA
  | COLONEQ
  | EOF

type id =
  [ `Id of string
  ]

type aexpr =
  [ `IntConstant of int
  | `IntVariable of id
  | `IntPlus of (aexpr * aexpr)
  ]

type bexpr =
  [ `BoolConstant of bool
  | `BoolAnd of (bexpr * bexpr)
  | `BoolNot of bexpr
  | `Leq of (aexpr * aexpr)
  ]

type stmt =
  [ `AssignStmt of (string * expr)
  | `AExprStmt of aexpr
  | `SeqStmt of (stmt * stmt)
  | `WhileStmt of (bexpr * stmt)
  ]
