open Core
open Printf



let print_position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.option_program Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
      raise (Invalid_argument ("Lexing problem at " ^ (print_position lexbuf) ^ ": " ^ msg))
  | Parser.Error ->
      raise (Invalid_argument ("Parsing problem at " ^ (print_position lexbuf) ^ "."))


let rec convert_commands (cs : Syntax.command list) : Libminuska.Syntax.groundterm =
  match cs with
  | [] -> raise (Invalid_argument ("Empty command sequence"))
  | c::[] -> (convert_command c)
  | c1::c2::cs2 -> `GTerm(`Id "seq", [(convert_command c1);(convert_commands (c2::cs2))])
and convert_command (ast : Syntax.command) : Libminuska.Syntax.groundterm =
  match ast with
  | `CmdAssign (x,e) -> `GTerm (`Id "assign", [(convert_id x); (convert_aexp e)])
  | `CmdIf (b, cs1, cs2) -> `GTerm (`Id "ite", [(convert_bexp b); (convert_commands cs1); (convert_commands cs2)])
  | `CmdWhile (b, cs) -> `GTerm (`Id "while", [(convert_bexp b); (convert_commands cs)])
  | `CmdExpr e -> convert_aexp e
and convert_id (x : Syntax.id) : Libminuska.Syntax.groundterm =
  match x with
  | `Id s -> `GTerm (`Id "var", [(`GTb (`BuiltinString s))])
and convert_aexp (e : Syntax.aexpr) : Libminuska.Syntax.groundterm =
  match e with
  | `AExprInt n -> (`GTb (`BuiltinInt n))
  | `AExprVar x -> (convert_id x)
  | `AExprPlus (a, b) -> `GTerm(`Id "plus", [(convert_aexp a);(convert_aexp b)])
  | `AExprMinus (a, b) -> `GTerm(`Id "minus", [(convert_aexp a);(convert_aexp b)])
and convert_bexp (e : Syntax.bexpr) : Libminuska.Syntax.groundterm =
  match e with
  | `BExprBool b -> `GTb (`BuiltinBool b)
  | `BExprNeg e2 -> `GTerm(`Id "neg", [(convert_bexp e2)])
  | `BExprAnd (e1,e2) -> `GTerm(`Id "and", [(convert_bexp e1); (convert_bexp e2)])
  | `BExprOr (e1,e2) -> `GTerm(`Id "or", [(convert_bexp e1); (convert_bexp e2)])
  | `BExprEq (e1,e2) -> `GTerm(`Id "eq", [(convert_aexp e1); (convert_aexp e2)])
  | `BExprLe (e1,e2) -> `GTerm(`Id "le", [(convert_aexp e1); (convert_aexp e2)])
  | `BExprLt (e1,e2) -> `GTerm(`Id "lt", [(convert_aexp e1); (convert_aexp e2)])

let parse (lexbuf : Lexing.lexbuf) : Libminuska.Syntax.groundterm =
  match parse_with_error lexbuf with
  | Some value -> convert_commands value
  | None -> raise (Invalid_argument "Empty file?")
