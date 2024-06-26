open Core
open Printf



let print_position outx lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.option_program Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)


let rec print_commands (cs : Syntax.command list) =
  match cs with
  | [] -> ""
  | c::[] -> (print_command c)
  | c1::c2::cs2 -> "seq[" ^ (print_command c1) ^ ", " ^ (print_commands (c2::cs2)) ^ "]"
and print_command (c : Syntax.command) =
  match c with
  | `CmdAssign (x,e) -> "assign[" ^ (print_var x) ^ ", " ^ (print_aexpr e) ^ "]"
  | `CmdIf (b, cs1, cs2) -> "if[" ^ (print_bexpr b) ^ ", " ^ (print_commands cs1) ^ ", " ^ (print_commands cs2) ^ "]"
  | `CmdWhile (b, cs) -> "while[" ^ (print_bexpr b) ^ ", " ^ (print_commands cs) ^ "]"
and print_var (x : Syntax.id) =
  match x with
  | `Id s -> "var[" ^ (print_string s ) ^ "]"
and print_string (x : string) =
  "(@builtin-string \"" ^ x ^ "\")"
and print_int (x : int) =
  "(@builtin-int " ^ (string_of_int x) ^ ")"
and print_bool (x : bool) =
  "(@builtin-bool " ^ (string_of_bool x) ^ ")"
and print_aexpr (e : Syntax.aexpr) =
  match e with
  | `AExprInt n -> print_int n
  | `AExprVar x -> "var[" ^ (print_var x) ^ "]" 
  | `AExprPlus (a, b) -> "plus[" ^ (print_aexpr a) ^ ", " ^ (print_aexpr b) ^ "]"
  | `AExprMinus (a, b) -> "minus[" ^ (print_aexpr a) ^ ", " ^ (print_aexpr b) ^ "]"
and print_bexpr (e : Syntax.bexpr) =
  match e with
  | `BExprBool b -> print_bool b
  | `BExprNeg e2 -> "neg[" ^ (print_bexpr e2) ^ "]"
  | `BExprAnd (e1,e2) -> "and[" ^ (print_bexpr e1) ^ ", " ^ (print_bexpr e2) ^ "]"
  | `BExprOr (e1,e2) -> "or[" ^ (print_bexpr e1) ^ ", " ^ (print_bexpr e2) ^ "]"
  | `BExprEq (e1,e2) -> "eq[" ^ (print_aexpr e1) ^ ", " ^ (print_aexpr e2) ^ "]"
  | `BExprLe (e1,e2) -> "le[" ^ (print_aexpr e1) ^ ", " ^ (print_aexpr e2) ^ "]"
  | `BExprLt (e1,e2) -> "lt[" ^ (print_aexpr e1) ^ ", " ^ (print_aexpr e2) ^ "]"


let print_ast (ast : Syntax.command list) oux =
    let s = print_commands ast in
    fprintf oux "%s" s;
    ()

let parse_and_print lexbuf oux =
  match parse_with_error lexbuf with
  | Some value ->
    print_ast value oux
  | None ->
    fprintf stderr "empty file\n";
    ()


let append_ast input_filename output_channel =
  let inx = In_channel.create input_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_and_print lexbuf output_channel;
  In_channel.close inx;
  ()


let do_parse input_filename output_filename () =
  let oux = Out_channel.create output_filename in
  append_ast input_filename oux;
  Out_channel.close oux;
  ()


let command =
  Command.basic
    ~summary:"Generate a Minuska-compatible parser for the IMP programming language"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        input_filename = anon (("program.imp" %: Filename_unix.arg_type)) and
        output_filename = anon (("program.ast" %: Filename_unix.arg_type))
     in
     fun () -> do_parse input_filename output_filename ())

let () = Command_unix.run ~version:"0.1" command