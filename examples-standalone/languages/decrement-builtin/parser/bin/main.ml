open Core
open Printf

let print_position outx lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.option_int Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let print_int (x : int) =
  "(@builtin-int " ^ (string_of_int x) ^ ")"

let print_ast ast oux =
    let s = print_int ast in
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
    ~summary:"Generate a Minuska-compatible parser for the Decrement-builtin programming language"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        input_filename = anon (("program.decb" %: Filename_unix.arg_type)) and
        output_filename = anon (("program.ast" %: Filename_unix.arg_type))
     in
     fun () -> do_parse input_filename output_filename ())

let () = Command_unix.run ~version:"0.1" command