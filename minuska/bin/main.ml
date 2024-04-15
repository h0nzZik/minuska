open Core
open Printf
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.definition Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)


let print_definition def =
    let _ = def in
    printf("Hello, world\n");
    ()

let parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    print_definition value
  | None -> ()

let transform input_filename output_filename () =
  let inx = In_channel.create input_filename in
  let oux = Out_channel.create output_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_and_print lexbuf;
  Out_channel.close oux;
  In_channel.close inx


let command =
  Command.basic
    ~summary:"Generate a Coq (*.v) file from a Minuska (*.m) file"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))

     in
     fun () -> transform input_filename output_filename ())

let () = Command_unix.run ~version:"1.0" ~build_info:"RWO" command

