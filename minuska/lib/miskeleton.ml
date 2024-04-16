open Core
open Printf

open Dsm

let parse_gt_and_print lexbuf oux =
  match Miparse.parse_groundterm_with_error lexbuf with
  | Some value ->
    Miprint.print_groundterm value oux
  | None -> ()


let run (step : StepT) program () =
  let inx = In_channel.create input_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_gt_and_print lexbuf stdout;
  In_channel.close inx;
  ()

let command_run (step : StepT) =
  Command.basic
    ~summary:"An interpreter"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        program = anon (("program" %: Filename_unix.arg_type)) and
        depth = anon (("depth" %: int))
     in
     fun () -> run step program ())

let main (step : StepT) =
    Command_unix.run ~version:"1.0" ~build_info:"RWO" command_run

