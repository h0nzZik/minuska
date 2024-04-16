open Core
open Printf


let rec convert_groundterm (g : Syntax.groundterm) : Dsm.gT =
  match g with
  | `GTerm (`Id s, gs) ->
    Dsm.T_term (s,(List.map ~f:convert_groundterm gs))

let parse_gt_and_print lexbuf oux step depth =
  match Miparse.parse_groundterm_with_error lexbuf with
  | Some gterm ->
    let _ = depth in
    let _ = Miprint.print_groundterm oux gterm in
    let _ = step (convert_groundterm gterm) in
    ()
  | None ->
    fprintf stderr "%s\n" "Cannot parse";
    exit (-1)


let run step input_filename depth () =
  let inx = In_channel.create input_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_gt_and_print lexbuf stdout step depth;
  In_channel.close inx;
  ()

let command_run step =
  Command.basic
    ~summary:"An interpreter"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        program = anon (("program" %: Filename_unix.arg_type)) and
        depth = anon (("depth" %: int))
     in
     fun () -> run step program depth ())

let main step =
    Command_unix.run ~version:"1.0" ~build_info:"RWO" (command_run step)

