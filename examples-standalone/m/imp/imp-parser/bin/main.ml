open Core
open Printf

let do_parse input_filename output_filename () =
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