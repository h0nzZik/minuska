open Core
open Printf


let convert_builtin (b : Syntax.builtin) : (Dsm.myBuiltinType) =
  match b with
  | `BuiltinInt n -> (Dsm.Bv_Z n)

let rec convert_groundterm (g : Syntax.groundterm) : Dsm.gT =
  match g with
  | `GTb b ->
    Dsm.gt_over (convert_builtin b)
  | `GTerm (`Id s, gs) ->
    Dsm.T_term (s,(List.map ~f:convert_groundterm gs))

let convert_builtin_back (b : Dsm.myBuiltinType) : Syntax.builtin =
  match b with
  | Dsm.Bv_Z n -> `BuiltinInt n
  | _ -> failwith "Unsupported builtin value"

let rec convert_groundterm_back (g : Dsm.gT) : Syntax.groundterm =
  match g with
  | Dsm.T_over b ->
    `GTb (convert_builtin_back b)
  | Dsm.T_term ( s, gs) ->
    `GTerm (`Id s,(List.map ~f:convert_groundterm_back gs))

let rec run_n_steps step max_depth curr_depth gterm =
  if curr_depth >= max_depth then (curr_depth, gterm)
  else (
    let ogterm2 = step gterm in
    match ogterm2 with
    | None -> (curr_depth, gterm)
    | Some gterm2 ->
        run_n_steps step max_depth (curr_depth + 1) gterm2
  )

let parse_gt_and_print lexbuf oux step depth output_file =
  match Miparse.parse_groundterm_with_error lexbuf with
  | Some gterm ->
    (* fprintf oux "%s\n" (Miunparse.groundterm_to_string gterm); *)
    let cg = (convert_groundterm gterm) in
    let res = run_n_steps step depth 0 cg in (
    match res with
    | (actual_depth,result) ->
      fprintf oux "Taken %d steps\n" actual_depth;
      let cfgoux = (match output_file with Some name -> Out_channel.create name | None -> oux) in
      fprintf cfgoux "%s\n" (Miunparse.groundterm_to_string (convert_groundterm_back result));
      (match output_file with Some _ -> () | None -> Out_channel.close cfgoux; ());
      ()
    )
  | None ->
    fprintf stderr "%s\n" "Cannot parse";
    exit (-1)


let run step input_filename depth output_file () =
  let inx = In_channel.create input_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_gt_and_print lexbuf stdout step depth output_file;
  In_channel.close inx;
  ()

let command_run step =
  Command.basic
    ~summary:"An interpreter"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        program = anon (("program" %: Filename_unix.arg_type)) and
        depth = flag "--depth" (required int) ~doc:"maximal number of steps to execute" and
        output_file = flag "--output-file" (optional string) ~doc:"filename to put the final configuration to"
     in
     fun () -> run step program depth output_file ())

let main step =
    Command_unix.run ~version:"1.0" ~build_info:"RWO" (command_run step)

