open Core
open Printf

let convert_builtin (iface : 'a Dsm.builtinInterface) (b : Syntax.builtin)  : ((string, 'a) Dsm.builtin_value)  =
  match b with
  | `BuiltinInt n -> (
    match (iface.bi_inject_Z (Z.of_int n)) with
      | Some v -> v
      | None -> failwith "The chosen builtin model does not support integers (Z)"
    )
  | `BuiltinString s ->(
     match (iface.bi_inject_string (Stringutils.explode s)) with
      | Some v -> v
      | None -> failwith "The chosen builtin model does not support strings"  
    )
  | `BuiltinBool b -> (
    match (iface.bi_inject_bool b) with
      | Some v -> v
      | None -> failwith "The chosen builtin model does not support bools"
    )
  | `BuiltinError -> failwith "Cannot convert `BuiltinError" (* Dsm.Bv_error *)
  | `OpaqueBuiltin -> failwith "Cannot convert unknown builtin back into Coq runtime"

let rec convert_groundterm (iface : 'a Dsm.builtinInterface) (g : Syntax.groundterm): Dsm.gT =
  match g with
  | `GTb b ->
    Dsm.gt_over iface.bi_beta (convert_builtin iface b)
  | `GTerm (`Id s, gs) ->
    Dsm.T_term ((Stringutils.explode s),(List.map ~f:(convert_groundterm iface) gs))

let wrap_init (g : Dsm.gT) : Dsm.gT =
  Dsm.T_term ((Stringutils.explode "builtin.init"), [g])

let convert_builtin_back (iface : 'a Dsm.builtinInterface) (b : (string, 'a) Dsm.builtin_value) : Syntax.builtin =
  let b2 = iface.bi_eject b in
  match b2 with
  | Some b3 -> (
    match b3 with
    | Inl x -> `BuiltinBool x
    | Inr (Inl x) -> `BuiltinInt (Z.to_int x)
    | Inr (Inr (Inl x)) -> `BuiltinString (Stringutils.implode x)
    | Inr (Inr (Inr _)) -> `BuiltinError
  )
  | None -> `OpaqueBuiltin

let rec convert_groundterm_back (iface : 'a Dsm.builtinInterface) (g : Dsm.gT) : Syntax.groundterm =
  match g with
  | Dsm.T_over b ->
    `GTb (convert_builtin_back iface b)
  | Dsm.T_term (s, gs) ->
    `GTerm (`Id (Stringutils.implode s),(List.map ~f:(convert_groundterm_back iface) gs))

let rec run_n_steps step max_depth curr_depth gterm =
  if curr_depth >= max_depth then (curr_depth, gterm)
  else (
    let ogterm2 = step gterm in
    match ogterm2 with
    | None -> (curr_depth, gterm)
    | Some gterm2 ->
        run_n_steps step max_depth (curr_depth + 1) gterm2
  )

let parse_gt_and_run (iface : 'a Dsm.builtinInterface) lexbuf oux step depth output_file bench =
  match Miparse.parse_groundterm_with_error lexbuf with
  | Some gterm ->
    (* fprintf oux "%s\n" (Miunparse.groundterm_to_string gterm); *)


    let t0 = Benchmark.make 0L in
    let cg = (convert_groundterm iface gterm) in
    let res = run_n_steps step depth 0 (wrap_init cg) in (
    let b = Benchmark.sub (Benchmark.make 0L) t0 in
    if bench then (
      fprintf stderr "Execution wall clock time: %.02f\n" (b.wall);
      (*fprintf oux "Execution times:\n";
      fprintf oux "%s\n" (Benchmark.to_string b);*)
      ()
    ) else ();
    match res with
    | (actual_depth,result) ->
      fprintf oux "Taken %d steps\n" actual_depth;
      let cfgoux = (match output_file with Some name -> Out_channel.create name | None -> oux) in
      fprintf cfgoux "%s\n" (Miunparse.groundterm_to_string (convert_groundterm_back iface result));
      (match output_file with Some _ -> () | None -> Out_channel.close cfgoux; ());
      ()
    )
  | None ->
    fprintf stderr "%s\n" "Cannot parse";
    exit (-1)


let run (iface : 'a Dsm.builtinInterface) step input_filename depth output_file bench () =
  let inx = In_channel.create input_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_gt_and_run iface lexbuf stdout step depth output_file bench;
  In_channel.close inx;
  ()


(* TODO cleanup after execution *)
let parse_first (iface : 'a Dsm.builtinInterface) bench (path_to_parser : string option) input_file (f : 'a Dsm.builtinInterface -> string -> unit) : unit =
  match path_to_parser with
  | Some s -> (
      let astdir = (Filename_unix.temp_dir "language-interpreter" ".minuska") in
      let astfile = Filename.concat astdir "input.ast" in
      let c = (s ^ " " ^ input_file ^ " " ^ astfile) in
      let t0 = Benchmark.make 0L in
      let _ = Sys_unix.command c in
      let b = Benchmark.sub (Benchmark.make 0L) t0 in
      if bench then (
        fprintf stderr "Parsing wall clock time: %.02f\n" (b.wall);
        (*fprintf oux "Execution times:\n";
        fprintf oux "%s\n" (Benchmark.to_string b);*)
        ()
      ) else ();

      (*fprintf stderr "command: %s" c;*)
      
      (f iface astfile)
    )
  | None -> (f iface input_file)

let command_run (iface : 'a Dsm.builtinInterface) (path_to_parser : string option) step =
  Command.basic
    ~summary:"An interpreter"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        program = anon (("program" %: Filename_unix.arg_type)) and
        depth = flag "--depth" (required int) ~doc:"maximal number of steps to execute" and
        bench = flag "--bench" (no_arg) ~doc:"measure the time to parse and execute the program" and
        output_file = flag "--output-file" (optional string) ~doc:"filename to put the final configuration to"
     in
     fun () -> (parse_first iface bench path_to_parser program (fun iface fname -> run iface step fname depth output_file bench ()) ))

let main (path_to_parser : string option) (iface : 'a Dsm.builtinInterface) step =
  Printexc.record_backtrace true;
    try (Command_unix.run ~version:"0.3" (command_run iface path_to_parser step)) with
    | Stack_overflow -> (printf "Stack overflow.\n%s" (Printexc.get_backtrace ()));;

