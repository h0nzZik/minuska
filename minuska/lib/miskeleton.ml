open Core
open Printf
open Libminuskapluginbase
open Util
open Pluginbase

let klike_builtin_inject (b : builtin_repr) : string Dsm.builtinValue0 =
  match b.br_kind with
  | "int" -> ((Dsm.Bv_Z (Z.of_string (b.br_value))))
  | "bool" -> (
    match b.br_value with
    | "true" -> ((Dsm.Bv_bool true))
    | "false" -> ((Dsm.Bv_bool false))
    | _ -> failwith (sprintf "Unknown boolean value '%s': only 'true' and 'false' are allowed" b.br_value)
  )
  | "string" -> ((Dsm.Bv_str (b.br_value)))
  | _ -> failwith (sprintf "Unknown kind of builtins '%s' for module 'klike'" b.br_kind)

let klike_builtin_eject (b : string Dsm.builtinValue0) : builtin_repr =
  match b with
  | Dsm.Bv_Z z -> (({br_kind="int"; br_value=(Z.to_string z);}))
  | Dsm.Bv_bool b' -> (({br_kind="bool"; br_value=(if b' then "true" else "false");}))
  | Dsm.Bv_str s -> ((({br_kind="string"; br_value=s};)))
  | Dsm.Bv_list _ -> ({br_kind="list"; br_value="_"})
  | Dsm.Bv_pmap _ -> ({br_kind="map"; br_value="_"})


let klike_builtin_coq_quote (b : builtin_repr) : string = 
  match b.br_kind with
  | "int" -> (sprintf "(bv_Z (%s)%%Z)" (b.br_value))
  | "bool" -> (
    match b.br_value with
    | "true" -> ("(bv_bool true)")
    | "false" -> ("(bv_bool false)")
    | _ -> failwith (sprintf "Unknown boolean value '%s': only 'true' and 'false' are allowed" b.br_value)
  )
  | "string" -> (sprintf "(bv_str \"%s\")" b.br_value)

let empty_builtin_coq_quote (b : builtin_repr) : Dsm.emptyset =
  failwith (sprintf "Cannot represent given builtin using module 'empty'")

let empty_builtin_inject (b : builtin_repr) : Dsm.emptyset =
  match b with
  | _ -> failwith (sprintf "Cannot represent given builtin using module 'empty'")

let empty_builtin_eject (b : Dsm.emptyset) : builtin_repr =
  match b with
  | _ -> failwith "This should be unreachable"

let rec convert_groundterm
  (builtin_inject : builtin_repr -> 'builtin)
  (g : Syntax.groundterm)
  : ((string, 'builtin) Extracted.termOver') =
  match g with
  | `GTb b ->
    Extracted.T_over (builtin_inject b)
  | `GTerm (`Id s, gs) ->
    Extracted.T_term (s,(List.map ~f:(convert_groundterm builtin_inject) gs))

let wrap_init (g : ((string, 'builtin) Extracted.termOver')) : ((string, 'builtin) Extracted.termOver') =
  Extracted.T_term (("builtin.init"), [g])

let wrap_init0 : ((string, 'builtin) Extracted.termOver') =
  Extracted.T_term (("builtin.init"), [])
  
let rec groundterm_coq_quote
  (builtin_eject : 'builtin -> builtin_repr)
  (g : Extracted.gT)
  : string =
  match g with
  | Extracted.T_over b ->
    let b'' = ((builtin_eject b)) in
    (sprintf "(@builtin:%s(\"%s\"))" b''.br_kind b''.br_value)
  | Extracted.T_term (s, gs) ->
    let ss = List.map ~f:(groundterm_coq_quote builtin_eject) gs in
    sprintf "%s %s" s (format_string_list ss)

let rec run_n_steps
  (step : Extracted.gT -> (Extracted.gT*'a) option)
  (generate_debug : 'a list -> string)
  (rev_trace : 'a list)
  (max_depth : int)
  (curr_depth : int)
  gterm
  =
  if curr_depth >= max_depth then (curr_depth, gterm, generate_debug (List.rev rev_trace))
  else (
    let ogterm2 = step gterm in
    match ogterm2 with
    | None -> (curr_depth, gterm, generate_debug (List.rev rev_trace))
    | Some (gterm2,info) ->
        run_n_steps
          step
          generate_debug
          (info::rev_trace)
          max_depth
          (curr_depth + 1)
          gterm2
  )

let with_bench (f : unit -> 'a) =
  let t0 = Benchmark.make 0L in
  let r = f () in
  let b = Benchmark.sub (Benchmark.make 0L) t0 in
  (r,b)
(* 
let och_with_open_text (name : string) (f : Out_channel.t -> 'a) =
  let oux = Out_channel.open_text in
  try (f oux) with *)

let with_output_file_or_stdout (fname : string option) (f : Out_channel.t -> 'a) =
  match fname with
  | Some name -> Out_channel.with_file name ~f:(f)
  | None -> f stdout

let command_run
  (builtin_inject : builtin_repr -> 'builtin)
  (builtin_eject : 'builtin -> builtin_repr )
  (parser : Lexing.lexbuf -> 'programT)
  (step : 'programT -> Extracted.gT -> Extracted.gT option)
  (step_ext : 'programT -> Extracted.gT -> (Extracted.gT*int) option)
  (lang_debug_info : string list)
  =
  Command.basic
    ~summary:"An interpreter"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        program_name = anon (("program" %: Filename_unix.arg_type)) and
        depth = flag "--depth" (required int) ~doc:"maximal number of steps to execute" and
        bench = flag "--bench" (no_arg) ~doc:"measure the time to parse and execute the program" and
        output_file = flag "--output-file" (optional string) ~doc:"filename to put the final configuration to" and
        with_trace = flag "--trace" (no_arg) ~doc:"Trace execution steps"
     in
     (
      fun () ->
        In_channel.with_file program_name ~f:(fun f_in ->
          let lexbuf = Lexing.from_channel f_in in
          lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = program_name };
          let program = parser lexbuf in
          let res0 = with_bench (fun () -> (
            let my_step = (
              match with_trace with
              | false -> (
                  (
                    (fun g -> (match step program g with None -> None | Some g' -> Some (g', -1))), (
                    (fun _ -> "No debug info."),
                    []
                    )
                  )
              )
              | true -> (
                  (
                    (step_ext program), (
                    (fun indices ->
                      let names = List.mapi ~f:(fun step_number rule_idx -> (string_of_int (step_number + 1)) ^ ": " ^ (List.nth_exn lang_debug_info rule_idx)) indices in
                      let log = List.fold_left names ~init:("") ~f:(fun acc x -> acc ^ "\n" ^ x) in
                      log
                    ),
                    []
                    )
                  )
              )
            ) in
            let res0 = run_n_steps (fst my_step) (fst (snd my_step)) (snd (snd my_step)) depth 0 wrap_init0 in
            res0
          )) in
          let res = fst res0 in
          let bench_result = snd res0 in
          if bench then (fprintf stderr "Execution wall clock time: %.02f\n" (bench_result.wall); ());
          let (actual_depth,result, info) = res in
          fprintf stdout "Taken %d steps\n" actual_depth;
          (if with_trace then (fprintf stdout "Trace:\n%s\n" info; ()));
          with_output_file_or_stdout output_file (fun f_out -> 
            fprintf f_out "%s\n" (groundterm_coq_quote builtin_eject result);
            ()
          );
          ()
        )
     )
    )

let main0
  (builtin_inject : builtin_repr -> 'builtin)
  (builtin_eject : 'builtin -> builtin_repr )
  (parser : Lexing.lexbuf -> 'programT)
  (step : 'programT -> Extracted.gT -> Extracted.gT option)
  (step_ext : 'programT -> Extracted.gT -> (Extracted.gT*int) option)
  (lang_debug_info : string list)
  =
  Printexc.record_backtrace true;
    try (Command_unix.run ~version:"0.6" (command_run
      builtin_inject
      builtin_eject
      parser
      step
      step_ext
      lang_debug_info (*(List.map lang_debug_info ~f:Stringutils.implode)*)
      )) with
    | Stack_overflow -> (printf "Stack overflow.\n%s" (Printexc.get_backtrace ()));;


let wrap_interpreter builtin_inject interpreter : 'programT -> Extracted.gT -> Extracted.gT option =
  (fun a b -> (*Stdlib.Obj.magic*) (interpreter ((*Stdlib.Obj.magic*) (convert_groundterm builtin_inject a)) (Stdlib.Obj.magic b)))

let wrap_interpreter_ext builtin_inject interpreter_ext =
  (fun a b -> 
    let r = Stdlib.Obj.magic (interpreter_ext (Stdlib.Obj.magic (convert_groundterm builtin_inject a)) (Stdlib.Obj.magic b)) in
    match r with
    | Some v ->
      Some ((fst v), (Z.to_int (snd v)))
    | None -> None
  )


let main
      (builtin_inject : builtin_repr -> 'builtin)
      (builtin_eject : 'builtin -> builtin_repr )
      (sym_info : string -> ('pred,'hpred,'func,'attr,'meth) Extracted.symbolInfo)
      (parser : Lexing.lexbuf -> 'programT)
      langDefaults
      lang_Decls
      =
  let r : Extracted.realization = {
    realize_br = (fun br ->
      let br' : builtin_repr =  { br_kind=(br.br_kind); br_value=(br.br_value); } in 
      match (builtin_inject br') with
      | None -> failwith "Cannot realize builtin"
      | Some b -> Some b
    );
    string2sym = (fun x -> Obj.magic x);
    string2var = (fun x -> Obj.magic x);
    string2p = (fun x -> x);
    string2qfa = (fun s -> match sym_info s with
    | Extracted.Si_none -> failwith (sprintf "Bad string: '%s'" s)
    | Extracted.Si_predicate p -> Some (Extracted.Inl (Extracted.Inl (p)))
    );
  } in
  let pre1T = Extracted.process_declarations Extracted.Default_label langDefaults lang_Decls in
  match pre1T with
  | Extracted.Inl(st) -> (
    match (Extracted.to_theory st) with
    | (thy, dbg) -> (
      match (Extracted.realize_thy mysigma r thy) with
      | Extracted.Inr e -> failwith (sprintf "Failed to realize the given theory: %s" e)
      | Extracted.Inl thy2 -> (
        let is_valid_dec = Extracted.rewritingTheory2_wf_dec mysigma thy2 in
        let _ = (match is_valid_dec with
         | true -> () (* OK *)
         | false -> printf "Warning: the given theory is not well-formed\n"; ()
        ) in
        let basic_interpreter = Extracted.global_naive_interpreter mysignature myhiddensignature mybeta myhiddenmodel my_program_info thy2 in
        let ext_interpreter = Extracted.global_naive_interpreter_ext mysignature myhiddensignature mybeta myhiddenmodel my_program_info thy2 in
        main0
        pvae
        (pvae.pvae_builtin_interface)
        parser
        (wrap_interpreter builtin_inject basic_interpreter)
        (wrap_interpreter_ext builtin_inject ext_interpreter)
        (dbg)  
      )
    )
  )
  | Extracted.Inr(err) -> (
    failwith (sprintf "Err: %s" err)
  )
