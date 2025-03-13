open Core
open Printf
open Libminuskapluginbase.Pluginbase
module Stringutils = Libminuskapluginbase.Stringutils

let __ = let rec f _ = Obj.repr f in Obj.repr f

let convert_builtin (iface : 'a Extracted.builtinInterface) (b : Syntax.builtin)  : ((string, 'a) Extracted.builtin_value)  =
  match b with
  | `BuiltinInt n -> (
    iface.bi_inject_Z (fun a -> match a with | None -> failwith "The chosen builtin model does not support integers (Z)" | Some b -> b) (Z.of_int n))
  | `BuiltinString s ->(
     iface.bi_inject_string (fun a -> match a with | None -> failwith "The chosen builtin model does not support strings" | Some b -> b) (Stringutils.explode s)
    )
  | `BuiltinBool b -> (
      iface.bi_inject_bool (fun a -> match a with | None -> failwith "The chosen builtin model does not support bools" | Some b -> b) b
    )
  | `BuiltinError -> failwith "Cannot convert `BuiltinError" (* Extracted.Bv_error *)
  | `OpaqueBuiltin -> failwith "Cannot convert unknown builtin back into Coq runtime"

let rec convert_groundterm (iface : 'a Extracted.builtinInterface) (g : Syntax.groundterm): Extracted.gT =
  match g with
  | `GTb b ->
    Extracted.gt_over iface.bi_signature iface.bi_beta (convert_builtin iface b)
  | `GTerm (`Id s, gs) ->
    Extracted.T_term ((Stringutils.explode s),(List.map ~f:(convert_groundterm iface) gs))

let wrap_init (g : Extracted.gT) : Extracted.gT =
  Extracted.T_term ((Stringutils.explode "builtin.init"), [g])

let wrap_init0 : Extracted.gT =
  Extracted.T_term ((Stringutils.explode "builtin.init"), [])
  

let convert_builtin_back (iface : 'a Extracted.builtinInterface) (b : (string, 'a) Extracted.builtin_value) : Syntax.builtin =
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

let rec convert_groundterm_back (iface : 'a Extracted.builtinInterface) (g : Extracted.gT) : Syntax.groundterm =
  match g with
  | Extracted.T_over b ->
    `GTb (convert_builtin_back iface b)
  | Extracted.T_term (s, gs) ->
    `GTerm (`Id (Stringutils.implode s),(List.map ~f:(convert_groundterm_back iface) gs))

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
  (parser : Lexing.lexbuf -> 'programT)
  (iface : 'a Extracted.builtinInterface)
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
            fprintf f_out "%s\n" (Miunparse.groundterm_to_string (convert_groundterm_back iface result));
            ()
          );
          ()
        )
     )
    )

let main0
  (iface : 'a Extracted.builtinInterface)
  (parser : Lexing.lexbuf -> 'programT)
  (step : 'programT -> Extracted.gT -> Extracted.gT option)
  (step_ext : 'programT -> Extracted.gT -> (Extracted.gT*int) option)
  (lang_debug_info : Extracted.string list)
  =
  Printexc.record_backtrace true;
    try (Command_unix.run ~version:"0.6" (command_run
      parser
      iface
      step
      step_ext
      (List.map lang_debug_info ~f:Stringutils.implode)
      )) with
    | Stack_overflow -> (printf "Stack overflow.\n%s" (Printexc.get_backtrace ()));;


let wrap_interpreter iface interpreter =
  (fun a b -> Obj.magic (interpreter (Obj.magic (convert_groundterm iface a)) (Obj.magic b)))

let wrap_interpreter_ext iface interpreter_ext =
  (fun a b -> 
    let r = Obj.magic (interpreter_ext (Obj.magic (convert_groundterm iface a)) (Obj.magic b)) in
    match r with
    | Some v ->
      Some ((fst v), (Z.to_int (snd v)))
    | None -> None
  )


let main iface parser interpreter interpreter_ext debug_info  =
  main0
    iface
    parser
    (wrap_interpreter iface interpreter)
    (wrap_interpreter_ext iface interpreter_ext)
    (debug_info)
