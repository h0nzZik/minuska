open Core
open Printf
open Libminuskapluginbase
open Util
open Pluginbase


type ('vr, 'v, 'nv, 'hv, 'prg, 'ts, 'fs, 'ps, 'qs, 'ats, 'ms, 'hps) interpreterSkeletonI =
  {
    v_edc             : 'v Extracted.eDC ;
    hv_edc            : 'hv Extracted.eDC ;
    nv_edc            : 'nv Extracted.eDC ;
    vr_edc            : 'vr Extracted.eDC ;
    vr_inf            : 'vr Extracted.infinite ;
    ts_edc            : 'ts Extracted.eDC ;
    fs_edc            : 'fs Extracted.eDC ;
    ps_edc            : 'ps Extracted.eDC ;
    ats_edc           : 'ats Extracted.eDC ;
    ms_edc            : 'ms Extracted.eDC ;
    qs_edc            : 'qs Extracted.eDC ;
    hps_edc           : 'hps Extracted.eDC ;
    background_model  : (('v, 'hv, 'nv, 'vr, 'ts, 'fs, 'ps, 'ats, 'ms, 'qs, 'hps, 'prg) Extracted.backgroundModelOver) ;
    builtin_inject    : (builtin_repr -> 'v) ;
    builtin_eject     : ('v -> builtin_repr ) ;
    bindings          : (string -> ('ps, 'hps,'fs,'ats,'qs,'ms) Extracted.symbolInfo) ;
  }


let klike_builtin_inject (b : builtin_repr)  =
  match b.br_kind with
  | "int" -> ((Extracted.Bv_Z (Z.of_string (b.br_value))))
  | "bool" -> (
    match b.br_value with
    | "true" -> ((Extracted.Bv_bool true))
    | "false" -> ((Extracted.Bv_bool false))
    | _ -> failwith (sprintf "Unknown boolean value '%s': only 'true' and 'false' are allowed" b.br_value)
  )
  | "string" -> ((Extracted.Bv_str (b.br_value)))
  | _ -> failwith (sprintf "Unknown kind of builtins '%s' for module 'klike'" b.br_kind)

let klike_builtin_eject b : builtin_repr =
  match b with
  | Extracted.Bv_Z z -> (({br_kind="int"; br_value=(Z.to_string z);}))
  | Extracted.Bv_bool b' -> (({br_kind="bool"; br_value=(if b' then "true" else "false");}))
  | Extracted.Bv_str s -> ((({br_kind="string"; br_value=s};)))
  | Extracted.Bv_list _ -> ({br_kind="list"; br_value="_"})
  | Extracted.Bv_pmap _ -> ({br_kind="map"; br_value="_"})

let empty_builtin_inject (b : builtin_repr) =
  match b with
  | _ -> failwith (sprintf "Cannot represent given builtin using module 'empty'")

let empty_builtin_eject b : builtin_repr =
  match b with
  | _ -> failwith "This should be unreachable"


let klike_interface (*: ((,,,,,Extracted.myQuerySymbol,) interpreterSkeletonI)*) = (

  let sym_edc = (Extracted.top_string_symbols_edc) in
  let m  = (Extracted.top_builtin_klike_model sym_edc) in
  let hm = (Extracted.top_hidden_unit_model) in
  let pi = (Extracted.top_pi_trivial_pi) in
  let bs = (Extracted.combine_symbol_classifiers
    (Extracted.top_builtin_klike_bindings)
    (Extracted.top_pi_trivial_bindings)
    (Extracted.top_hidden_unit_bindings)
  ) in
  {
    v_edc = Extracted.top_builtin_klike_bv_edc Extracted.top_string_symbols_edc;
    ts_edc = Extracted.top_string_symbols_edc;
    fs_edc = Extracted.top_builtin_klike_fs_edc;
    ps_edc = Extracted.top_builtin_klike_ps_edc;
    qs_edc = Extracted.top_pi_trivial_qs_edc;
    hv_edc = Extracted.top_hidden_unit_edc;
    ats_edc = Extracted.top_hidden_unit_ats_edc;
    ms_edc = Extracted.top_hidden_unit_ms_edc;
    hps_edc = Extracted.top_hidden_unit_hps_edc;
    nv_edc = Extracted.top_nv_edc;
    vr_edc = Extracted.top_string_symbols_edc;
    vr_inf = Extracted.top_string_infinite;
    background_model = {
        value_algebra = m;
        hidden_algebra = hm;
        program_info = pi;
        nondet_gen = (fun _ -> ());
    };
    builtin_inject = klike_builtin_inject;
    builtin_eject = klike_builtin_eject;
    bindings = bs;
  }
)

let empty_interface = (
  let sym_edc = (Extracted.top_string_symbols_edc) in		       
  let m  = (Extracted.top_builtin_empty_model) in
  let hm = (Extracted.top_hidden_unit_model) in
  let pi = (Extracted.top_pi_trivial_pi) in
  let bs = (Extracted.combine_symbol_classifiers
    (Extracted.top_builtin_empty_bindings)
    (Extracted.top_pi_trivial_bindings)
    (Extracted.top_hidden_unit_bindings)
  ) in
  {
    v_edc = Extracted.top_builtin_empty_bv_edc;
    ts_edc = Extracted.top_string_symbols_edc;
    fs_edc = Extracted.top_builtin_empty_fs_edc;
    ps_edc = Extracted.top_builtin_empty_ps_edc;
    qs_edc = Extracted.top_pi_trivial_qs_edc;
    hv_edc = Extracted.top_hidden_unit_edc;
    ats_edc = Extracted.top_hidden_unit_ats_edc;
    ms_edc = Extracted.top_hidden_unit_ms_edc;
    hps_edc = Extracted.top_hidden_unit_hps_edc;
    nv_edc = Extracted.top_nv_edc;
    vr_edc = Extracted.top_string_symbols_edc;
    vr_inf = Extracted.top_string_infinite;
    background_model = {
        value_algebra = m;
        hidden_algebra = hm;
        program_info = pi;
        nondet_gen = (fun _ -> ());
    };
    builtin_inject = empty_builtin_inject;
    builtin_eject = empty_builtin_eject;
    bindings = bs;
  }
)

let rec convert_groundterm
  (builtin_inject : builtin_repr -> 'builtin)
  (g : Syntax.groundterm)
  : ((string, 'builtin2) Extracted.termOver') =
  match g with
  | `GTb b ->
    Extracted.T_over (builtin_inject b)
  | `GTerm (`Id s, gs) ->
    Extracted.T_term (s,(List.map ~f:(convert_groundterm builtin_inject) gs))

let wrap_init (g : ((string, 'builtin) Extracted.termOver')) : ((string, 'builtin) Extracted.termOver') =
  Extracted.T_term (("builtin.init"), [g])

let wrap_init0 : ((string, 'builtin) Extracted.termOver') =
  Extracted.T_term (("builtin.init"), [])
  
let rec show_groundterm
  (builtin_eject : 'builtin -> builtin_repr)
  (g : (string, 'builtin2) Extracted.termOver')
  : string =
  match g with
  | Extracted.T_over b ->
    let b'' = ((builtin_eject b)) in
    (sprintf "(@builtin:%s(\"%s\"))" b''.br_kind b''.br_value)
  | Extracted.T_term (s, gs) ->
    let ss = List.map ~f:(show_groundterm builtin_eject) gs in
    sprintf "%s %s" s (format_string_list ss)

let rec run_n_steps
  (nvgen : Z.t -> 'nv)
  (step :
    'nv ->
    (((string, 'builtin) Extracted.termOver')*'hidden_data) ->
    (((((string, 'builtin) Extracted.termOver')*'hidden_data)*'a) option)
  )
  (generate_debug : 'a list -> string)
  (rev_trace : 'a list)
  (max_depth : Z.t)
  (curr_depth : Z.t)
  (gterm : (string, 'builtin) Extracted.termOver')
  (h : 'hidden_data)
  : (Z.t*((string, 'builtin) Extracted.termOver')*(string))
  =
  if Z.geq curr_depth max_depth then (curr_depth, gterm, generate_debug (List.rev rev_trace))
  else (
    let ogterm2 = step (nvgen (curr_depth)) (gterm,h) in
    match ogterm2 with
    | None -> (curr_depth, gterm, generate_debug (List.rev rev_trace))
    | Some ((gterm2,h'),info) ->
        run_n_steps
          nvgen
          step
          generate_debug
          (info::rev_trace)
          max_depth
          (Z.add curr_depth (Z.of_int 1))
          gterm2
          h'
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
  (iface : ('vr, 'v, 'nv, 'hv, 'prg, 'ts, 'fs, 'ps, 'qs, 'ats, 'ms, 'hps) interpreterSkeletonI)
  (parser : Lexing.lexbuf -> 'prg)
  (step :
    'programT ->
    'nv ->
    (((string, 'v) Extracted.termOver')*'hv) ->
    (((string, 'v) Extracted.termOver')*'hv) option
  )
  (step_ext :
    'programT ->
    'nv ->
    (((string, 'v) Extracted.termOver')*'hv) ->
    ((((string, 'v) Extracted.termOver')*'hv)*Z.t) option
  )
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
                    (fun (nv : 'nv) (g : (((string, 'a) Extracted.termOver')*'hidden_data)) -> (match step program nv g with None -> None | Some g' -> Some (g', (Z.of_int ( -1))  ))), (
                    (fun _ -> "No debug info."),
                    []
                    )
                  )
              )
              | true -> (
                  (
                    ((step_ext program)), (
                    (fun (indices : 'myint list) : string ->
                      let names : string list = List.mapi ~f:(
                        fun (step_number : int) (rule_idx : 'myint) -> (
                          (string_of_int (step_number + 1 ))
                          ^ ": "
                          ^ (List.nth_exn lang_debug_info (Z.to_int rule_idx))
                      )) indices in
                      let log : string = List.fold_left names ~init:("") ~f:(fun acc x -> acc ^ "\n" ^ x) in
                      log
                    ),
                    []
                    )
                  )
              )
            ) in
            let actual_step : ('nv -> (((string, 'a) Extracted.termOver')*'hidden_data) -> ((((string, 'a) Extracted.termOver')*'hidden_data)*'bb) option) = (fst my_step) in
            let show_log : 'bb list -> string = (fst (snd my_step)) in
            let initial_log = (snd (snd my_step)) in
            let (initial_h : 'hidden_data) = iface.background_model.hidden_algebra.hidden_init in
            let res0 = run_n_steps iface.background_model.nondet_gen actual_step show_log initial_log (Z.of_int depth) (Z.of_int 0) wrap_init0 initial_h in
            res0
          )) in
          let res = fst res0 in
          let bench_result = snd res0 in
          if bench then (fprintf stderr "Execution wall clock time: %.02f\n" (bench_result.wall); ());
          let (actual_depth,result, info) = res in
          fprintf stdout "Taken %s steps\n" (Z.to_string actual_depth);
          (if with_trace then (fprintf stdout "Trace:\n%s\n" info; ()));
          with_output_file_or_stdout output_file (fun f_out -> 
            fprintf f_out "%s\n" (show_groundterm iface.builtin_eject result);
            ()
          );
          ()
        )
     )
    )

let main0
  (iface : ('vr, 'v, 'nv, 'hv, 'prg, 'ts, 'fs, 'ps, 'qs, 'ats, 'ms, 'hps) interpreterSkeletonI)
  (parser : Lexing.lexbuf -> 'prg)
  (step : 'prg -> 'nv -> (((string, 'v) Extracted.termOver')*'hv) -> (((string, 'v) Extracted.termOver')*'hv) option)
  (step_ext : 'prg -> 'nv -> (((string, 'v) Extracted.termOver')*'hv) -> ((((string, 'v) Extracted.termOver')*'hv)*Z.t) option)
  (lang_debug_info : string list)
  =
  Printexc.record_backtrace true;
    try (Command_unix.run ~version:"0.6" (command_run
      iface
      parser
      step
      step_ext
      lang_debug_info
      )) with
    | Stack_overflow -> (printf "Stack overflow.\n%s" (Printexc.get_backtrace ()));;

let main
      (iface : ('vr, 'v, 'nv, 'hv, 'prg, 'ts, 'fs, 'ps, 'qs, 'ats, 'ms, 'hps) interpreterSkeletonI)
      (parser : Lexing.lexbuf -> 'programT)
      langDefaults
      lang_Decls
      =
  let r (*: ('builtin, string, string, 'pred, 'hpred, 'func, 'attr, 'query, 'meth) Extracted.realization *) = {
    Extracted.realize_br = (fun (br : Extracted.builtinRepr) : 'v option ->
      let br' : builtin_repr =  { br_kind=(br.br_kind); br_value=(br.br_value); } in 
      Some ((iface.builtin_inject br'))
    );
    Extracted.string2sym = (fun (x : string) -> x);
    Extracted.string2var = (fun (x : string) -> x);
    Extracted.string2m = (fun (x : string) (*: 'meth option*) ->
      match iface.bindings x with
      | Extracted.Si_method m -> Some (m)
      | _ -> None
    );
    Extracted.string2p = (fun (x : string) (*('pred, 'hpred) Extracted.sum option*)  ->
      match iface.bindings x with
      | Extracted.Si_predicate p -> Some (Extracted.Inl (p))
      | Extracted.Si_hidden_predicate p -> Some (Extracted.Inr (p))
      | _ -> None
    );

    Extracted.string2qfa = (fun (x : string) (*(('query,'func) Extracted.sum, 'attr) Extracted.sum option*) ->
      match iface.bindings x with
      | Si_attribute a -> Some (Extracted.Inr (a))
      | Si_query q -> Some (Extracted.Inl (Extracted.Inl (q)))
      | Si_function f -> Some (Extracted.Inl (Extracted.Inr (f)))
      | _ -> None
    );
  } in
  let pre1T = Extracted.top_frontend_process_declarations Extracted.Default_label langDefaults lang_Decls in
  match pre1T with
  | Extracted.Inl(st) -> (
    match (Extracted.top_frontend_to_thy st) with
    | (thy, dbg) -> (
      match (Extracted.top_frontend_realize_thy (*iface.value_algebra*) r thy) with
      | Extracted.Inr e -> failwith (sprintf "Failed to realize the given theory: %s" e)
      | Extracted.Inl thy2 -> (
        let is_valid_dec = Extracted.top_thy_wf Extracted.string_eq_dec Extracted.string_countable thy2 in
        let _ = (match is_valid_dec with
         | true -> () (* OK *)
         | false -> printf "Warning: the given theory is not well-formed\n"; ()
        ) in
        let basic_interpreter = (
            Extracted.top_poly_interpreter
              iface.v_edc
              iface.hv_edc
              iface.nv_edc
              iface.vr_edc
              iface.vr_inf
              iface.ts_edc
              iface.fs_edc
              iface.ps_edc
              iface.ats_edc
              iface.ms_edc
              iface.qs_edc
              iface.hps_edc
              iface.background_model
              thy2
        ) in
        let ext_interpreter = (
          Extracted.top_poly_interpreter_ext
              iface.v_edc
              iface.hv_edc
              iface.nv_edc
              iface.vr_edc
              iface.vr_inf
              iface.ts_edc
              iface.fs_edc
              iface.ps_edc
              iface.ats_edc
              iface.ms_edc
              iface.qs_edc
              iface.hps_edc
              iface.background_model
              thy2
        ) in
        (main0
          iface
          parser
          basic_interpreter
          (* (wrap_interpreter iface.builtin_inject basic_interpreter) *)
          ext_interpreter
          (* (wrap_interpreter_ext iface.builtin_inject ext_interpreter) *)
          (dbg)  
        )
      )
    )
  )
  | Extracted.Inr(err) -> (
    failwith (sprintf "Err: %s" err)
  )
