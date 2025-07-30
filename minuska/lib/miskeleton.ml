open Core
open Printf
open Libminuskapluginbase
open Util
open Pluginbase


type ('b, 'builtin, 'pred,'hpred,'func,'attr,'query,'meth) interpreterSkeletonI =
  {
    signature         : (Extracted.signature) ;
    hidden_signature  : (Extracted.hiddenSignature) ;
    value_algebra     : ((string, 'b) Extracted.model) ;
    hidden_algebra    : ((string, 'b) Extracted.hiddenModel) ;
    program_info      : ((string, 'b) Extracted.programInfo) ;
    static_model      : (Extracted.staticModel) ;
    builtin_inject    : (builtin_repr -> 'builtin) ;
    builtin_eject     : ('builtin -> builtin_repr ) ;
    (* builtin_coq_quote : builtin_repr -> string ; *)
    bindings          : (string -> ('pred,'hpred,'func,'attr,'query,'meth) Extracted.symbolInfo) ;
  }


let klike_builtin_inject (b : builtin_repr) : 'string Extracted.builtinValue0 =
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

let klike_builtin_eject (b : string Extracted.builtinValue0) : builtin_repr =
  match b with
  | Extracted.Bv_Z z -> (({br_kind="int"; br_value="???"; (*br_value=(Z.to_string z);*)}))
  | Extracted.Bv_bool b' -> (({br_kind="bool"; br_value=(if b' then "true" else "false");}))
  | Extracted.Bv_str s -> ((({br_kind="string"; br_value=s};)))
  | Extracted.Bv_list _ -> ({br_kind="list"; br_value="_"})
  | Extracted.Bv_pmap _ -> ({br_kind="map"; br_value="_"})

(* 
let klike_builtin_coq_quote (b : builtin_repr) : string = 
  match b.br_kind with
  | "int" -> (sprintf "(bv_Z (%s)%%Z)" (b.br_value))
  | "bool" -> (
    match b.br_value with
    | "true" -> ("(bv_bool true)")
    | "false" -> ("(bv_bool false)")
    | _ -> failwith (sprintf "Unknown boolean value '%s': only 'true' and 'false' are allowed" b.br_value)
  )
  | "string" -> (sprintf "(bv_str \"%s\")" b.br_value) *)

(* let klike_static_model : Extracted.staticModel =  (
  let s  = (Extracted.top_builtin_klike_signature) in
  let hs = (Extracted.top_hidden_unit_signature Extracted.top_builtin_klike_signature) in
  let m  = (Extracted.top_builtin_klike_model Extracted.top_symbols_strings) in
  let hm = (Extracted.top_hidden_unit_model Extracted.top_symbols_strings s m) in
  let pi = (Extracted.top_pi_trivial_pi Extracted.top_symbols_strings s m) in
  (Extracted.top_build_static_model s hs m hm pi)
) *)

(* 
let empty_builtin_coq_quote (b : builtin_repr) : string =
  failwith (sprintf "Cannot represent given builtin using module 'empty'") *)

let empty_builtin_inject (b : builtin_repr) : Extracted.emptyset =
  match b with
  | _ -> failwith (sprintf "Cannot represent given builtin using module 'empty'")

let empty_builtin_eject (b : Extracted.emptyset) : builtin_repr =
  match b with
  | _ -> failwith "This should be unreachable"


let klike_interface (*: ((,,,,,Extracted.myQuerySymbol,) interpreterSkeletonI)*) = (
  let s  = (Extracted.top_builtin_klike_signature) in
  let hs = (Extracted.top_hidden_unit_signature Extracted.top_builtin_klike_signature) in
  let m  = (Extracted.top_builtin_klike_model Extracted.top_symbols_strings) in
  let hm = (Extracted.top_hidden_unit_model Extracted.top_symbols_strings s m) in
  let pi = (Extracted.top_pi_trivial_pi Extracted.top_symbols_strings s m) in
  let sm = (Extracted.top_build_static_model s hs m hm pi) in
  let bs = (Extracted.combine_symbol_classifiers
    (Extracted.top_builtin_klike_bindings)
    (Extracted.top_pi_trivial_bindings)
    (Extracted.top_hidden_unit_bindings)
  ) in
  {
    signature = s ;
    hidden_signature = hs;
    value_algebra = m;
    hidden_algebra = hm;
    program_info = pi;
    static_model = sm;
    builtin_inject = klike_builtin_inject;
    builtin_eject = klike_builtin_eject;
    (* builtin_coq_quote = klike_builtin_coq_quote; *)
    bindings = bs;
  }
)
(* 
let empty_static_model : Extracted.staticModel =  (
  let s  = (Extracted.top_builtin_empty_signature) in
  let hs = (Extracted.top_hidden_unit_signature Extracted.top_builtin_empty_signature) in
  let m  = (Extracted.top_builtin_empty_model Extracted.top_symbols_strings) in
  let hm = (Extracted.top_hidden_unit_model Extracted.top_symbols_strings s m) in
  let pi = (Extracted.top_pi_trivial_pi Extracted.top_symbols_strings s m) in
  (Extracted.top_build_static_model s hs m hm pi)
) *)

let empty_interface = (
  let s  = (Extracted.top_builtin_empty_signature) in
  let hs = (Extracted.top_hidden_unit_signature Extracted.top_builtin_empty_signature) in
  let m  = (Extracted.top_builtin_empty_model Extracted.top_symbols_strings) in
  let hm = (Extracted.top_hidden_unit_model Extracted.top_symbols_strings s m) in
  let pi = (Extracted.top_pi_trivial_pi Extracted.top_symbols_strings s m) in
  let sm = (Extracted.top_build_static_model s hs m hm pi) in
  let bs = (Extracted.combine_symbol_classifiers
    (Extracted.top_builtin_empty_bindings)
    (Extracted.top_pi_trivial_bindings)
    (Extracted.top_hidden_unit_bindings)
  ) in
  {
    signature = s ;
    hidden_signature = hs;
    value_algebra = m;
    hidden_algebra = hm;
    program_info = pi;
    static_model = sm;
    builtin_inject = empty_builtin_inject;
    builtin_eject = empty_builtin_eject;
    (* builtin_coq_quote = empty_builtin_coq_quote; *)
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
  (step :
    (((string, 'builtin) Extracted.termOver')*'hidden_data) ->
    (((((string, 'builtin) Extracted.termOver')*'hidden_data)*'a) option)
  )
  (generate_debug : 'a list -> string)
  (rev_trace : 'a list)
  (max_depth : int)
  (curr_depth : int)
  (gterm : (string, 'builtin) Extracted.termOver')
  (h : 'hidden_data)
  : (int*((string, 'builtin) Extracted.termOver')*(string))
  =
  if curr_depth >= max_depth then (curr_depth, gterm, generate_debug (List.rev rev_trace))
  else (
    let ogterm2 = step (gterm,h) in
    match ogterm2 with
    | None -> (curr_depth, gterm, generate_debug (List.rev rev_trace))
    | Some ((gterm2,h'),info) ->
        run_n_steps
          step
          generate_debug
          (info::rev_trace)
          max_depth
          (curr_depth + 1)
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
  (iface : ('b, 'builtin, 'pred,'hpred,'func,'attr,'query,'meth) interpreterSkeletonI)
  (parser : Lexing.lexbuf -> 'programT)
  (step :
    'programT ->
    (((string, 'a) Extracted.termOver')*'hidden_data) ->
    (((string, 'a) Extracted.termOver')*'hidden_data) option
  )
  (step_ext :
    'programT ->
    (((string, 'a) Extracted.termOver')*'hidden_data) ->
    ((((string, 'a) Extracted.termOver')*'hidden_data')*int) option
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
                    (fun (g : (((string, 'a) Extracted.termOver')*'hidden_data)) -> (match step program g with None -> None | Some g' -> Some (g', -1))), (
                    (fun _ -> "No debug info."),
                    []
                    )
                  )
              )
              | true -> (
                  (
                    (step_ext program), (
                    (fun (indices : 'myint list) : string ->
                      let names : string list = List.mapi ~f:(fun (step_number : int) (rule_idx : 'myint) -> (string_of_int (step_number + 1)) ^ ": " ^ (List.nth_exn lang_debug_info rule_idx)) indices in
                      let log : string = List.fold_left names ~init:("") ~f:(fun acc x -> acc ^ "\n" ^ x) in
                      log
                    ),
                    []
                    )
                  )
              )
            ) in
            let actual_step : ((((string, 'a) Extracted.termOver')*'hidden_data) -> ((((string, 'a) Extracted.termOver')*'hidden_data)*'bb) option) = (fst my_step) in
            let show_log : 'bb list -> string = (fst (snd my_step)) in
            let initial_log = (snd (snd my_step)) in
            let (initial_h : 'hidden_data) = iface.hidden_algebra.hidden_init in
            let res0 = run_n_steps actual_step show_log initial_log depth 0 wrap_init0 initial_h in
            res0
          )) in
          let res = fst res0 in
          let bench_result = snd res0 in
          if bench then (fprintf stderr "Execution wall clock time: %.02f\n" (bench_result.wall); ());
          let (actual_depth,result, info) = res in
          fprintf stdout "Taken %d steps\n" actual_depth;
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
  (iface : ('b, 'builtin, 'pred,'hpred,'func,'attr,'query,'meth) interpreterSkeletonI)
  (parser : Lexing.lexbuf -> 'programT)
  (step : 'programT -> (((string, 'a) Extracted.termOver')*'hidden_data) -> (((string, 'a) Extracted.termOver')*'hidden_data) option)
  (step_ext : 'programT -> (((string, 'a) Extracted.termOver')*'hidden_data) -> ((((string, 'a) Extracted.termOver')*'hidden_data)*int) option)
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
      (iface : ('b, 'builtin, 'pred,'hpred,'func,'attr,'query,'meth) interpreterSkeletonI)
      (parser : Lexing.lexbuf -> 'programT)
      langDefaults
      lang_Decls
      =
  let r : ('builtin, string, string, 'pred, 'hpred, 'func, 'attr, 'query, 'meth) Extracted.realization = {
    realize_br = (fun (br : Extracted.builtinRepr) : 'builtin option ->
      let br' : builtin_repr =  { br_kind=(br.br_kind); br_value=(br.br_value); } in 
      Some (Obj.magic (iface.builtin_inject br'))
    );
    string2sym = (fun (x : string) -> x);
    string2var = (fun (x : string) -> x);
    string2m = (fun (x : string) (*: 'meth option*) ->
      match iface.bindings x with
      | Extracted.Si_method m -> Some (m)
      | _ -> None
    );
    string2p = (fun (x : string) (*('pred, 'hpred) Extracted.sum option*)  ->
      match iface.bindings x with
      | Extracted.Si_predicate p -> Some (Extracted.Inl (p))
      | Extracted.Si_hidden_predicate p -> Some (Extracted.Inr (p))
      | _ -> None
    );

    string2qfa = (fun (x : string) (*(('query,'func) Extracted.sum, 'attr) Extracted.sum option*) ->
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
      match (Extracted.top_frontend_realize_thy iface.static_model (Obj.magic r) thy) with
      | Extracted.Inr e -> failwith (sprintf "Failed to realize the given theory: %s" e)
      | Extracted.Inl thy2 -> (
        let is_valid_dec = Extracted.top_thy_wf iface.static_model thy2 in
        let _ = (match is_valid_dec with
         | true -> () (* OK *)
         | false -> printf "Warning: the given theory is not well-formed\n"; ()
        ) in
        let basic_interpreter : 'programT -> (((string, 'blt) Extracted.termOver')*'hidden_data) -> (((string, 'blt) Extracted.termOver')*'hidden_data) option = (
          Obj.magic (
            Extracted.top_naive_interpreter 
              iface.signature 
              iface.hidden_signature
              iface.value_algebra
              iface.hidden_algebra
              iface.program_info
              thy2 
          )
        ) in
        let ext_interpreter : 'programT -> (((string, 'blt) Extracted.termOver')*'hidden_data) -> ((((string, 'blt) Extracted.termOver')*'hidden_data)*int) option = (
          (*Obj.magic*) (Extracted.top_naive_interpreter_ext 
            iface.signature 
            iface.hidden_signature
            iface.value_algebra
            iface.hidden_algebra
            iface.program_info
            thy2
          )
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
