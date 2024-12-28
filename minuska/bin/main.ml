open Core
open Printf
open Sexplib.Std

open Libminuska
module Syntax = Libminuska.Syntax

type coqModule = 
  | User_module of string
  | Std_module of string
  [@@deriving sexp]

type languagedescr = {
  language           : string      ;
  semantics          : string      ;
  static_model : string ;
  program_info : coqModule ;
} [@@deriving sexp]

type builtins_map_t = (string, string, String.comparator_witness) Map.t ;;
type query_map_t = (string, string, String.comparator_witness) Map.t ;;

let get_pi (m : coqModule) =
  match m with
  | Std_module name ->(
    match name with
    | "trivial" -> Libminuska.Extracted.pi_trivial
    | _ -> failwith "Unknown program info specified"
    )
  | User_module _ -> (
    failwith "User-provided program infos are not supported yet"
  )

let get_iface (static_model : string) =  
  match static_model with
  | "klike" -> Libminuska.Extracted.builtins_klike
  | "empty" -> Libminuska.Extracted.builtins_empty
  | _ -> failwith "Unknown static model specified"

let transform_map m =
  let binding = List.map ~f:(fun p -> (Stringutils.implode (fst p), Stringutils.implode (snd p))) m in
  let m2 = Map.of_alist_exn (module String) binding in
  m2

let get_builtins_map (static_model : string) : builtins_map_t =
  let builtins_binding_coq = (get_iface static_model).bi_bindings in
  let builtins_binding = List.map ~f:(fun p -> (Stringutils.implode (fst p), Stringutils.implode (snd p))) builtins_binding_coq in
  let builtins_map : builtins_map_t = Map.of_alist_exn (module String) builtins_binding in
  builtins_map

let coqc_command = "coqc" ;;
(* let ocamlfind_command = "ocamlfind" ;; *)
(* let minuska_contrib_dir = "/coq/user-contrib/Minuska" ;; *)

(* let libdir = (Filename_unix.realpath (Filename.dirname (Filename_unix.realpath (Sys_unix.executable_name)) ^ "/../lib")) ;;
let minuska_dir = libdir ^ minuska_contrib_dir ;; *)

let minuska_dir = "/usr/lib/coq/user-contrib/Minuska" ;;

let parse_and_print
  (iface : 'a Extracted.builtinInterface)
  (builtins_map : builtins_map_t)
  (query_map : query_map_t)
  (name_of_builtins : string) (name_of_pi : string) lexbuf oux =
  match Miparse.parse_definition_with_error lexbuf with
  | Some value ->
    Micoqprint.print_definition iface builtins_map query_map name_of_builtins name_of_pi value oux
  | None -> ()


let append_definition
  (iface : 'a Extracted.builtinInterface)
  (builtins_map : builtins_map_t)
  (query_map : query_map_t)
  (name_of_builtins : string)
  (name_of_pi : string)
  input_filename
  output_channel
  =
  In_channel.with_file input_filename ~f:(fun inx ->
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
    parse_and_print iface builtins_map query_map name_of_builtins name_of_pi lexbuf output_channel;  
  );
  fprintf output_channel "%s\n" {|Definition T := Eval vm_compute in (to_theory Act (process_declarations Act default_act mybeta my_program_info Lang_Decls)). |};
  fprintf output_channel "%s\n" {|Definition lang_interpreter (*: (StepT my_program_info)*) := global_naive_interpreter my_program_info (fst T).|};
  fprintf output_channel "%s\n" {|Definition lang_interpreter_ext (*: (StepT_ext my_program_info)*) := global_naive_interpreter_ext my_program_info (fst T).|};
  fprintf output_channel "%s\n" {|Definition lang_debug_info : list string := (snd T).|};
  fprintf output_channel "%s\n" {|
    (* This lemma asserts well-formedness of the definition *)
    Lemma language_well_formed: isSome(RewritingTheory2_wf_heuristics (fst T)).
    Proof.
      (* This is the main syntactic check. If this fails, the semantics contain a bad rule. *) ltac1:(compute_done).
    Qed.
    (* This lemma asserts soundness of the generated interpreter. *)
    (* Unfortunately, we cannot rely on the extraction here.
    Lemma interp_sound:
        Interpreter_sound'
        (fst T)
        lang_interpreter
    .
    Proof.
        apply @global_naive_interpreter_sound.
        (*{ apply _. }*)
        ltac1:(assert(Htmp: isSome(RewritingTheory2_wf_heuristics (fst T)))).
        {
            apply language_well_formed.
        }
        unfold is_true, isSome in Htmp.
        destruct (RewritingTheory2_wf_heuristics (fst T)) eqn:Heq>[|inversion Htmp].
        assumption.
    Qed.
    *)
  |} ;
  ()

let wrap_init (g : Syntax.groundterm) : Syntax.groundterm =
  `GTerm ((`Id "builtin.init"), [g])

let write_gterm
  (iface : 'a Extracted.builtinInterface)
  (name_of_builtins : string)
  (name_of_pi : string)
  lexbuf outname =
  match Miparse.parse_groundterm_with_error lexbuf with
  | Some gt ->
    Out_channel.with_file outname ~f:(fun oux ->
      fprintf oux "%s" {|
      From Minuska Require Export
        prelude
        default_everything
        pval_ocaml_binding
      .
      From Minuska Require Import
        builtin.empty
        builtin.klike
        (* pi.trivial *)
      .
      |};
      fprintf oux "Definition mybeta := (bi_beta MyUnit builtins_%s).\n" name_of_builtins;
      fprintf oux "#[global] Existing Instance mybeta.\n";
      fprintf oux "Definition my_program_info := %s.MyProgramInfo.\n" name_of_pi;
      fprintf oux "Definition mysigma : StaticModel := (default_everything.DSM my_program_info).\n";
      fprintf oux "Existing Instance mysigma.\n";
      fprintf oux "%s" {|
        Definition given_groundterm := 
      |};
      Micoqprint.print_groundterm oux iface name_of_builtins (wrap_init gt);
      fprintf oux " .\n";
    );
    ()
  | None -> ()



let run l =
  let _ = fprintf stderr "> %s\n" (String.concat l) in
  Sys_unix.command (String.concat l)

let generate_interpreter_coq_internal (cfg : languagedescr) input_filename (output_coq : string) =
  let iface = (get_iface cfg.static_model) in
  let builtins_map = (get_builtins_map (cfg.static_model)) in
  let name_of_builtins = cfg.static_model in
  let name_of_pi = (
    match cfg.program_info with
    | User_module _ -> failwith "User 'program info' modules are not supported yet"
    | Std_module name -> name
  ) in
  let pi = get_pi cfg.program_info in
  let query_map = transform_map (snd pi) in
  (* create coqfile *)
  Out_channel.with_file output_coq ~f:(fun oux_coqfile ->
    append_definition iface builtins_map query_map name_of_builtins name_of_pi input_filename oux_coqfile;
    fprintf oux_coqfile "Definition chosen_builtins := builtins_%s.\n" name_of_builtins;
    ()
  )

let generate_interpreter_ml_internal (cfg : languagedescr) input_filename (output_ml : string) =
  let mldir = (Filename_unix.temp_dir "langdef" ".minuska") in
  let coqfile = Filename.concat mldir "interpreter.v" in
  let mlfile = Filename.concat mldir "interpreter.ml" in
  let _ = generate_interpreter_coq_internal cfg input_filename coqfile in
  (* append to coqfile *)
  Out_channel.with_file coqfile ~append:(true) ~f:(fun oux_coqfile ->
    fprintf oux_coqfile "%s" {|
      Require Import Ascii.
      Extract Inductive string => "Libminuska.Extracted.string" [ "Libminuska.Extracted.EmptyString" "Libminuska.Extracted.String" ].
      Extract Inductive ascii => "Libminuska.Extracted.ascii" [ "Libminuska.Extracted.Ascii" ].
      Extract Inductive RewritingRule2 => "Libminuska.Extracted.rewritingRule2" [  "(fun (a, b, c, d) -> { Libminuska.Extracted.r_from = a; Libminuska.Extracted.r_to = b; Libminuska.Extracted.r_scs = c; Libminuska.Extracted.r_act = d; })" ].
      Extract Inductive Act => "Libminuska.Extracted.act" [ "Libminuska.Extracted.Default_act" "Libminuska.Extracted.Invisible_act" ].
      Extract Inductive TermOver' => "Libminuska.Extracted.termOver'" [ "Libminuska.Extracted.T_over" "Libminuska.Extracted.T_term" ].
      Extract Constant TermOver "'a" => "'a Libminuska.Extracted.termOver".
      Extract Inductive BuiltinInterface => "Libminuska.Extracted.builtinInterface" [ "(fun (a, b, c, d, e, f) -> { Libminuska.Extracted.bi_beta = a; Libminuska.Extracted.bi_bindings = b; Libminuska.Extracted.bi_inject_bool = c; Libminuska.Extracted.bi_inject_Z = d; Libminuska.Extracted.bi_inject_string = e; Libminuska.Extracted.bi_eject = f; })" ].
      Extract Constant bi_beta => "(fun x -> x.Libminuska.Extracted.bi_beta)".
      Extract Inductive Builtin => "Libminuska.Extracted.builtin" [  "Libminuska.Extracted.mkBuiltin" ].
      Extract Constant builtins_empty => "Libminuska.Extracted.builtins_empty".
      Extract Constant builtins_klike => "Libminuska.Extracted.builtins_klike".
      Extract Constant pi_trivial => "Libminuska.Extracted.pi_trivial".
      Extract Constant DSM => "Libminuska.Extracted.dSM".
      Extract Constant GT => "Libminuska.Extracted.gT".
      Extract Constant gt_term => "Libminuska.Extracted.gt_term".
      Extract Constant gt_over => "Libminuska.Extracted.gt_over".
      Extract Inductive ProgramInfo => "Libminuska.Extracted.programInfo" [ "(fun (b, d) -> { Libminuska.Extracted.querySymbol_eqdec = b; Libminuska.Extracted.pi_symbol_interp = d; })" ].
      Extract Constant program_info => "Libminuska.Extracted.programInfo".
      Extract Constant global_naive_interpreter => "Libminuska.Extracted.global_naive_interpreter".
      Extract Constant global_naive_interpreter_ext => "Libminuska.Extracted.global_naive_interpreter_ext".
    |};
    fprintf oux_coqfile "Set Extraction Output Directory \"%s\".\n" (mldir);
    fprintf oux_coqfile "Extraction \"%s\" lang_interpreter lang_interpreter_ext lang_debug_info chosen_builtins.\n" ("interpreter.ml");
  );
  (* extract coq into ocaml *)
  let rv = run ["cd "; mldir; "; "; coqc_command; " "; "-R "; minuska_dir; " Minuska "; coqfile; " > coq_log.txt"] in
  (if rv <> 0 then failwith ("`"^ coqc_command ^ "` failed. Is the language definition well-formed?"));
  let _ = run ["cp '"; mlfile; "' '"; output_ml; "'"] in
  let _ = run ["cp '"; mlfile; "i' '"; output_ml; "i'"] in
  ()

let transform_groundterm
  (iface : 'a Extracted.builtinInterface)
  (name_of_builtins : string)
  (name_of_pi : string)
  input_fname output_fname () =
  In_channel.with_file input_fname ~f:(fun inx ->
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_fname };
    write_gterm iface name_of_builtins name_of_pi lexbuf output_fname;  
  );
  ()

let generate_interpreter_ml scm_filename (out_ml_file : string) =
  let dir = Filename.to_absolute_exn ~relative_to:(Core_unix.getcwd ()) (Filename.dirname scm_filename) in
  let cfg = Sexp.load_sexp scm_filename |> languagedescr_of_sexp in
  let mfile = if (Filename.is_relative cfg.semantics) then (Filename.concat dir cfg.semantics) else (cfg.semantics) in
  generate_interpreter_ml_internal cfg mfile out_ml_file;
  ()

let generate_interpreter_coq scm_filename (out_coq_file : string) =
  let dir = Filename.to_absolute_exn ~relative_to:(Core_unix.getcwd ()) (Filename.dirname scm_filename) in
  let cfg = Sexp.load_sexp scm_filename |> languagedescr_of_sexp in
  let mfile = if (Filename.is_relative cfg.semantics) then (Filename.concat dir cfg.semantics) else (cfg.semantics) in
  generate_interpreter_coq_internal cfg mfile out_coq_file;
  ()

let initialize_project project_name name_of_builtins name_of_program_info =
  let _ = Sys_unix.command (sprintf "dune init project %s ." project_name) in
  Out_channel.with_file "lang.scm" ~f:(fun oux ->
    fprintf oux {|
      (
        (language %s)
        (semantics def.m)
        (static_model "%s")
        (program_info (std_module "%s"))
      )
    |} project_name name_of_builtins name_of_program_info;
  );
  Out_channel.with_file "dune" ~f:(fun oux ->
    fprintf oux {|
    (env (dev (flags (:standard -warn-error -A))))
    
    (executable
      (public_name run)
      (package %s)
      (name run)
      (libraries
          minuska
      )
      (modules run internal)
    )

    (rule
      (targets internal.ml internal.mli)
      (deps lang.scm def.m)
      (action
      (chdir %%{workspace_root}
      (run minuska generate-interpreter-ml lang.scm internal.ml)))
    )
    |} project_name
  );
  Out_channel.with_file "def.m" ~f:(fun oux ->
    fprintf oux {|
      @frames: [
        simple(X): c[builtin.cseq [X,REST]]
      ];
      @value(X): (is_true(bool.false())) ;
      @nonvalue(X): (is_true(bool.false())) ;
      @context(HOLE): c[HOLE];
      @strictness: [];

      @rule [init]: builtin.init[] => c[builtin.cseq[program.ast(), builtin.empty_cseq[]], map.empty()] where [];
      @rule/simple [plus]: plus[X,Y] => z.plus(X, Y) where [is_true(z.is(X)), is_true(z.is(Y))] ;
    |}
  );
  Out_channel.with_file "run.ml" ~f:(fun oux ->
    fprintf oux {|
      open Core
      open Printf

      let main () =
        Libminuska.Miskeleton.main
          Internal.chosen_builtins
          (fun _ -> failwith "Parser not implemented.")
          Internal.lang_interpreter
          Internal.lang_interpreter_ext
          Internal.lang_debug_info
        
      let _ = main ()
    |}
  );
  ()

let command_init =
  Command.basic
    ~summary:"Generate a Minuska project (`lang.scm`, `lang.m`, `run.ml`, `dune-project`, `dune`) in the current directory."
    ~readme:(fun () -> "TODO")
    (
      let%map_open.Command
        project_name = flag "--name" (required string) ~doc:"project name" and
        name_of_builtins = flag "--builtins" (required string) ~doc:"builtins to use" and
        name_of_program_info = flag "--program-info" (required string) ~doc:"program info to use"
      in
      fun () -> initialize_project project_name name_of_builtins name_of_program_info
    )

let command_groundterm2coq =
  Command.basic
    ~summary:"Generate a Coq (*.v) file from a ground term (e.g., a program)"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        name_of_builtins = flag "--builtins" (required string) ~doc:"builtins to use" and
        name_of_pi = flag "--program-info" (required string) ~doc:"program info to use" and
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))

     in
     fun () -> transform_groundterm (get_iface name_of_builtins) name_of_builtins name_of_pi input_filename output_filename ())

let command_generate_interpreter_coq =
  Command.basic
    ~summary:"Generate an interpreter *.v file from a Minuska project file (*.scm)"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        scm_filename = anon (("lang.scm" %: Filename_unix.arg_type)) and
        out_ml_file = anon (("lang.ml" %: Filename_unix.arg_type))
      in
      fun () -> generate_interpreter_coq scm_filename out_ml_file)

let command_generate_interpreter_ml =
  Command.basic
    ~summary:"Generate an interpreter *.ml file from a Minuska project file (*.scm)"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        scm_filename = anon (("lang.scm" %: Filename_unix.arg_type)) and
        out_ml_file = anon (("lang.ml" %: Filename_unix.arg_type))
      in
      fun () -> generate_interpreter_ml scm_filename out_ml_file)


let command_print_coqbin =
  Command.basic
    ~summary:"Prints path to Coq's bin directory"
    ~readme:(fun () -> "TODO")
    (Command.Param.return
      (fun () -> (
          if (Sys_unix.file_exists_exn coqc_command) then
            printf "%s" (Filename.dirname coqc_command)
          else (
            let _ = Sys_unix.command (String.concat ["which "; coqc_command]) in ()
          )
        ); ())
    )

let command_print_coqflags =
  Command.basic
  ~summary:"Prints coq flags"
  ~readme:(fun () -> "TODO")
  (Command.Param.return
    (fun () -> printf "%s" ("-R " ^ minuska_dir ^ " Minuska"))
  )

let command_run =
  Command.basic
    ~summary:"Run a command in a Coq-friendly environment"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        cmd = flag "--" escape ~doc:("Command to run")
      in
      fun () -> 
	let command_to_run = (match cmd with Some x -> x | None -> []) in 
        if (Sys_unix.file_exists_exn coqc_command) then
        (let _ = Sys_unix.command ((String.concat ["env PATH=\""; (Filename.dirname coqc_command); ":$PATH\" COQPATH=\""; (Filename.dirname minuska_dir); ":$COQPATH\" "]) ^ (String.concat ~sep:" " command_to_run)) in
          ()
        ) else (
          let _ = Sys_unix.command ((String.concat ["env COQPATH=\""; (Filename.dirname minuska_dir); ":$COQPATH\" "]) ^ (String.concat ~sep:" " command_to_run)) in
          ()
        )
      )
    

let command_info =
  Command.group
    ~summary:"Information about Minuska installation"
    [
      "coqbin", command_print_coqbin;
      "coqflags", command_print_coqflags;
      "run", command_run
    ]


let command =
  Command.group
    ~summary:"A verified semantic framework"
    [
      "init", command_init;
      (* "generate-interpreter", command_generate_interpreter; *)
      "generate-interpreter-ml", command_generate_interpreter_ml;
      "generate-interpreter-coq", command_generate_interpreter_coq;
      (* "compile", command_compile; *)
      (* "def2coq", command_generate; *) (* TODO replace this with something*)
      "gt2coq", command_groundterm2coq;
      "info", command_info
     ]

let () = Command_unix.run ~version:"0.6" command

