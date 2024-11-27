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
  (* coq_modules        : string list ;
  ocaml_modules      : string list ; *)
  parser_exe     : string ;
  parser_builder : string option [@sexp.option];
  static_model : string ;
  program_info : coqModule ;
} [@@deriving sexp]

type builtins_map_t = (string, string, String.comparator_witness) Map.t ;;

let get_iface (static_model : string) =  
  match static_model with
  | "klike" -> Libminuska.Extracted.builtins_klike
  | "empty" -> Libminuska.Extracted.builtins_empty
  | _ -> failwith "Unknown static model specified"

let get_builtins_map (static_model : string) : builtins_map_t =
  let builtins_binding_coq = (get_iface static_model).bi_bindings in
  let builtins_binding = List.map ~f:(fun p -> (Stringutils.implode (fst p), Stringutils.implode (snd p))) builtins_binding_coq in
  let builtins_map : builtins_map_t = Map.of_alist_exn (module String) builtins_binding in
  builtins_map

let coqc_command = "coqc" ;;
let ocamlfind_command = "ocamlfind" ;;
let minuska_contrib_dir = "/coq/user-contrib/Minuska" ;;

let libdir = (Filename_unix.realpath (Filename.dirname (Filename_unix.realpath (Sys_unix.executable_name)) ^ "/../lib")) ;;
let minuska_dir = libdir ^ minuska_contrib_dir ;;

let parse_and_print (iface : 'a Extracted.builtinInterface) (builtins_map : builtins_map_t) (name_of_builtins : string) (name_of_pi : string) lexbuf oux =
  match Miparse.parse_definition_with_error lexbuf with
  | Some value ->
    Micoqprint.print_definition iface builtins_map name_of_builtins name_of_pi value oux
  | None -> ()


let append_definition (iface : 'a Extracted.builtinInterface) (builtins_map : builtins_map_t) (name_of_builtins : string) (name_of_pi : string) input_filename output_channel =
  let inx = In_channel.create input_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_and_print iface builtins_map name_of_builtins name_of_pi lexbuf output_channel;
  In_channel.close inx;
  fprintf output_channel "%s\n" {|Definition T := Eval vm_compute in (to_theory Act (process_declarations Act default_act mybeta my_program_info Lang_Decls)). |};
  fprintf output_channel "%s\n" {|Definition lang_interpreter : (StepT my_program_info) := global_naive_interpreter my_program_info (fst T).|};
  fprintf output_channel "%s\n" {|Definition lang_interpreter_ext : (StepT_ext my_program_info) := global_naive_interpreter_ext my_program_info (fst T).|};
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
(* 
let transform (iface : 'a Extracted.builtinInterface) (builtins_map : builtins_map_t) (name_of_builtins : string) (name_of_pi : string) input_filename output_filename () =
  let oux = Out_channel.create output_filename in
  append_definition iface builtins_map name_of_builtins name_of_pi input_filename oux;
  Out_channel.close oux;
  () *)


let wrap_init (g : Syntax.groundterm) : Syntax.groundterm =
  `GTerm ((`Id "builtin.init"), [g])

let write_gterm (iface : 'a Extracted.builtinInterface) (name_of_builtins : string) lexbuf outname =
  match Miparse.parse_groundterm_with_error lexbuf with
  | Some gt ->
    let oux = Out_channel.create outname in
    fprintf oux "%s" {|
    From Minuska Require Export
      prelude
      default_everything
      pval_ocaml_binding
    .
    From Minuska Require Import
      builtin.empty
      builtin.klike
    .
    |};
    fprintf oux "Definition mybeta := (bi_beta MyUnit builtins_%s).\n" name_of_builtins;
    fprintf oux "#[global] Existing Instance mybeta.\n";

    fprintf oux "%s" {|
      Definition given_groundterm := 
    |};
    Micoqprint.print_groundterm oux iface name_of_builtins (wrap_init gt);
    fprintf oux " .\n";
    Out_channel.close oux;
    ()
  | None -> ()



let run l =
  let _ = fprintf stderr "> %s\n" (String.concat l) in
  Sys_unix.command (String.concat l)

let generate_interpreter_ml_internal (cfg : languagedescr) input_filename (output_ml : string) =
  let iface = (get_iface cfg.static_model) in
  let builtins_map = (get_builtins_map (cfg.static_model)) in
  let name_of_builtins = cfg.static_model in
  let name_of_pi = (
    match cfg.program_info with
    | User_module _ -> failwith "User 'program info' modules are not supported yet"
    | Std_module name -> name
  ) in
  let mldir = (Filename_unix.temp_dir "langdef" ".minuska") in
  let mlfile = Filename.concat mldir "interpreter.ml" in
  let coqfile = Filename.concat mldir "interpreter.v" in
  (* create coqfile *)
  let oux_coqfile = Out_channel.create coqfile in
  append_definition iface builtins_map name_of_builtins name_of_pi input_filename oux_coqfile;
  fprintf oux_coqfile "%s" {|
    Require Import Ascii.
    Extract Inductive string => "Libminuska.Extracted.string" [ "Libminuska.Extracted.EmptyString" "Libminuska.Extracted.String" ].
    Extract Inductive ascii => "Libminuska.Extracted.ascii" [ "Libminuska.Extracted.Ascii" ].
    Extract Inductive RewritingRule2 => "Libminuska.Extracted.rewritingRule2" [  "(fun (a, b, c, d) -> { Libminuska.Extracted.r_from = a; Libminuska.Extracted.r_to = b; Libminuska.Extracted.r_scs = c; Libminuska.Extracted.r_act = d; })" ].
    Extract Inductive Act => "Libminuska.Extracted.act" [ "Libminuska.Extracted.Default_act" "Libminuska.Extracted.Invisible_act" ].
    Extract Inductive TermOver' => "Libminuska.Extracted.termOver'" [ "Libminuska.Extracted.T_over" "Libminuska.Extracted.T_term" ].
    Extract Inductive BuiltinInterface => "Libminuska.Extracted.builtinInterface" [ "(fun (a, b, c, d, e, f) -> { Libminuska.Extracted.bi_beta = a; Libminuska.Extracted.bi_bindings = b; Libminuska.Extracted.bi_inject_bool = c; Libminuska.Extracted.bi_inject_Z = d; Libminuska.Extracted.bi_inject_string = e; Libminuska.Extracted.bi_eject = f; })" ].
    Extract Constant bi_beta => "(fun x -> x.Libminuska.Extracted.bi_beta)".
    Extract Inductive Builtin => "Libminuska.Extracted.builtin" [  "Libminuska.Extracted.mkBuiltin" ].
    Extract Constant builtins_empty => "Libminuska.Extracted.builtins_empty".
    Extract Constant builtins_klike => "Libminuska.Extracted.builtins_klike".
    Extract Constant DSM => "Libminuska.Extracted.dSM".
    Extract Constant GT => "Libminuska.Extracted.gT".
    Extract Constant gt_term => "Libminuska.Extracted.gt_term".
    Extract Constant gt_over => "Libminuska.Extracted.gt_over".
    Extract Constant global_naive_interpreter => "Libminuska.Extracted.global_naive_interpreter".
    Extract Constant global_naive_interpreter_ext => "Libminuska.Extracted.global_naive_interpreter_ext".
  |};
  fprintf oux_coqfile "Set Extraction Output Directory \"%s\".\n" (mldir);
  fprintf oux_coqfile "Extraction \"%s\" lang_interpreter lang_interpreter_ext lang_debug_info.\n" ("interpreter.ml");
  Out_channel.close oux_coqfile;
  (* extract coq into ocaml *)
  let rv = run ["cd "; mldir; "; "; coqc_command; " "; "-R "; minuska_dir; " Minuska "; coqfile; " > coq_log.txt"] in
  (if rv <> 0 then failwith ("`"^ coqc_command ^ "` failed. Is the language definition well-formed?"));
  let _ = run ["cp '"; mlfile; "' '"; output_ml; "'"] in
  let _ = run ["cp '"; mlfile; "i' '"; output_ml; "i'"] in
  ()

let transform_groundterm (iface : 'a Extracted.builtinInterface) (name_of_builtins : string) input_fname output_fname () =
  let inx = In_channel.create input_fname in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_fname };
  write_gterm iface name_of_builtins lexbuf output_fname;
  In_channel.close(inx)

let refresh_parser parser_builder =
  ( match parser_builder with
  | Some command -> let _ = run [command] in ()
  | None -> ()
  );
  ()

let compile (cfg : languagedescr) input_filename interpreter_name oparserexe =
  let mldir = (Filename_unix.temp_dir "interpreter" ".minuska") in
  let mlfile = Filename.concat mldir "interpreter.ml" in
  let oparseexestr = (match oparserexe with
  | Some _ -> "(Some ((Filename.dirname Sys_unix.executable_name) ^ \"/../libexec/parser\") )"
  | None -> "None"
  ) in
  let _ = generate_interpreter_ml_internal cfg input_filename mlfile in
  (* Add an entry command *)
  let _ = Out_channel.with_file ~append:true mlfile ~f:(fun outc -> 
    fprintf outc "let _ = (Libminuska.Miskeleton.main %s Libminuska__.Dsm.builtins_%s lang_interpreter lang_interpreter_ext lang_debug_info)\n" oparseexestr (cfg.static_model)
  ) in
  let rv = run [
          "cd "; mldir; "; ";
          "env OCAMLPATH="; libdir; ":$OCAMLPATH ";
          ocamlfind_command; " ocamlopt -thread -package libminuska -package zarith -linkpkg -g -o ";
          "interpreter.exe"; " "; (String.append mlfile "i"); " "; mlfile] in
  (if rv <> 0 then failwith ("Internal error: `ocamlopt` failed."));
  let appdir = Filename.concat mldir "interpreter.AppDir" in
  let real_interpreter_name = interpreter_name in
  let _ = Core_unix.mkdir_p appdir in
  let _ = Core_unix.mkdir_p (Filename.concat appdir "bin") in
  let _ = Core_unix.mkdir_p (Filename.concat appdir "libexec") in
  let desktop_oux = Out_channel.create (Filename.concat appdir "interpreter.desktop") in
  fprintf desktop_oux "%s" {|[Desktop Entry]
Name=Interpreter
Exec=interpreter
Icon=interpreter
Type=Application
Categories=Utility;
Terminal=true|};
  Out_channel.close desktop_oux;
  let _ = run ["mv "; mldir; "/interpreter.exe"; " "; (Filename.concat appdir "bin/interpreter")] in
  let _ = (match oparserexe with
  | Some parserexe -> let _ = run ["cp "; parserexe; " "; ((Filename.concat appdir "libexec/parser"))] in ()
  | None -> ()
  ) in
  let _ = run ["cp "; (Filename.dirname (Filename_unix.realpath (Sys_unix.executable_name)) ^ "/../share/coq-minuska/minuska-256x256.png"); " "; (Filename.concat appdir "interpreter.png")] in
  let apprun_oux = Out_channel.create (Filename.concat appdir "AppRun") in
  fprintf apprun_oux "%s" {|#!/usr/bin/env bash
exec -a "$ARGV0" $(dirname "$0")/bin/interpreter $@
|};
  Out_channel.close apprun_oux;
  let _ = run ["chmod +x "; ((Filename.concat appdir "AppRun"))] in
  let _ = run ["appimagetool "; appdir; " "; real_interpreter_name] in
  let _ = input_filename in
  ()

let generate_interpreter_ml scm_filename (out_ml_file : string) =
  let dir = Filename.to_absolute_exn ~relative_to:(Core_unix.getcwd ()) (Filename.dirname scm_filename) in
  let cfg = Sexp.load_sexp scm_filename |> languagedescr_of_sexp in
  let mfile = if (Filename.is_relative cfg.semantics) then (Filename.concat dir cfg.semantics) else (cfg.semantics) in
  generate_interpreter_ml_internal cfg mfile out_ml_file;
  ()
  

let generate_interpreter scm_filename () =
  let dir = Filename.to_absolute_exn ~relative_to:(Core_unix.getcwd ()) (Filename.dirname scm_filename) in
  let cfg = Sexp.load_sexp scm_filename |> languagedescr_of_sexp in
  let mfile = if (Filename.is_relative cfg.semantics) then (Filename.concat dir cfg.semantics) else (cfg.semantics) in
  let parserfile = if (Filename.is_relative cfg.parser_exe) then (Filename.concat dir cfg.parser_exe) else (cfg.parser_exe) in
  let parser_builder = (
    match cfg.parser_builder with
    | Some command -> Some ("cd " ^ dir ^ "; " ^ command)
    | None -> None
  ) in
  refresh_parser parser_builder;
  compile cfg mfile (cfg.language ^ "-interpreter") (Some parserfile);
  ()
(* 
let command_generate =
  Command.basic
    ~summary:"Generate a Coq (*.v) file from a Minuska (*.m) file"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        builtins = flag "--builtins" (required string) ~doc:"builtins to use" and
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))

     in
     fun () -> transform (get_iface builtins) (get_builtins_map builtins) builtins input_filename output_filename ()) *)


let command_groundterm2coq =
  Command.basic
    ~summary:"Generate a Coq (*.v) file from a ground term (e.g., a program)"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        name_of_builtins = flag "--builtins" (required string) ~doc:"builtins to use" and
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))

     in
     fun () -> transform_groundterm (get_iface name_of_builtins) name_of_builtins input_filename output_filename ())

(* 
let command_compile =
  Command.basic
    ~summary:"Generate an interpreter from a Minuska (*.m) file"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        name_of_builtins = anon(("builtins" %: string)) and
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("interpreter" %: Filename_unix.arg_type))
     in
     fun () -> compile (get_iface name_of_builtins) (get_builtins_map name_of_builtins) name_of_builtins input_filename output_filename None) *)

let command_generate_interpreter =
Command.basic
  ~summary:"Generate an interpreter from a Minuska project file (*.scm)"
  ~readme:(fun () -> "TODO")
  (let%map_open.Command
      scm_filename = anon (("lang.scm" %: Filename_unix.arg_type))
    in
    fun () -> generate_interpreter scm_filename ())

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
      "generate-interpreter", command_generate_interpreter;
      "generate-interpreter-ml", command_generate_interpreter_ml;
      (* "compile", command_compile; *)
      (* "def2coq", command_generate; *) (* TODO replace this with something*)
      "gt2coq", command_groundterm2coq;
      "info", command_info
     ]

let () = Command_unix.run ~version:"0.5" command

