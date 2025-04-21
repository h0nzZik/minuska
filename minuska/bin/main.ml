open Core
open Printf
open Sexplib
open Sexplib.Std

open Libminuska
open Libminuskapluginbase
open Syntax

open Libminuskapluginbase.Pluginbase
(*module Stringutils = Libminuskapluginbase.Stringutils*)

type languagedescr = {
  language                 : string      ;
  semantics                : string      ;
  primitive_value_algebra  : coqModuleName ;
  program_info             : coqModuleName ;
} [@@deriving sexp]

type builtins_map_t = (string, string, String.comparator_witness) Map.t ;;
type query_map_t = (string, string, String.comparator_witness) Map.t ;;

let transform_map m =
  let binding = List.map ~f:(fun p -> ((*Stringutils.implode*) (fst p), (*Stringutils.implode*) (snd p))) m in
  let m2 = Map.of_alist_exn (module String) binding in
  m2

let get_builtins_map (primitive_value_algebra_name : coqModuleName) : builtins_map_t =
  let builtins_binding_coq = (get_primitive_value_algebra primitive_value_algebra_name).pvae_builtin_interface.bi_bindings in
  let builtins_binding = List.map ~f:(fun p -> ((*Stringutils.implode*) (fst p), (*Stringutils.implode*) (snd p))) builtins_binding_coq in
  let builtins_map : builtins_map_t = Map.of_alist_exn (module String) builtins_binding in
  builtins_map

(* < to be patched in Nix> *)
let coqc_command = "coqc" ;;
let minuska_dir = "/usr/lib/coq/user-contrib/Minuska" ;;
let stdpp_dir = "/usr/lib/coq/user-contrib/stdpp" ;;
let equations_dir = "/usr/lib/coq/user-contrib/Equations" ;;
(* </to be patched in Nix> *)

let coqflags : string = sprintf "-include %s -R %s Equations -R %s stdpp -R %s Minuska" equations_dir equations_dir stdpp_dir minuska_dir


let parse_and_print
  (pvae : primitiveValueAlgebraEntry)
  (builtins_map : builtins_map_t)
  (query_map : query_map_t)
  ~(name_of_builtins : coqModuleName)
  ~(name_of_pi : coqModuleName) lexbuf oux =
  match Miparse.parse_definition_with_error lexbuf with
  | Some value ->
    Micoqprint.print_definition pvae builtins_map query_map ~name_of_builtins:(name_of_builtins) ~name_of_pi:(name_of_pi) value oux
  | None -> ()


let append_definition
  (pvae : primitiveValueAlgebraEntry)
  (builtins_map : builtins_map_t)
  (query_map : query_map_t)
  ~(name_of_builtins : coqModuleName)
  ~(name_of_pi : coqModuleName)
  input_filename
  output_channel
  =
  In_channel.with_file input_filename ~f:(fun inx ->
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
    parse_and_print pvae builtins_map query_map ~name_of_builtins:(name_of_builtins) ~name_of_pi:(name_of_pi) lexbuf output_channel;  
  );
  fprintf output_channel "%s\n" {|Definition pre1T := Eval vm_compute in (process_declarations Act default_act mysignature mybeta my_program_info Lang_Decls). |};
  fprintf output_channel "%s\n" {|Definition pre2T := Eval vm_compute in (match pre1T as m return (match m return Type with inl _ => State | inr _ => string end) with inl t => t | inr s => s end). |};
  fprintf output_channel "%s\n" {|Fail Definition myerror : string := Eval vm_compute in (pre2T). |};
  fprintf output_channel "%s\n" {|Definition myok : State := Eval vm_compute in (pre2T). |};
  fprintf output_channel "%s\n" {|Definition T1 := Eval vm_compute in (fst (to_theory Act myok)). |};
  fprintf output_channel "%s\n" {|Definition T2 := Eval vm_compute in (snd (to_theory Act myok)). |};
  fprintf output_channel "%s\n" {|Definition lang_interpreter (*: (StepT my_program_info)*) := global_naive_interpreter my_program_info T1.|};
  fprintf output_channel "%s\n" {|Definition lang_interpreter_ext (*: (StepT_ext my_program_info)*) := global_naive_interpreter_ext my_program_info T1.|};
  fprintf output_channel "%s\n" {|Definition lang_debug_info : list string := T2.|};
  fprintf output_channel "%s\n" {|
    (* This lemma asserts well-formedness of the definition *)
    Lemma language_well_formed: spec_interpreter.RewritingTheory2_wf T1.
    Proof.
      (* This is the main syntactic check. If this fails, the semantics contains a bad rule. *)
      ltac1:(compute_done).
    Qed.
    (* This lemma asserts soundness of the generated interpreter. *)
    (* Unfortunately, we cannot rely on the extraction here.
    Lemma interp_sound:
        Interpreter_sound'
        T1
        lang_interpreter
    .
    Proof.
        apply global_naive_interpreter_sound.
        apply language_well_formed.
    Qed.
    *)
  |} ;
  ()

let wrap_init (g : groundterm) : groundterm =
  `GTerm ((`Id "builtin.init"), [g])

let write_gterm
  (pvae : primitiveValueAlgebraEntry)
  (name_of_builtins : coqModuleName)
  (name_of_pi : coqModuleName)
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
      fprintf oux "Require %s.\n" (get_primitive_value_algebra name_of_builtins).pvae_coq_import;
      fprintf oux "Require %s.\n" (get_pi name_of_pi).pie_coq_import;
      fprintf oux "Definition mysignature := (bi_signature MyUnit %s).\n" (get_primitive_value_algebra name_of_builtins).pvae_coq_entity_name;
      fprintf oux "#[global] Existing Instance mysignature.\n";
      fprintf oux "Definition mybeta := (bi_beta MyUnit %s).\n" (get_primitive_value_algebra name_of_builtins).pvae_coq_entity_name;
      fprintf oux "#[global] Existing Instance mybeta.\n";
      fprintf oux "Definition my_program_info := %s.\n" (get_pi name_of_pi).pie_coq_entity_name;
      fprintf oux "Definition mysigma : StaticModel := (default_everything.DSM my_program_info).\n";
      fprintf oux "Existing Instance mysigma.\n";
      fprintf oux "%s" {|
        Definition given_groundterm := 
      |};
      Micoqprint.print_groundterm oux pvae (wrap_init gt);
      fprintf oux " .\n";
    );
    ()
  | None -> ()



let run l =
  let _ = fprintf stderr "> %s\n" (String.concat l) in
  Sys_unix.command (String.concat l)

let generate_interpreter_coq_internal (cfg : languagedescr) input_filename (output_coq : string) =
  let pvae = ((get_primitive_value_algebra cfg.primitive_value_algebra)) in
  let builtins_map = (get_builtins_map (cfg.primitive_value_algebra)) in
  let pi = get_pi cfg.program_info in
  let query_map = transform_map (pi.pie_table) in
  (* create coqfile *)
  Out_channel.with_file output_coq ~f:(fun oux_coqfile ->
    append_definition pvae builtins_map query_map ~name_of_builtins:(cfg.primitive_value_algebra) ~name_of_pi:(cfg.program_info) input_filename oux_coqfile;
    fprintf oux_coqfile "Definition chosen_builtins := %s.\n" (get_primitive_value_algebra cfg.primitive_value_algebra).pvae_coq_entity_name;
    ()
  )

let generate_interpreter_ml_internal (user_dir : string) (cfg : languagedescr) input_filename (output_ml : string) =
  let mldir = (Filename_unix.temp_dir "langdef" ".minuska") in
  let coqfile = Filename.concat mldir "interpreter.v" in
  let mlfile = Filename.concat mldir "interpreter.ml" in
  let _ = generate_interpreter_coq_internal cfg input_filename coqfile in
  (* append to coqfile *)
  Out_channel.with_file coqfile ~append:(true) ~f:(fun oux_coqfile ->
    fprintf oux_coqfile "%s" {|
      Require Import Ascii Coq.extraction.ExtrOcamlNativeString.
Extract Inductive string => "string"
[
"
  """"
"
"
  (fun (c, s) -> Stdlib.String.make 1 c ^ s)
"
]
"
 (fun f0 f1 s ->
    let l = Stdlib.String.length s in
    if l = 0 then f0 () else f1 (Stdlib.String.get s 0) (Stdlib.String.sub s 1 (l-1)))
".
      (*Extract Inductive string => "Libminuska.Extracted.string" [ "Libminuska.Extracted.EmptyString" "Libminuska.Extracted.String" ].*)
      (*Extract Inductive ascii => "Libminuska.Extracted.ascii" [ "Libminuska.Extracted.Ascii" ].*)
      Extract Inductive stdpp.countable.Countable => "Libminuska.Extracted.countable" [ "(fun (e,d) -> {Libminuska.Extracted.encode = e; Libminuska.Extracted.decode = d;})" ].
      Extract Inductive RewritingRule2 => "Libminuska.Extracted.rewritingRule2" [  "(fun (a, b, c, d) -> { Libminuska.Extracted.r_from = a; Libminuska.Extracted.r_to = b; Libminuska.Extracted.r_scs = c; Libminuska.Extracted.r_act = d; })" ].
      Extract Inductive Act => "Libminuska.Extracted.act" [ "Libminuska.Extracted.Default_act" "Libminuska.Extracted.Invisible_act" ].
      Extract Inductive TermOver' => "Libminuska.Extracted.termOver'" [ "Libminuska.Extracted.T_over" "Libminuska.Extracted.T_term" ].
      Extract Constant TermOver "'a" => "'a Libminuska.Extracted.termOver".
      Extract Inductive BuiltinInterface => "Libminuska.Extracted.builtinInterface" [ "(fun (a0, a, b, d, e, f, g) -> { Libminuska.Extracted.bi_signature = a0; Libminuska.Extracted.bi_beta = a; Libminuska.Extracted.bi_bindings = b; })" ] "(fun myf x -> match x with {Libminuska.Extracted.bi_signature=a0;Libminuska.Extracted.bi_beta=a;Libminuska.Extracted.bi_bindings=b;} -> (myf a0 a b ))" .

      Extract Constant bi_beta => "(fun x -> x.Libminuska.Extracted.bi_beta)".
      Extract Inductive Signature => "Libminuska.Extracted.signature" [ "(fun (x1,x2) -> Libminuska.Extracted.builtin_function_symbol_eqdec = x1; Libminuska.Extracted.builtin_predicate_symbol_eqdec = x2; ))" ].
      Extract Inductive Model => "Libminuska.Extracted.model" [  "(fun (x1,x2,x3) -> {Libminuska.Extracted.builtin_value_eqdec = x1; Libminuska.Extracted.builtin_function_interp = x2; Libminuska.Extracted.builtin_predicate_interp = x3;})" ].
      Extract Constant builtins_empty => "Libminuska.Extracted.builtins_empty".
      Extract Constant builtins_klike => "Libminuska.Extracted.builtins_klike".
      Extract Constant pi_trivial => "Libminuska.Extracted.pi_trivial".
      Extract Constant DSM => "Libminuska.Extracted.dSM".
      Extract Constant GT => "Libminuska.Extracted.gT".
      Extract Constant gt_term => "Libminuska.Extracted.gt_term".
      Extract Constant gt_over => "Libminuska.Extracted.gt_over".
      Extract Inductive ProgramInfo => "Libminuska.Extracted.programInfo" [ "(fun (b, c, d) -> { Libminuska.Extracted.querySymbol_eqdec = b; Libminuska.Extracted.querySymbol_countable = c; Libminuska.Extracted.pi_symbol_interp = d; })" ].
      Extract Constant program_info => "Libminuska.Extracted.programInfo".
      Extract Constant global_naive_interpreter => "Libminuska.Extracted.global_naive_interpreter".
      Extract Constant global_naive_interpreter_ext => "Libminuska.Extracted.global_naive_interpreter_ext".
    |};
    fprintf oux_coqfile "Set Extraction Output Directory \"%s\".\n" (mldir);
    fprintf oux_coqfile "Extraction \"%s\" lang_interpreter lang_interpreter_ext lang_debug_info chosen_builtins.\n" ("interpreter.ml");
  );
  (* extract coq into ocaml *)
  let rv = run ["cd "; mldir; "; "; coqc_command; " "; coqflags; " -R "; user_dir; " User "; coqfile; " > coq_log.txt"] in
  (if rv <> 0 then failwith ("`"^ coqc_command ^ "` failed. Is the language definition well-formed?"));
  let _ = run ["cp '"; mlfile; "' '"; output_ml; "'"] in
  let _ = run ["cp '"; mlfile; "i' '"; output_ml; "i'"] in
  ()

let transform_groundterm
  (pvae : primitiveValueAlgebraEntry)
  (name_of_builtins : coqModuleName)
  (name_of_pi : coqModuleName)
  input_fname output_fname () =
  In_channel.with_file input_fname ~f:(fun inx ->
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_fname };
    write_gterm pvae name_of_builtins name_of_pi lexbuf output_fname;  
  );
  ()

let generate_interpreter_ml (modules : string list) scm_filename (out_ml_file : string) =
  let curdir = Core_unix.getcwd () in
  List.iter ~f:(fun m -> printf "Loading module '%s'\n" m; Dynlink.loadfile m) modules;
  let dir = Filename.to_absolute_exn ~relative_to:(curdir) (Filename.dirname scm_filename) in
  let cfg = Sexp.load_sexp scm_filename |> languagedescr_of_sexp in
  let mfile = if (Filename.is_relative cfg.semantics) then (Filename.concat dir cfg.semantics) else (cfg.semantics) in
  generate_interpreter_ml_internal curdir cfg mfile out_ml_file;
  ()

let generate_interpreter_coq scm_filename (out_coq_file : string) =
  let dir = Filename.to_absolute_exn ~relative_to:(Core_unix.getcwd ()) (Filename.dirname scm_filename) in
  let cfg = Sexp.load_sexp scm_filename |> languagedescr_of_sexp in
  let mfile = if (Filename.is_relative cfg.semantics) then (Filename.concat dir cfg.semantics) else (cfg.semantics) in
  generate_interpreter_coq_internal cfg mfile out_coq_file;
  ()

let initialize_project project_name (name_of_builtins : coqModuleName) (name_of_program_info : coqModuleName) =
  let _ = Sys_unix.command (sprintf "dune init project %s ." project_name) in
  Out_channel.with_file "lang.scm" ~f:(fun oux ->
    fprintf oux
{|
  (
    (language %s)
    (semantics def.m)
    (primitive_value_algebra %s)
    (program_info %s)
  )
|}
    project_name (Sexp.to_string (sexp_of_coqModuleName name_of_builtins)) (Sexp.to_string (sexp_of_coqModuleName name_of_program_info));
  );
  Out_channel.with_file "dune" ~f:(fun oux ->
    fprintf oux
{|
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
|}
    project_name
  );
  Out_channel.with_file "def.m" ~f:(fun oux ->
    fprintf oux
{|
@frames: [
  simple(X): c[builtin.cseq [X,REST]]
];
@value(X): @false ;
@context(HOLE): c[HOLE];
@strictness: [];

@rule [init]: builtin.init[] => c[builtin.cseq[program.ast(), builtin.empty_cseq[]], map.empty()] where @true;
@rule/simple [plus]: plus[X,Y] => z.plus(X, Y) where @and(z.is(X), z.is(Y)) ;
|}
  );
  Out_channel.with_file "run.ml" ~f:(fun oux ->
    fprintf oux {|
      open Core
      open Printf
      open Libminuskapluginbase
      open Pluginbase

      let main () =
        Libminuska.Miskeleton.main
          (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("%s"))))
          Internal.chose_builtins
          (fun _ -> failwith "Parser not implemented.")
          Internal.lang_interpreter
          Internal.lang_interpreter_ext
          Internal.lang_debug_info
        
      let _ = main ()
    |} (Sexp.to_string (sexp_of_coqModuleName name_of_builtins))
  );
  ()

let command_init =
  Command.basic
    ~summary:"Generate a Minuska project (`lang.scm`, `lang.m`, `run.ml`, `dune-project`, `dune`) in the current directory."
    ~readme:(fun () -> "TODO")
    (
      let%map_open.Command
        project_name = flag "--name" (required string) ~doc:"project name" and
        name_of_builtins0 = flag "--builtins" (required string) ~doc:"builtins to use" and
        name_of_program_info0 = flag "--program-info" (required string) ~doc:"program info to use"
      in
      fun () -> 
        let name_of_builtins = coqModuleName_of_sexp (Sexp.of_string name_of_builtins0) in
        let name_of_program_info = coqModuleName_of_sexp (Sexp.of_string name_of_program_info0) in
        initialize_project project_name name_of_builtins name_of_program_info
    )

let command_groundterm2coq =
  Command.basic
    ~summary:"Generate a Coq (*.v) file from a ground term (e.g., a program)"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
    (* TODO support user-provided PVAs *)
        name_of_builtins0 = flag "--builtins" (required string) ~doc:"builtins to use" and
        name_of_program_info0 = flag "--program-info" (required string) ~doc:"program info to use" and
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))

     in
     fun () -> 
      let name_of_builtins = coqModuleName_of_sexp (Sexp.of_string name_of_builtins0) in
      let name_of_program_info = coqModuleName_of_sexp (Sexp.of_string name_of_program_info0) in
      transform_groundterm (get_primitive_value_algebra name_of_builtins) name_of_builtins name_of_program_info input_filename output_filename ())

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
        dynload = (flag) "--dynload" (listed string) ~doc:("module to dynamically load") and
        scm_filename = anon (("lang.scm" %: Filename_unix.arg_type)) and
        out_ml_file = anon (("lang.ml" %: Filename_unix.arg_type))
      in
      fun () -> generate_interpreter_ml dynload scm_filename out_ml_file)


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
    (fun () -> 
      printf "%s" coqflags
      (* printf "%s" ("-R " ^ minuska_dir ^ " Minuska") *)
    )
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
      "generate-interpreter-ml", command_generate_interpreter_ml;
      "generate-interpreter-coq", command_generate_interpreter_coq;
      "gt2coq", command_groundterm2coq;
      "info", command_info
     ]

let () = Command_unix.run ~version:"0.6" command

