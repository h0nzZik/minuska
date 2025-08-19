open Core
open Printf
open Sexplib

open Libminuska
open Libminuskapluginbase.Pluginbase

(* < to be patched in Nix> *)
let coqc_command = "coqc" ;;
let minuska_dir = "/usr/lib/coq/user-contrib/Minuska" ;;
let stdpp_dir = "/usr/lib/coq/user-contrib/stdpp" ;;
let equations_dir = "/usr/lib/coq/user-contrib/Equations" ;;
(* </to be patched in Nix> *)

let coqflags : string = sprintf "-include %s -R %s Equations -R %s stdpp -R %s Minuska" equations_dir equations_dir stdpp_dir minuska_dir


let parse_and_print
  lexbuf
  (oux : Out_channel.t)
  =
  match Miparse.parse_definition_with_error lexbuf with
  | Some value ->
    fprintf oux "%s" (Micoqprint.definition_to_str value);
    ()
  | None -> ()


let append_definition
  input_filename
  (output_channel : Out_channel.t)
  =
  In_channel.with_file input_filename ~f:(fun inx ->
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
    parse_and_print lexbuf output_channel;  
  );
  ()

let wrap_init (g : groundterm) : groundterm =
  `GTerm ((`Id "builtin.init"), [g])

(* FIXME this is probably wrong *)
let write_gterm
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
      |};
      fprintf oux {|
        Definition given_groundterm := (%s).
      |} (Micoqprint.groundterm_to_string (wrap_init gt));
      ()
    );
    ()
  | None -> ()



let run l =
  let _ = fprintf stderr "> %s\n" (String.concat l) in
  Sys_unix.command (String.concat l)

let generate_interpreter_coq_internal input_filename (output_coq : string) =
  Out_channel.with_file output_coq ~f:(fun oux_coqfile ->
    append_definition input_filename oux_coqfile;
    ()
  ); ()

let generate_interpreter_ml_internal (user_dir : string) input_filename (output_ml : string) =
  let mldir = (Filename_unix.temp_dir "langdef" ".minuska") in
  let coqfile = Filename.concat mldir "interpreter.v" in
  let mlfile = Filename.concat mldir "interpreter.ml" in
  let _ = generate_interpreter_coq_internal input_filename coqfile in
  (* append to coqfile *)
  Out_channel.with_file coqfile ~append:(true) ~f:(fun oux_coqfile ->
    fprintf oux_coqfile "%s" {|
      Require Import Ascii Coq.extraction.ExtrOcamlNativeString.
(*
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
".*)
      (*Extract Inductive string => "Libminuska.Extracted.string" [ "Libminuska.Extracted.EmptyString" "Libminuska.Extracted.String" ].*)
      (*Extract Inductive ascii => "Libminuska.Extracted.ascii" [ "Libminuska.Extracted.Ascii" ].*)
      Extract Inductive stdpp.countable.Countable => "Libminuska.Extracted.countable" [ "(fun (e,d) -> {Libminuska.Extracted.encode = e; Libminuska.Extracted.decode = d;})" ].
      Extract Inductive RewritingRule2' => "Libminuska.Extracted.rewritingRule2'" [  "(fun (a, b, c, d) -> { Libminuska.Extracted.r_from = a; Libminuska.Extracted.r_to = b; Libminuska.Extracted.r_scs = c; Libminuska.Extracted.r_label = d; })" ].
      Extract Inductive Label => "Libminuska.Extracted.label" [ "Libminuska.Extracted.Default_label" "Libminuska.Extracted.Invisible_label" ].
      Extract Inductive TermOver' => "Libminuska.Extracted.termOver'" [ "Libminuska.Extracted.T_over" "Libminuska.Extracted.T_term" ].
      (* Extract Inductive ValueAlgebraInterface => "Libminuska.Extracted.valueAlgebraInterface" [ "(fun (a0, a, b, c) -> { Libminuska.Extracted.bi_signature = a0; Libminuska.Extracted.bi_beta = a; Libminuska.Extracted.bi_bindings = b; Libminuska.Extracted.bi_show_builtin = c; })" ] "(fun myf x -> match x with {Libminuska.Extracted.bi_signature=a0;Libminuska.Extracted.bi_beta=a;Libminuska.Extracted.bi_bindings=b; Libminuska.Extracted.bi_show_builtin = c} -> (myf a0 a b c))" . *)

      (* Extract Constant bi_beta => "(fun x -> x.Libminuska.Extracted.bi_beta)". *)
      (* Extract Constant builtins_empty => "Libminuska.Extracted.builtins_empty". *)
      (* Extract Constant builtins_klike => "Libminuska.Extracted.builtins_klike". *)
      (* Extract Constant pi_trivial => "Libminuska.Extracted.pi_trivial". *)
      (* Extract Constant GT => "Libminuska.Extracted.gT". *)
      (* Extract Constant gt_term => "Libminuska.Extracted.gt_term". *)
      (* Extract Constant gt_over => "Libminuska.Extracted.gt_over". *)

      Extract Inductive BuiltinRepr => "Libminuska.Extracted.builtinRepr" [ "(fun (a,b) -> { Libminuska.Extracted.br_kind=a; Libminuska.Extracted.br_value=b; } )" ].
      Extract Inductive StringBuiltinOrVar => "Libminuska.Extracted.stringBuiltinOrVar" [ "Libminuska.Extracted.Sbov_builtin" "Libminuska.Extracted.Sbov_var" ] .
      Extract Inductive ProgramInfo => "Libminuska.Extracted.programInfo" [ "(fun (b, c, d) -> { Libminuska.Extracted.querySymbol_eqdec = b; Libminuska.Extracted.querySymbol_countable = c; Libminuska.Extracted.pi_symbol_interp = d; })" ].
      Extract Inductive Declaration => "Libminuska.Extracted.declaration" [ "Libminuska.Extracted.Decl_rule" "Libminuska.Extracted.Decl_ctx" "Libminuska.Extracted.Decl_strict" ] .
      Extract Inductive StringSideCondition => "Libminuska.Extracted.stringSideCondition" [ "Libminuska.Extracted.Ssc_true" "Libminuska.Extracted.Ssc_false" "Libminuska.Extracted.Ssc_pred" "Libminuska.Extracted.Ssc_npred" "Libminuska.Extracted.Ssc_and" "Libminuska.Extracted.Ssc_or" ].
      Extract Inductive StringExpression => "Libminuska.Extracted.stringExpression" [ "Libminuska.Extracted.Se_ground" "Libminuska.Extracted.Se_variable" "Libminuska.Extracted.Se_apply" ].
      Extract Inductive Defaults => "Libminuska.Extracted.defaults" [ "(fun (a,b,c,d) -> {Libminuska.Extracted.default_cseq_name = a; Libminuska.Extracted.default_empty_cseq_name = b; Libminuska.Extracted.default_context_template = c; Libminuska.Extracted.default_isValue = d;})" ].
      (* Extract Constant global_naive_interpreter => "Libminuska.Extracted.global_naive_interpreter". *)
      (* Extract Constant global_naive_interpreter_ext => "Libminuska.Extracted.global_naive_interpreter_ext". *)
    |};
    fprintf oux_coqfile "Set Extraction Output Directory \"%s\".\n" (mldir);
    fprintf oux_coqfile "Extraction \"%s\" Lang_Decls LangDefaults (*chosen_builtins*).\n" ("interpreter.ml");
  );
  (* extract coq into ocaml *)
  let rv = run ["cd "; mldir; "; "; coqc_command; " "; coqflags; " -R "; user_dir; " User "; coqfile; " > coq_log.txt"] in
  (if rv <> 0 then failwith ("`"^ coqc_command ^ "` failed. Is the language definition well-formed?"));
  let _ = run ["cp '"; mlfile; "' '"; output_ml; "'"] in
  let _ = run ["cp '"; mlfile; "i' '"; output_ml; "i'"] in
  ()

let transform_groundterm
  input_fname output_fname () =
  In_channel.with_file input_fname ~f:(fun inx ->
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_fname };
    write_gterm lexbuf output_fname;  
  );
  ()

let generate_interpreter_ml defm_filename (out_ml_file : string) =
  let curdir = Core_unix.getcwd () in
  generate_interpreter_ml_internal curdir defm_filename out_ml_file;
  ()

let generate_interpreter_coq defm_filename (out_coq_file : string) =
  generate_interpreter_coq_internal defm_filename out_coq_file;
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
    fprintf oux 
{|
open Core
open Printf
open Libminuskapluginbase
open Pluginbase

let main () =
  let pvae = (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("%s")))) in
  let signature = (pvae.pvae_builtin_interface.bi_signature) in
  let builtins = (pvae.pvae_builtin_interface.bi_beta) in
  let pie = (get_trivial_program_info signature builtins) in
  Libminuska.Miskeleton.main
    pvae
    pie          
    (fun _ -> failwith "Parser not implemented.")
    Internal.langDefaults
    Internal.lang_Decls
  
let _ = main ()
|}
    (Sexp.to_string (sexp_of_coqModuleName name_of_builtins))
  );
  ()

let command_init =
  Command.basic
    ~summary:"Generate a Minuska project (`lang.scm`, `lang.m`, `run.ml`, `dune-project`, `dune`) in the current directory. NOT MAINTAINED/TESTED, FIXME"
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
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))
     in
     fun () -> 
      transform_groundterm input_filename output_filename ())

let command_generate_interpreter_coq =
  Command.basic
    ~summary:"Generate an interpreter *.v file from a Minuska language definition file (*.m)"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        defm_filename = anon (("lang.m" %: Filename_unix.arg_type)) and
        out_ml_file = anon (("lang.ml" %: Filename_unix.arg_type))
      in
      fun () -> generate_interpreter_coq defm_filename out_ml_file)

let command_generate_interpreter_ml =
  Command.basic
    ~summary:"Generate an interpreter *.ml file from a Minuska language definition file (*.m)"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        defm_filename = anon (("lang.m" %: Filename_unix.arg_type)) and
        out_ml_file = anon (("lang.ml" %: Filename_unix.arg_type))
      in
      fun () -> generate_interpreter_ml defm_filename out_ml_file)


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

