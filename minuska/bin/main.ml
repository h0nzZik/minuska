open Core
open Printf

open Libminuska
module Syntax = Libminuska.Syntax


let parse_and_print lexbuf oux =
  match Miparse.parse_definition_with_error lexbuf with
  | Some value ->
    Micoqprint.print_definition value oux
  | None -> ()


let append_definition input_filename output_channel =
  let inx = In_channel.create input_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_and_print lexbuf output_channel;
  In_channel.close inx;
  fprintf output_channel "%s\n" {|Definition T := Eval vm_compute in (to_theory Act (process_declarations Act default_act Lang_Decls)). |};
  fprintf output_channel "%s\n" {|Definition lang_interpreter : StepT := global_naive_interpreter (fst T).|};
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
        { apply _. }
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

let transform input_filename output_filename () =
  let oux = Out_channel.create output_filename in
  append_definition input_filename oux;
  Out_channel.close oux;
  ()


let wrap_init (g : Syntax.groundterm) : Syntax.groundterm =
  `GTerm ((`Id "builtin.init"), [g])

let write_gterm lexbuf outname =
  match Miparse.parse_groundterm_with_error lexbuf with
  | Some gt ->
    let oux = Out_channel.create outname in
    fprintf oux "%s" {|
      From Minuska Require Export
        prelude
        default_everything
      .
      Definition given_groundterm := 
    |};
    Micoqprint.print_groundterm oux (wrap_init gt);
    fprintf oux " .\n";
    Out_channel.close oux;
    ()
  | None -> ()

let transform_groundterm input_fname output_fname () =
  let inx = In_channel.create input_fname in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_fname };
  write_gterm lexbuf output_fname;
  In_channel.close(inx)

let run l =
  let _ = fprintf stderr "> %s\n" (String.concat l) in
  Sys_unix.command (String.concat l)

let compile input_filename interpreter_name () =
  (* let real_interpreter_name = Filename_unix.realpath interpreter_name in *)
  let real_interpreter_name = interpreter_name in
  let mldir = (Filename_unix.temp_dir "interpreter" ".minuska") in
  let coqfile = Filename.concat mldir "interpreter.v" in
  let mlfile = Filename.concat mldir "interpreter.ml" in
  transform input_filename coqfile ();
  let oux_coqfile = Out_channel.create coqfile in
  append_definition input_filename oux_coqfile;
  fprintf oux_coqfile "Set Extraction Output Directory \"%s\".\n" (mldir);
  fprintf oux_coqfile "Extraction \"%s\" lang_interpreter.\n" ("interpreter.ml");
  Out_channel.close oux_coqfile;
  let libdir = Filename.dirname (Filename_unix.realpath (Sys_unix.executable_name)) ^ "/../lib" in
  let minuska_dir = libdir ^ "/coq/user-contrib/Minuska" in
  let coq_minuska_dir = libdir ^ "/coq-minuska" in
  let _ = coq_minuska_dir in
  (* fprintf stdout "libdir: %s" libdir; *)
  let rv = run ["cd "; mldir; "; coqc "; "-R "; minuska_dir; " Minuska "; coqfile; " > coq_log.txt"] in
  (if rv <> 0 then failwith "`coqc` failed. Is the language definition well-formed?");
  let _ = Out_channel.with_file ~append:true mlfile ~f:(fun outc -> fprintf outc "%s\n" "let _ = (Libminuska.Miskeleton.main lang_interpreter)") in
  (*let _ = run ["cat "; mlfile] in*)
  let _ = run [
          "cd "; mldir; "; ";
          "env OCAMLPATH="; libdir; ":$OCAMLPATH ";
          "ocamlfind ocamlopt -thread -package coq-minuska -package zarith -linkpkg -g -o ";
          "interpreter.exe"; " "; (String.append mlfile "i"); " "; mlfile] in
  let _ = run ["mv "; mldir; "/interpreter.exe"; " "; real_interpreter_name] in
  let _ = input_filename in
  fprintf stdout "Hello, interpreter!\n";
  ()

let command_generate =
  Command.basic
    ~summary:"Generate a Coq (*.v) file from a Minuska (*.m) file"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))

     in
     fun () -> transform input_filename output_filename ())


let command_groundterm2coq =
  Command.basic
    ~summary:"Generate a Coq (*.v) file from a ground term (e.g., a program)"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))

     in
     fun () -> transform_groundterm input_filename output_filename ())


let command_compile =
  Command.basic
    ~summary:"Generate an interpreter from a Minuska (*.m) file"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("interpreter" %: Filename_unix.arg_type))
     in
     fun () -> compile input_filename output_filename ())

let command =
  Command.group
    ~summary:"A verified semantic framework"
    ["compile", command_compile;
     "def2coq", command_generate;
     "gt2coq", command_groundterm2coq]

let () = Command_unix.run ~version:"0.2" command

