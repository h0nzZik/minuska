open Core
open Printf

open Libminuska
module Syntax = Libminuska.Syntax


let parse_and_print lexbuf oux =
  match Miparse.parse_definition_with_error lexbuf with
  | Some value ->
    Miprint.print_definition value oux
  | None -> ()


let append_definition input_filename output_channel =
  let inx = In_channel.create input_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_and_print lexbuf output_channel;
  In_channel.close inx;
  fprintf output_channel "%s\n" {|Definition T := Eval vm_compute in (to_theory Act (process_declarations Act default_act Lang_Decls)). |};
  fprintf output_channel "%s\n" {|Definition lang_interpreter : StepT := naive_interpreter (fst T).|};
  ()

let transform input_filename output_filename () =
  let oux = Out_channel.create output_filename in
  append_definition input_filename oux;
  Out_channel.close oux;
  ()

let run l =
  let _ = fprintf stderr "> %s\n" (String.concat l) in
  Sys_unix.command (String.concat l)

let compile input_filename interpreter_name () =
  let mldir = (Filename_unix.temp_dir "interpreter" ".minuska") in
  let coqfile = Filename.concat mldir "interpreter.v" in
  let mlfile = Filename.concat mldir "interpreter.ml" in
  transform input_filename coqfile ();
  let oux_coqfile = Out_channel.create coqfile in
  append_definition input_filename oux_coqfile;
  fprintf oux_coqfile "Set Extraction Output Directory \"%s\".\n" (mldir);
  fprintf oux_coqfile "Extraction \"%s\" lang_interpreter.\n" ("interpreter.ml");
  Out_channel.close oux_coqfile;
  let libdir = Filename.dirname (Sys_unix.executable_name) ^ "/../lib" in
  let minuska_dir = libdir ^ "/coq/user-contrib/Minuska" in
  let coq_minuska_dir = libdir ^ "/coq-minuska" in
  let _ = coq_minuska_dir in
  fprintf stdout "libdir: %s" libdir;
  let _ = run ["cd "; mldir; "; coqc "; "-R "; minuska_dir; " Minuska "; coqfile] in
  let _ = Out_channel.with_file ~append:true mlfile ~f:(fun outc -> fprintf outc "%s\n" "let _ = (Libminuska.Miskeleton.main lang_interpreter)") in
  let _ = run ["cat "; mlfile] in
  let _ = run [
          "cd "; mldir; "; ";
          "env OCAMLPATH="; libdir; ":$OCAMLPATH ";
          "ocamlfind ocamlc -package coq-minuska -package zarith -linkpkg -g -w -20 -w -26 -o ";
          "interpreter.exe"; " "; (String.append mlfile "i"); " "; mlfile] in
  let _ = run ["cp "; mldir; "/interpreter.exe"; " "; interpreter_name] in
  let _ = input_filename in
  let _ = interpreter_name in
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
    ["compile", command_compile; "def2coq", command_generate]

let () = Command_unix.run ~version:"1.0" ~build_info:"RWO" command

