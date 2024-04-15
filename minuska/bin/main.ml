open Core
open Printf
open Lexing
open Syntax

let builtins_alist =
  [ "bool.neg", "b_bool_neg";
    "bool.and", "b_and";
    "bool.false", "b_false"
  ]

let builtins_map = Map.of_alist_exn (module String) builtins_alist


let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.definition Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)


let output_part_1 = {|
From Minuska Require Import
    prelude
    spec
    string_variables
    builtins
    default_static_model
    frontend
.

Variant Act := default_act | invisible_act.

#[local]
Instance Σ : StaticModel :=
    default_model (default_builtin.β)
.
|}

let rec print_groundterm (oux : Out_channel.t) (g : groundterm) : unit =
  match g with
  | `GTerm (`Id s, gs) ->
    fprintf oux "(@t_term symbol builtin_value %s [" s;
    List.iter ~f:(fun x -> print_groundterm oux x; fprintf oux "; ";) gs;
    fprintf oux "])"

let rec print_pattern (oux : Out_channel.t) (p : pattern) : unit =
  match p with
  | `PVar (`Var s) -> fprintf oux "(bov_variable %s)" s
  | `PTerm (`Id s, ps) ->
    fprintf oux "(@t_term symbol BuiltinOrVar %s [" s;
    List.iter ~f:(fun x -> print_pattern oux x; fprintf oux "; ";) ps;
    fprintf oux "])"

let _ = print_pattern

let rec print_expr (oux : Out_channel.t) (e : expr) : unit =
  match e with
  | `EVar (`Var s) -> fprintf oux "(e_variable %s)" s
  | `EGround g ->
    fprintf oux "(e_ground ";
    print_groundterm oux g;
    fprintf oux ")"

  | `ECall (`Id s, es) ->
    let name0 = Map.find builtins_map s in
    match name0 with
    | None -> failwith (String.append "Unknown builtin: " s)
    | Some name ->
        match List.length es with
        | 0 -> fprintf oux "(e_nullary %s)" name
        | 1 ->
            fprintf oux "(e_unary %s" name;
            print_expr oux (List.nth_exn es 0);
            fprintf oux ")"
        | 2 ->
            fprintf oux "(e_binary %s" name;
            print_expr oux (List.nth_exn es 0);
            fprintf oux ", ";
            print_expr oux (List.nth_exn es 1);
            fprintf oux ")"
        | 3 ->
            fprintf oux "(e_ternary %s" name;
            print_expr oux (List.nth_exn es 0);
            fprintf oux ", ";
            print_expr oux (List.nth_exn es 1);
            fprintf oux ", ";
            print_expr oux (List.nth_exn es 2);
            fprintf oux ")"
        | _ -> failwith "Bad length"


let print_definition def oux =
    let _ = def in
    fprintf oux "%s" output_part_1;
    print_expr oux (snd (def.value));
    ()

let parse_and_print lexbuf oux =
  match parse_with_error lexbuf with
  | Some value ->
    print_definition value oux
  | None -> ()




let transform input_filename output_filename () =
  let inx = In_channel.create input_filename in
  let oux = Out_channel.create output_filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = input_filename };
  parse_and_print lexbuf oux;
  Out_channel.close oux;
  In_channel.close inx


let command =
  Command.basic
    ~summary:"Generate a Coq (*.v) file from a Minuska (*.m) file"
    ~readme:(fun () -> "TODO")
    (let%map_open.Command
        input_filename = anon (("filename_in" %: Filename_unix.arg_type)) and
        output_filename = anon (("filename_out" %: Filename_unix.arg_type))

     in
     fun () -> transform input_filename output_filename ())

let () = Command_unix.run ~version:"1.0" ~build_info:"RWO" command

