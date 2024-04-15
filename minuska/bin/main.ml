open Core
open Printf
open Lexing
open Syntax

let builtins_alist =
  [ "bool.neg", "b_bool_neg";
    "bool.and", "b_and";
    "bool.or", "b_or";
    "bool.false", "b_false";
    "term.same_symbol", "b_have_same_symbol";
  ]

let builtins_map = Map.of_alist_exn (module String) builtins_alist

let myiter (f : 'a -> 'b) (g : unit -> unit) (l : 'a list)  : unit =
    let ln = List.length l in
    List.iteri ~f:(fun idx x -> if (idx + 1 = ln) then (f x) else (f x; g ())) l;
    ()

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

let output_part_2 = {delimiter|
#[local]
Instance LangDefaults : Defaults := {|
    default_cseq_name := "__builtin_cseq" ;
    default_empty_cseq_name := "__builtin_empty_cseq" ;
    default_context_template
        := (context-template (@t_term _ _ "u_cfg") ([ HOLE ]) with HOLE) ;

    default_isValue := isValue ;
|}.
|delimiter}

let rec print_groundterm (oux : Out_channel.t) (g : groundterm) : unit =
  match g with
  | `GTerm (`Id s, gs) ->
    fprintf oux "(@t_term symbol builtin_value \"%s\" [" s;
    myiter (fun x -> print_groundterm oux x; ()) (fun () -> fprintf oux "; "; ()) gs;
    fprintf oux "])"

let rec print_pattern (oux : Out_channel.t) (p : pattern) : unit =
  match p with
  | `PVar (`Var s) -> fprintf oux "(t_over (bov_variable \"%s\"))" s
  | `PTerm (`Id s, ps) ->
    fprintf oux "(@t_term symbol BuiltinOrVar \"%s\" [" s;
    myiter (fun x -> print_pattern oux x; ()) (fun () -> fprintf oux "; "; ()) ps;
    fprintf oux "])"

let _ = print_pattern

let rec print_expr_w_hole (oux : Out_channel.t) (e : expr) (hole : string option) : unit =
  match e with
  | `EVar (`Var s) -> (
        match hole with
        | None -> fprintf oux "(e_variable %s)" s
        | Some s2 ->
            if String.(s = s2) then
                fprintf oux "(%s)" s2
            else
                fprintf oux "(e_variable %s)" s
        )
  | `EGround g ->
    fprintf oux "(e_ground ";
    print_groundterm oux g;
    fprintf oux ")"

  | `ECall (`Id s, es) ->
    let name0 = Map.find builtins_map s in
    match name0 with
    | None -> failwith (String.append "Unknown builtin: " s)
    | Some name1 ->
        let name = (String.append "default_builtin." name1) in
        match List.length es with
        | 0 -> fprintf oux "(e_nullary %s)" name
        | 1 ->
            fprintf oux "(e_unary %s " name;
            print_expr_w_hole oux (List.nth_exn es 0) hole;
            fprintf oux ")"
        | 2 ->
            fprintf oux "(e_binary %s " name;
            print_expr_w_hole oux (List.nth_exn es 0) hole;
            fprintf oux " ";
            print_expr_w_hole oux (List.nth_exn es 1) hole;
            fprintf oux ")"
        | 3 ->
            fprintf oux "(e_ternary %s " name;
            print_expr_w_hole oux (List.nth_exn es 0) hole;
            fprintf oux " ";
            print_expr_w_hole oux (List.nth_exn es 1) hole;
            fprintf oux " ";
            print_expr_w_hole oux (List.nth_exn es 2) hole;
            fprintf oux ")"
        | _ -> failwith "Bad length"



let print_expr (oux : Out_channel.t) (e : expr) : unit =
  print_expr_w_hole oux e None

let _ = print_expr


let print_rule (oux : Out_channel.t) (r : rule) : unit =
    fprintf oux "(decl_rule (@mkRuleDeclaration Σ Act \"%s\" (@mkRewritingRule2 Σ Act " (r.name);
    print_pattern oux (r.lhs);
    print_exprterm oux (r.lhs);
    fprintf oux ")))\n";
    ()


let print_definition def oux =
    let _ = def in
    fprintf oux "%s" output_part_1;
    fprintf oux "Definition isValue (";
    fprintf oux "%s" (match (fst (def.value)) with `Var s -> s);
    fprintf oux " : Expression2) := ";
    print_expr_w_hole oux (snd (def.value)) (Some (match (fst (def.value)) with `Var s -> s));
    fprintf oux ".\n";
    fprintf oux "%s\n" output_part_2;
    fprintf oux "Definition Lang_Decls : list Declaration := [\n";
    myiter (fun x -> print_rule oux x; ()) (fun () -> fprintf oux "; "; ()) (def.rules);
    fprintf oux "\n].\n";
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

