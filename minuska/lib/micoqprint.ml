open Core
open Syntax

type builtins_map_t = (string, string, String.comparator_witness) Map.t ;;
type query_map_t = (string, string, String.comparator_witness) Map.t ;;

let myiter (f : 'a -> 'b) (g : unit -> unit) (l : 'a list)  : unit =
    let ln = List.length l in
    List.iteri ~f:(fun idx x -> if (idx + 1 = ln) then (f x) else (f x; g ())) l;
    ()


let output_part_1 = {|
Require Import Minuska.pval_ocaml_binding Minuska.default_everything Minuska.builtin.empty Minuska.builtin.klike Minuska.pi.trivial.
|}

let output_part_2 = {delimiter|

#[local]
Instance LangDefaults : Defaults := {|
    default_cseq_name := "builtin.cseq" ;
    default_empty_cseq_name := "builtin.empty_cseq" ;
    default_context_template := myContext ;

    default_isValue := isValue ;
    default_isNonValue := isNonValue ;
|}.
|delimiter}

let translate_name
  (my_builtins_map : builtins_map_t)
  (my_query_map : query_map_t)
  (name : string)
  : (string*string)
  =
  let name0 = Map.find my_builtins_map name in
    match name0 with
    | None ->  (
      let name1 = Map.find my_query_map name in
      match name1 with
      | None ->
        failwith (String.append "Unknown builtin: " name)
      | Some name2 ->
        let name = (name2) in
        ("e_query", name)
    )
    | Some name1 ->
        let name = (name1) in
        ("e_fun", name)

let builtin2str (iface : 'a Dsm.builtinInterface) (name_of_builtins : string) b =
  (* This is only to throw error if we cannot convert it *)
  let _ = Miskeleton.convert_builtin iface b in
  match b with
  | `BuiltinInt n -> "(bi_inject_Z _ builtins_"^name_of_builtins^" (fun a => match a with Some b => b | None => bv_error end) (" ^ (string_of_int n) ^ ")%Z)"
  | `BuiltinString s -> "(bi_inject_string _ builtins_"^name_of_builtins^" (fun a => match a with Some b => b | None => bv_error end) \"" ^ s ^ "\")"
  | _ -> failwith "Unsupported builtin value (for printing into Coq)"

let rec print_groundterm
  (oux : Out_channel.t)
  (iface : 'a Dsm.builtinInterface)
  (name_of_builtins : string)
  (g : Syntax.groundterm) : unit =
  match g with
  | `GTb b ->
      fprintf oux "(@t_over symbol builtin_value ";
      fprintf oux "%s" (builtin2str iface name_of_builtins b);
      fprintf oux ")";
  | `GTerm (`Id s, gs) ->
    fprintf oux "(@t_term symbol builtin_value \"%s\" [" s;
    myiter (fun x -> print_groundterm oux iface name_of_builtins x; ()) (fun () -> fprintf oux "; "; ()) gs;
    fprintf oux "])"


let rec print_resolved_w_hole
  (oux : Out_channel.t)
  (p : Syntax.pattern) (hole : string option) : unit =
  match p with
  | `PVar (`Var s) -> (
      match hole with
      | None ->
          fprintf oux "(t_over (notations.inject_variable \"%s\"))" s
      | Some s2 ->
          if String.(s = s2) then
              fprintf oux "(%s)" s2
          else
              fprintf oux "(t_over (notations.inject_variable \"%s\"))" s
    )
  | `PTerm (`Id s, ps) ->
    fprintf oux "(@t_term _ _ \"%s\" [" s;
    myiter (fun x -> print_resolved_w_hole oux x hole; ()) (fun () -> fprintf oux "; "; ()) ps;
    fprintf oux "])"

let rec print_pattern_w_hole (oux : Out_channel.t) (p : Syntax.pattern) (hole : string option) : unit =
  match p with
  | `PVar (`Var s) -> (
      match hole with
      | None ->
          fprintf oux "(t_over (bov_variable \"%s\"))" s
      | Some s2 ->
          if String.(s = s2) then
              fprintf oux "(%s)" s2
          else
              fprintf oux "(t_over (bov_variable \"%s\"))" s
    )
  | `PTerm (`Id s, ps) ->
    fprintf oux "(@t_term symbol BuiltinOrVar \"%s\" [" s;
    myiter (fun x -> print_pattern_w_hole oux x hole; ()) (fun () -> fprintf oux "; "; ()) ps;
    fprintf oux "])"

let print_pattern (oux : Out_channel.t) (p : Syntax.pattern) : unit =
  print_pattern_w_hole oux p None

let rec print_expr_w_hole
  (iface : 'a Dsm.builtinInterface)
  (my_builtins_map : builtins_map_t)
  (my_query_map : query_map_t)
  (name_of_builtins : string)
  (oux : Out_channel.t)
  (e : Syntax.expr)
  (hole : string option)
  : unit =
  match e with
  | `EVar (`Var s) -> (
        match hole with
        | None -> fprintf oux "(e_variable \"%s\")" s
        | Some s2 ->
            if String.(s = s2) then
                fprintf oux "(%s)" s2
            else
                fprintf oux "(e_variable \"%s\")" s
        )
  | `EGround g ->
    fprintf oux "(e_ground ";
    print_groundterm oux iface name_of_builtins g;
    fprintf oux ")"

  | `ECall (`Id s, es) ->
    let (k, name) = translate_name my_builtins_map my_query_map s in
    fprintf oux "(%s %s [" k name;
    myiter (fun x -> print_expr_w_hole iface my_builtins_map my_query_map name_of_builtins oux x hole; ()) (fun () -> fprintf oux "; "; ()) es;
    fprintf oux "])"



let print_expr
  (iface : 'a Dsm.builtinInterface)
  (my_builtins_map : builtins_map_t)
  (my_query_map : query_map_t)
  (name_of_builtins : string)
  (oux : Out_channel.t)
  (e : Syntax.expr)
  : unit =
  print_expr_w_hole iface my_builtins_map my_query_map name_of_builtins oux e None

let rec print_exprterm
  (iface : 'a Dsm.builtinInterface)
  (my_builtins_map : builtins_map_t)
  (my_query_map : query_map_t)
  (name_of_builtins : string)
  (oux : Out_channel.t)
  (p : Syntax.exprterm)
  : unit =
  match p with
  | `EExpr e -> fprintf oux "(@t_over symbol Expression2"; (print_expr iface my_builtins_map my_query_map name_of_builtins) oux e; fprintf oux ")";
  | `ETerm (`Id s, ps) ->
    fprintf oux "(@t_term symbol Expression2 \"%s\" [" s;
    myiter (fun x -> print_exprterm iface my_builtins_map my_query_map name_of_builtins oux x; ()) (fun () -> fprintf oux "; "; ()) ps;
    fprintf oux "])"

let print_cond_w_hole
  (iface : 'a Dsm.builtinInterface)
  (my_builtins_map : builtins_map_t)
  (my_query_map : query_map_t)
  (name_of_builtins : string)
  (oux : Out_channel.t)
  (c : Syntax.condition)
  (hole : string option)
  : unit =
  match c with
  | `Cond (`Id s, es) ->
      fprintf oux "(mkSideCondition2 _ %s [" (snd (translate_name my_builtins_map my_query_map s));
      myiter (fun x -> print_expr_w_hole iface my_builtins_map my_query_map name_of_builtins oux x hole; ()) (fun () -> fprintf oux "; "; ()) es;
      fprintf oux "])"



let print_rule
  (iface : 'a Dsm.builtinInterface)
  (my_builtins_map : builtins_map_t)
  (my_query_map : query_map_t)
  (name_of_builtins : string)
  (oux : Out_channel.t)
  (r : Syntax.rule) : unit =
    fprintf oux "(";
    (
      match (r.frame) with
      | None -> 
        fprintf oux "basic_rule my_program_info \"%s\" " (r.name)
      | Some (`Id s) ->
        fprintf oux "framed_rule my_program_info frame_%s \"%s\" " s (r.name)
    );
    
    print_pattern oux (r.lhs);
    fprintf oux " ";
    print_exprterm iface my_builtins_map my_query_map name_of_builtins oux (r.rhs);
    fprintf oux " ";
    fprintf oux "[";
    myiter (fun x -> print_cond_w_hole iface my_builtins_map my_query_map name_of_builtins oux x None; ()) (fun () -> fprintf oux "; "; ()) (r.cond);
    fprintf oux "]";
    fprintf oux ")\n";
    ()

let print_frame oux fr =
  fprintf oux "Definition frame_%s : (variable*(TermOver BuiltinOrVar)) := (" (match fr.name with `Id s -> s);
  fprintf oux "\"%s\"" (match fr.var with `Var s -> s);
  fprintf oux ",";
  print_pattern oux (fr.pat);
  fprintf oux ").\n";
  ()

let print_strict oux str =
  fprintf oux "(decl_strict (mkStrictnessDeclaration _ \"%s\" %d " (match str.symbol with `Id s -> s) (str.arity) ;
  fprintf oux "[";
  myiter (fun x -> fprintf oux "%d" x; ()) (fun () -> fprintf oux "; "; ()) (str.strict_places);
  fprintf oux "] isValue isNonValue myContext";
  fprintf oux "))\n";
  ()


let print_mycontext oux ctx =
  fprintf oux "Definition myContext := (context-template ";
  print_resolved_w_hole oux (ctx.pat) (Some (match (ctx.var) with `Var s -> s));
  fprintf oux " with %s).\n" (match ctx.var with `Var s -> s);
  ()  


let print_definition
  (iface : 'a Dsm.builtinInterface)
  (my_builtins_map : builtins_map_t)
  (my_query_map : query_map_t)
  (name_of_builtins : string)
  (name_of_pi : string)
  def oux =
    let _ = def in
    fprintf oux "%s" output_part_1;
    fprintf oux "Definition mybeta := (bi_beta MyUnit builtins_%s).\n" name_of_builtins;
    fprintf oux "#[global] Existing Instance mybeta.\n";
    fprintf oux "Definition my_program_info := %s.MyProgramInfo.\n" name_of_pi;
    fprintf oux "Definition mysigma : StaticModel := (default_everything.DSM my_program_info).\n";
    fprintf oux "Existing Instance mysigma.\n";
    fprintf oux "#[global] Existing Instance pi.%s.MyProgramInfo.\n" name_of_pi;
    print_mycontext oux (def.context);
    
    fprintf oux "Definition isValue (";
    fprintf oux "%s" (match (fst (def.Syntax.value)) with `Var s -> s);
    fprintf oux " : Expression2) := ";
    print_cond_w_hole iface my_builtins_map my_query_map name_of_builtins oux (snd (def.Syntax.value)) (Some (match (fst (def.Syntax.value)) with `Var s -> s));
    fprintf oux ".\n";
    
    fprintf oux "Definition isNonValue (";
    fprintf oux "%s" (match (fst (def.Syntax.nonvalue)) with `Var s -> s);
    fprintf oux " : Expression2) := ";
    print_cond_w_hole iface my_builtins_map my_query_map (name_of_builtins : string) oux (snd (def.Syntax.nonvalue)) (Some (match (fst (def.Syntax.nonvalue)) with `Var s -> s));
    fprintf oux ".\n";
    
    fprintf oux "%s\n" output_part_2;
    List.iter ~f:(fun fr -> print_frame oux fr) (def.frames);
    (* fprintf oux "%s\n" {|
    Definition basic_rule (name : string) (l : TermOver BuiltinOrVar) (r : TermOver Expression2) (cond : Expression2) : Declaration :=
      (decl_rule (@mkRuleDeclaration DSM Act name (@mkRewritingRule2 DSM Act l r [(mkSideCondition2 _ (e_nullary b_true) cond)] default_act)))
    .
    |}; *)
    fprintf oux "Definition Lang_Decls : list Declaration := [\n";
    myiter (fun x -> print_strict oux x; ()) (fun () -> fprintf oux ";" ; ()) (def.Syntax.strictness) ;
    fprintf oux "%s" "] ++ [\n";
    myiter (fun x -> print_rule iface my_builtins_map my_query_map (name_of_builtins : string) oux x; ()) (fun () -> fprintf oux "; "; ()) (def.Syntax.rules);
    fprintf oux "\n].\n";
    ()
    
