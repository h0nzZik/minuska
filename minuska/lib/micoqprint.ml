open Base
open Core
open Libminuskapluginbase
open Syntax
open Libminuskapluginbase.Pluginbase

type builtins_map_t = (string, string, String.comparator_witness) Map.t ;;
type query_map_t = (string, string, String.comparator_witness) Map.t ;;

let myiter (f : 'a -> 'b) (g : unit -> unit) (l : 'a list)  : unit =
    let ln = List.length l in
    List.iteri ~f:(fun idx x -> if (idx + 1 = ln) then (f x) else (f x; g ())) l;
    ()

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

let rec groundterm_to_string
    (pvae : primitiveValueAlgebraEntry)
    (g : Syntax.groundterm)
    : string =
    match g with
    | `GTb b -> (
      sprintf "(@t_over string string \"%s\")" (pvae.pvae_builtin_coq_quote b)
    )
      | `GTerm (`Id s, gs) -> (
      let gs_str = List.map ~f:(groundterm_to_string pvae) gs in
      sprintf "(@t_term string string \"%s\" %s)" s (Util.format_coq_string_list gs_str)
      )

let rec pattern_w_hole_to_str
  (pvae : primitiveValueAlgebraEntry)
    (p : Syntax.pattern)
    (hole : string option)
    : string =
  match p with
  | `PVar (`Var s) -> (
      match hole with
      | None -> (
        sprintf "(t_over (sbov_var \"%s\"))" s
      )
      | Some s2 -> (
        if String.(s=s2) then
          sprintf "(%s)" s2
        else
          sprintf "(t_over (sbov_var \"%s\"))" s
      )
  )
  | `PTerm (`Id s, ps) -> (
    let ps_str = List.map ~f:(fun a -> pattern_w_hole_to_str pvae a hole) ps in
    sprintf "(@t_term string StringBuiltinOrVar \"%s\" %s)" s (Util.format_coq_string_list ps_str)
  )

let pattern_to_str (pvae : primitiveValueAlgebraEntry) (p : Syntax.pattern) : string =
  pattern_w_hole_to_str pvae p None

let rec expr_w_hole_to_str
  (pvae : primitiveValueAlgebraEntry)
  (e : Syntax.expr)
  (hole : string option)
  : string
  =
  match e with
  | `EVar (`Var s) -> (
    match hole with
    | None -> (
      sprintf "(se_variable \"%s\")" s
    )
    | Some s2 -> (
      if String.(s = s2) then (
        sprintf "(%s)" s2
      ) else (
        sprintf "(se_variable \"%s\")" s
      )
    )
  )
  | `EGround g -> (
    sprintf "(se_ground %s)" (groundterm_to_string pvae g)
  )
  | `ECall (`Id s, es) -> (
    let es_str = List.map ~f:(fun a -> expr_w_hole_to_str pvae a hole) es in
    sprintf "(se_apply \"%s\" %s)" s (Util.format_coq_string_list es_str)
  )

  let expr_to_str (pvae : primitiveValueAlgebraEntry) (e : Syntax.expr) : string =
    (expr_w_hole_to_str pvae e None)

let rec exprterm_to_str
    (pvae : primitiveValueAlgebraEntry)
    (p : Syntax.exprterm)
    : string =
    match p with
    | `EExpr e -> (
      sprintf "(@t_over string StringExpression %s)" (expr_to_str pvae e)
    )
    | `ETerm (`Id s, ps) -> (
      let ps_str = List.map ~f:(exprterm_to_str pvae) ps in
      sprintf "(@t_term string StringExpression \"%s\" %s)" s (Util.format_coq_string_list ps_str)
    )

let rec cond_w_hole_to_str
  (pvae : primitiveValueAlgebraEntry)
  (c : Syntax.condition)
  (hole : string option)
  : string =
  match c with
  | `CondAtomic (`Id s, es) -> (
    let es_str = List.map ~f:(expr_to_str pvae) es in
    sprintf "(ssc_atom \"%s\" %s)" s (Util.format_coq_string_list es_str)
  )
  | `CondAnd (c1, c2) -> (
    sprintf "(ssc_and %s %s)" (cond_w_hole_to_str pvae c1 hole) (cond_w_hole_to_str pvae c2 hole)
  )
  | `CondOr (c1, c2) -> (
    sprintf "(ssc_or %s %s)" (cond_w_hole_to_str pvae c1 hole) (cond_w_hole_to_str pvae c2 hole)
  )
  | `CondTrue -> (
    "ssc_true"
  )
  | `CondFalse -> (
    "ssc_false"
  )

let cond_to_str
  (pvae : primitiveValueAlgebraEntry)
    (c : Syntax.condition)
    : string =
    (cond_w_hole_to_str pvae c None)

let rule_to_str
    (pvae : primitiveValueAlgebraEntry)
    (r : Syntax.rule)
    : string =
    let kind : string = (match r.frame with
      | None -> (sprintf "basic_rule \"%s\"" (r.name))
      | Some (`Id s) -> (
        sprintf "framed_rule frame_%s \"%s\"" s (r.name)
      )
    ) in
    sprintf "(%s %s %s %s)" kind (pattern_to_str pvae r.lhs) (exprterm_to_str pvae r.rhs) (cond_to_str pvae r.cond)

let frame_to_str (pvae : primitiveValueAlgebraEntry) fr : string =
  sprintf "(\"%s\",%s)" (match fr.fd_var with `Var s -> s) (pattern_to_str pvae fr.fd_pat)

let frame_definition_to_str (pvae : primitiveValueAlgebraEntry) fr : string =
  sprintf "Definition frame_%s : (variable*(TermOver StringBuiltinOrVar)) := %s.\n" (match fr.fd_name with `Id s -> s) (frame_to_str pvae fr)

let decl_strict_to_str strictness : string = (
  sprintf "(decl_strict (mkStrictnessDeclaration _ \"%s\" %d %s isValue myContext))\n"
    (match strictness.symbol with `Id s -> s)
    (strictness.arity)
    (Util.format_coq_string_list (List.map ~f:(fun a -> sprintf "%d" a) strictness.strict_places))
)

let mycontext_decl_to_str (pvae : primitiveValueAlgebraEntry) ctx : string = (
  let vname = (match (ctx.cd_var) with `Var s -> s) in
  sprintf "Definition myContext := (fun (%s : @TermOver' string StringBuiltinOrVar) => %s).\n" vname (pattern_w_hole_to_str pvae (ctx.cd_pat) (Some vname))
)

let isvalue_decl_to_str (pvae : primitiveValueAlgebraEntry) value : string = (
  let varname = (match (fst (value)) with `Var s -> s) in
  sprintf "Definition isValue (%s : StringExpression) := %s.\n" varname (cond_w_hole_to_str pvae (snd value) (Some varname))
)


let definition_to_str (pvae : primitiveValueAlgebraEntry) pi def : string = (
  let builtins_import = (pvae.pvae_coq_import) in
  let builtins_name = pvae.pvae_coq_entity_name in
  sprintf
{delimiter|
Require Import Minuska.pval_ocaml_binding %s %s Minuska.default_everything.
Definition mysignature := (bi_signature MyUnit %s).
#[global] Existing Instance mysignature.
Definition mybeta := (bi_beta MyUnit %s).
#[global] Existing Instance mybeta.
Definition my_program_info := %s.
Definition mysigma : StaticModel := (default_everything.DSM my_program_info).
#[global] Existing Instance mysigma.
#[global] Existing Instance my_program_info.
  %s
  %s
#[local]
Instance LangDefaults : Defaults := mkDefaults "builtin.cseq" "builtin.empty_cseq" myContext isValue.
  
%s
Definition Lang_Decls : list (Declaration Act) :=
  (%s)
  ++
  (%s)
. (* Lang_Decls *)
|delimiter}

  builtins_import
  (pi.pie_coq_import)
  builtins_name
  builtins_name
  (pi.pie_coq_entity_name)
  (mycontext_decl_to_str pvae (def.context))
  (isvalue_decl_to_str pvae (def.Syntax.value))
  (Util.format_string_list_per_line (List.map ~f:(frame_definition_to_str pvae) def.frames))
  (Util.format_coq_string_list_per_line (List.map ~f:(decl_strict_to_str) def.Syntax.strictness))
  (Util.format_coq_string_list_per_line (List.map ~f:(rule_to_str pvae) def.Syntax.rules))
)
