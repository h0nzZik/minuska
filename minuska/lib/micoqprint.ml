open Base
open Core
open Libminuskapluginbase
open Syntax
open Libminuskapluginbase.Pluginbase
(* 
let myiter (f : 'a -> 'b) (g : unit -> unit) (l : 'a list)  : unit =
    let ln = List.length l in
    List.iteri ~f:(fun idx x -> if (idx + 1 = ln) then (f x) else (f x; g ())) l;
    () *)

let rec groundterm_to_string
    (g : Syntax.groundterm)
    : string =
    match g with
    | `GTb b -> (
      sprintf "(@t_over string BuiltinRepr {|br_kind:=\"%s\";br_value:=\"%s\"|})" (b.br_kind) (b.br_value)
    )
    | `GTerm (`Id s, gs) -> (
    let gs_str = List.map ~f:(groundterm_to_string) gs in
    sprintf "(@t_term string BuiltinRepr \"%s\" %s)" s (Util.format_coq_string_list gs_str)
    )

let rec pattern_w_hole_to_str
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
    let ps_str = List.map ~f:(fun a -> pattern_w_hole_to_str a hole) ps in
    sprintf "(@t_term string StringBuiltinOrVar \"%s\" %s)" s (Util.format_coq_string_list ps_str)
  )

let pattern_to_str (p : Syntax.pattern) : string =
  pattern_w_hole_to_str p None

let rec expr_w_hole_to_str
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
    sprintf "(se_ground %s)" (groundterm_to_string g)
  )
  | `ECallF (`Id s, es) -> (
    let es_str = List.map ~f:(fun a -> expr_w_hole_to_str a hole) es in
    sprintf "(se_applyf \"%s\" %s)" s (Util.format_coq_string_list es_str)
  )
  | `ECallQ (`Id s, es) -> (
    let es_str = List.map ~f:(fun a -> expr_w_hole_to_str a hole) es in
    sprintf "(se_applyq \"%s\" %s)" s (Util.format_coq_string_list es_str)
  )

  let expr_to_str (e : Syntax.expr) : string =
    (expr_w_hole_to_str e None)

let rec exprterm_to_str
    (p : Syntax.exprterm)
    : string =
    match p with
    | `EExpr e -> (
      sprintf "(@t_over string StringExpression %s)" (expr_to_str e)
    )
    | `ETerm (`Id s, ps) -> (
      let ps_str = List.map ~f:(exprterm_to_str) ps in
      sprintf "(@t_term string StringExpression \"%s\" %s)" s (Util.format_coq_string_list ps_str)
    )

let rec cond_w_hole_to_str
  (c : Syntax.condition)
  (hole : string option)
  : string =
  match c with
  | `CondAtomicPred (`Id s, es) -> (
    let es_str = List.map ~f:(fun a -> expr_w_hole_to_str a hole) es in
    sprintf "(ssc_pred \"%s\" %s)" s (Util.format_coq_string_list es_str)
  )
  | `CondAtomicNPred (`Id s, es) -> (
    let es_str = List.map ~f:(fun a -> expr_w_hole_to_str a hole) es in
    sprintf "(ssc_npred \"%s\" %s)" s (Util.format_coq_string_list es_str)
  )
  | `CondAnd (c1, c2) -> (
    sprintf "(ssc_and %s %s)" (cond_w_hole_to_str c1 hole) (cond_w_hole_to_str c2 hole)
  )
  | `CondOr (c1, c2) -> (
    sprintf "(ssc_or %s %s)" (cond_w_hole_to_str c1 hole) (cond_w_hole_to_str c2 hole)
  )
  | `CondTrue -> (
    "ssc_true"
  )
  | `CondFalse -> (
    "ssc_false"
  )

let cond_to_str
    (c : Syntax.condition)
    : string =
    (cond_w_hole_to_str c None)

let rule_to_str
    (r : Syntax.rule)
    : string =
    let kind : string = (match r.frame with
      | None -> (sprintf "basic_rule \"%s\"" (r.name))
      | Some (`Id s) -> (
        sprintf "framed_rule frame_%s \"%s\"" s (r.name)
      )
    ) in
    sprintf "(%s %s %s %s)" kind (pattern_to_str r.lhs) (exprterm_to_str r.rhs) (cond_to_str r.cond)

let frame_to_str fr : string =
  sprintf "(\"%s\",%s)" (match fr.fd_var with `Var s -> s) (pattern_to_str fr.fd_pat)

let frame_definition_to_str fr : string =
  sprintf "Definition frame_%s : (string*(@TermOver' string StringBuiltinOrVar)) := %s.\n" (match fr.fd_name with `Id s -> s) (frame_to_str fr)

let decl_strict_to_str strictness : string = (
  sprintf "(decl_strict Label (mkStrictnessDeclaration \"%s\" %d %s isValue myContext))\n"
    (match strictness.symbol with `Id s -> s)
    (strictness.arity)
    (Util.format_coq_string_list (List.map ~f:(fun a -> sprintf "%d" a) strictness.strict_places))
)

let mycontext_decl_to_str ctx : string = (
  let vname = (match (ctx.cd_var) with `Var s -> s) in
  sprintf "Definition myContext := (fun (%s : @TermOver' string StringBuiltinOrVar) => %s).\n" vname (pattern_w_hole_to_str (ctx.cd_pat) (Some vname))
)

let isvalue_decl_to_str value : string = (
  let varname = (match (fst (value)) with `Var s -> s) in
  sprintf "Definition isValue (%s : StringExpression) := %s.\n" varname (cond_w_hole_to_str (snd value) (Some varname))
)

(* This expects an instance of a StaticModel to be in context. *)
let definition_to_str def : string = (
  sprintf
{delimiter|
Require Import Minuska.pval_ocaml_binding Minuska.default_everything.
  %s
  %s
#[local]
Instance LangDefaults : Defaults := mkDefaults "builtin.cseq" "builtin.empty_cseq" myContext isValue.
  
%s
Definition Lang_Decls : list (Declaration Label) :=
  (%s)
  ++
  (%s)
. (* Lang_Decls *)
|delimiter}
  (mycontext_decl_to_str (def.context))
  (isvalue_decl_to_str (def.Syntax.value))
  (Util.format_string_list_per_line (List.map ~f:(frame_definition_to_str) def.frames))
  (Util.format_coq_string_list_per_line (List.map ~f:(decl_strict_to_str) def.Syntax.strictness))
  (Util.format_coq_string_list_per_line (List.map ~f:(rule_to_str) def.Syntax.rules))
)
