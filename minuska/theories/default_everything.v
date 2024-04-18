From Minuska Require Import
    prelude
    spec
    string_variables
    builtins
    default_static_model
    frontend
    properties
.

Variant Act := default_act | invisible_act.

#[export]
Instance DSM : StaticModel :=
    default_model (default_builtin.β)
.

Definition GT := @TermOver' string builtin_value.

Definition StepT := GT -> option GT.

Definition gt_term (s : string) (l : list GT) : GT := @t_term string builtin_value s l.
(*
Definition gt_over b := term_over b.
*)

Definition basic_rule
    (name : string)
    (l : TermOver BuiltinOrVar)
    (r : TermOver Expression2)
    (cond : Expression2) : Declaration
:=
    (decl_rule (@mkRuleDeclaration DSM Act name (@mkRewritingRule2 DSM Act l r [(mkSideCondition2 _ (e_nullary default_builtin.b_true) cond)] default_act)))
.


Definition BoV_to_Expr2
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : Expression2
:=
    match bov with
    | bov_builtin b => (e_ground (t_over b))
    | bov_variable x => e_variable x
    end
.

About TermOverBoV_subst_expr2.

Definition framed_rule
    (frame : (variable*(TermOver BuiltinOrVar)))
    (name : string)
    (l : TermOver BuiltinOrVar)
    (r : TermOver Expression2)
    (cond : Expression2) : Declaration
:=
    (decl_rule (@mkRuleDeclaration DSM Act name (@mkRewritingRule2 DSM Act
        (TermOverBoV_subst frame.2 frame.1 l)
        (TermOverBoV_subst_expr2 frame.2 frame.1 r)
        [(mkSideCondition2 _ (e_nullary default_builtin.b_true) cond)] default_act)))
.

