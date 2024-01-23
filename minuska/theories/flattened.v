From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    syntax_properties
.


Record FlattenedRewritingRule {Σ : StaticModel}
:= mkFlattenedRewritingRule
{
    fr_from : OpenTerm ;
    fr_to : RhsPattern ;
    fr_scs : list SideCondition ;
}.

Definition flattened_rewrites_in_valuation_to
    {Σ : StaticModel}
    (ρ : Valuation)
    (r : FlattenedRewritingRule)
    (from to : GroundTerm)
    : Prop
:= satisfies ρ from (fr_from r)
/\ satisfies ρ to (fr_to r)
/\ satisfies ρ () (fr_scs r)
.

Definition flattened_rewrites_to
    {Σ : StaticModel}
    (r : FlattenedRewritingRule)
    (from to : GroundTerm)
    : Prop
:= exists ρ, flattened_rewrites_in_valuation_to ρ r from to
.

Definition FRR_wf
    {Σ : StaticModel}
    (r : FlattenedRewritingRule)
    : Prop
:=
    vars_of (fr_to r) ⊆ vars_of (fr_from r)
    (* TODO: add a requirement saying that all variables that occur on the lhs
       of some constraint, and specifically a pattern matching constraint,
       are reachable from the set of variables occuring in `fr_from r`
       in the graph induced by the list of pattern matching goals
    *)
.


Fixpoint AppliedOperator'_symbol_A_to_OpenTermB
    {Σ : StaticModel}
    {A B : Type}
    (A_to_OpenTermB : A ->
        ((AppliedOperatorOr' symbol B))
    )
    (x : AppliedOperator' symbol A)
    : ((AppliedOperator' symbol B))
:=
match x with
| ao_operator a => (ao_operator a)
| ao_app_operand x' a =>
    let t1 : (AppliedOperator' symbol B)
        := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x' in
    match A_to_OpenTermB a with
    | (aoo_app t2) => (ao_app_ao t1 t2)
    | (aoo_operand t2) => (ao_app_operand t1 t2)
    end
| ao_app_ao x1 x2 =>
    let t1 : (AppliedOperator' symbol B)
        := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x1 in
    let t2 : (AppliedOperator' symbol B)
        := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x2 in
    ao_app_ao t1 t2
end.

Definition AppliedOperatorOr'_symbol_A_to_OpenTermB
    {Σ : StaticModel}
    {A B : Type}
    (A_to_OpenTermB : A ->
        ((AppliedOperatorOr' symbol B))
    )
    (x : AppliedOperatorOr' symbol A)
    : ((AppliedOperatorOr' symbol B))
:=
match x with
| aoo_app app => aoo_app (AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB app)
| aoo_operand operand => A_to_OpenTermB operand
end.


Definition FlattenedRewritingRule_wf1
    {Σ : StaticModel}
    (r : FlattenedRewritingRule)
    : Prop
:= 
    let vs1 : gset variable := vars_of (fr_scs r) in
    let vs2 : gset variable := vars_of (fr_from r) in
    (vs1 ⊆ vs2)
.

(*
    This is known as 'weakly well-defined rule'
    in the literature.
*)
Definition FlattenedRewritingRule_wf2
    {Σ : StaticModel}
    (r : FlattenedRewritingRule)
    : Prop
:= 
    forall (g : GroundTerm) (ρ : Valuation),
        satisfies ρ g (fr_from r) ->
        satisfies ρ () (fr_scs r) ->
        exists (g' : GroundTerm),
            satisfies ρ g' (fr_to r)
.

Definition FlattenedRewritingRule_wf
    {Σ : StaticModel}
    (r : FlattenedRewritingRule)
    : Prop
:=
    FlattenedRewritingRule_wf1 r /\ FlattenedRewritingRule_wf2 r
.


Definition FlattenedRewritingTheory {Σ : StaticModel}
    := list FlattenedRewritingRule
.

Definition FlattenedRewritingTheory_wf
    {Σ : StaticModel}
    (Γ : FlattenedRewritingTheory)
    : Prop
:=
    Forall FlattenedRewritingRule_wf Γ
.

Definition rewriting_relation_flat
    {Σ : StaticModel}
    (Γ : list FlattenedRewritingRule)
    : relation GroundTerm
    := fun from to =>
        exists r, r ∈ Γ /\ flattened_rewrites_to r from to
.

Definition not_stuck_flat
    {Σ : StaticModel}
    (Γ : list FlattenedRewritingRule)
    (e : GroundTerm) : Prop
:= exists e', rewriting_relation_flat Γ e e'.

Definition flat_stuck
    {Σ : StaticModel}
    (Γ : list FlattenedRewritingRule)
    (e : GroundTerm) : Prop
:= not (not_stuck_flat Γ e).


Definition FlatInterpreter
    {Σ : StaticModel}
    (Γ : list FlattenedRewritingRule)
    : Type
    := GroundTerm -> option GroundTerm
.

Definition FlatInterpreter_sound
    {Σ : StaticModel}
    (Γ : list FlattenedRewritingRule)
    (wfΓ : FlattenedRewritingTheory_wf Γ)
    (interpreter : FlatInterpreter Γ)
    : Prop
    := (forall e,
        flat_stuck Γ e -> interpreter e = None)
    /\ (forall e,
        not_stuck_flat Γ e ->
        exists e', interpreter e = Some e')
.
