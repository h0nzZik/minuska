From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
.


Record FlattenedRewritingRule {Σ : Signature} := {
    fr_from : OpenTerm ;
    fr_to : RhsPattern ;
    fr_scs : list SideCondition ;
}.

Definition flattened_rewrites_in_valuation_to
    {Σ : Signature}
    (ρ : Valuation)
    (r : FlattenedRewritingRule)
    (from to : GroundTerm)
    : Prop
:= satisfies ρ from (fr_from r)
/\ satisfies ρ to (fr_to r)
/\ satisfies ρ () (fr_scs r)
.

Definition flattened_rewrites_to
    {Σ : Signature}
    (r : FlattenedRewritingRule)
    (from to : GroundTerm)
    : Prop
:= exists ρ, flattened_rewrites_in_valuation_to ρ r from to
.

Definition FRR_wf
    {Σ : Signature}
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
    {Σ : Signature}
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
    | (aoo_app _ _ t2) => (ao_app_ao t1 t2)
    | (aoo_operand _ _ t2) => (ao_app_operand t1 t2)
    end
| ao_app_ao x1 x2 =>
    let t1 : (AppliedOperator' symbol B)
        := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x1 in
    let t2 : (AppliedOperator' symbol B)
        := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x2 in
    ao_app_ao t1 t2
end.

Definition AppliedOperatorOr'_symbol_A_to_OpenTermB
    {Σ : Signature}
    {A B : Type}
    (A_to_OpenTermB : A ->
        ((AppliedOperatorOr' symbol B))
    )
    (x : AppliedOperatorOr' symbol A)
    : ((AppliedOperatorOr' symbol B))
:=
match x with
| aoo_app _ _ app => aoo_app _ _ (AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB app)
| aoo_operand _ _ operand => A_to_OpenTermB operand
end.

Definition FlattenedRewritingTheory {Σ : Signature}
    := list FlattenedRewritingRule
.

Definition rewriting_relation_flat
    {Σ : Signature}
    (Γ : list FlattenedRewritingRule)
    : relation GroundTerm
    := fun from to =>
        exists r, r ∈ Γ /\ flattened_rewrites_to r from to
.

Definition not_stuck_flat
    {Σ : Signature}
    (Γ : list FlattenedRewritingRule)
    (e : GroundTerm) : Prop
:= exists e', rewriting_relation_flat Γ e e'.

Definition flat_stuck
    {Σ : Signature}
    (Γ : list FlattenedRewritingRule)
    (e : GroundTerm) : Prop
:= not (not_stuck_flat Γ e).


Definition FlatInterpreter
    {Σ : Signature}
    (Γ : list FlattenedRewritingRule)
    : Type
    := GroundTerm -> option GroundTerm
.

Definition FlatInterpreter_sound
    {Σ : Signature}
    (Γ : list FlattenedRewritingRule)
    (interpreter : FlatInterpreter Γ)
    : Prop
    := (forall e,
        flat_stuck Γ e -> interpreter e = None)
    /\ (forall e,
        not_stuck_flat Γ e ->
        exists e', interpreter e = Some e')
.
