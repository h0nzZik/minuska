
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
.


Module Semantics.
    Import Syntax.


    Definition rewrites_in_valuation_to
        {Σ : Signature} (ρ : Valuation) (r : RewritingRule) (from to : Value)
        : Prop
    := rr_satisfies LR_Left ρ r from
    /\ rr_satisfies LR_Right ρ r to
    .

    Definition rewrites_to
        {Σ : Signature} (r : RewritingRule) (from to : Value)
        : Prop
    := exists ρ, rewrites_in_valuation_to ρ r from to
    .

    Definition RewritingTheory {Σ : Signature}
        := list RewritingRule
    .

    Definition rewriting_relation
        {Σ : Signature}
        (Γ : RewritingTheory)
        : relation Value
        := fun from to =>
            exists r, r ∈ Γ /\ rewrites_to r from to
    .

    Definition not_stuck
        {Σ : Signature}
        (Γ : RewritingTheory)
        (e : Value) : Prop
    := exists e', rewriting_relation Γ e e'.

    Definition stuck
        {Σ : Signature}
        (Γ : RewritingTheory)
        (e : Value) : Prop
    := not (not_stuck Γ e).

End Semantics.

Definition Interpreter
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Type
    := Value -> option Value
.

Definition Interpreter_sound
    {Σ : Signature}
    (Γ : RewritingTheory)
    (interpreter : Interpreter Γ)
    : Prop
    := (forall e,
        stuck Γ e -> interpreter e = None)
    /\ (forall e,
        not_stuck Γ e ->
        exists e', interpreter e = Some e')
.

Definition Explorer
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Type
    := Value -> list Value
.

Definition Explorer_sound
    {Σ : Signature}
    (Γ : RewritingTheory)
    (explorer : Explorer Γ)
    : Prop
    := forall (e e' : Value),
        e' ∈ explorer e <-> rewriting_relation Γ e e'
.




