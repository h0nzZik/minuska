From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
.


Definition Interpreter
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Type
    := GroundTerm -> option GroundTerm
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
    := GroundTerm -> list GroundTerm
.

Definition Explorer_sound
    {Σ : Signature}
    (Γ : RewritingTheory)
    (explorer : Explorer Γ)
    : Prop
    := forall (e e' : GroundTerm),
        e' ∈ explorer e <-> rewriting_relation Γ e e'
.

