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

Definition SymbolicInterpreter
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Type :=
    OpenTerm -> list OpenTerm   
.

Definition OpenTerm_not_stuck
    {Σ : Signature}
    (Γ : RewritingTheory)
    (φ : OpenTerm)
    : Prop
    := ∃ g,
        GroundTerm_satisfies_OpenTerm g φ /\
        not_stuck Γ g
.

Definition OpenTerm_stuck
    {Σ : Signature}
    (Γ : RewritingTheory)
    (φ : OpenTerm)
    : Prop
    := ~ OpenTerm_not_stuck Γ φ
.


Definition SymbolicInterpreter_sound
    {Σ : Signature}
    (Γ : RewritingTheory)
    (symbolic_interpreter : SymbolicInterpreter Γ)
    : Prop :=
    (forall (φ φ': OpenTerm),
        φ' ∈ symbolic_interpreter φ ->
            forall (g g' : GroundTerm),
                GroundTerm_satisfies_OpenTerm g φ ->
                GroundTerm_satisfies_OpenTerm g' φ' ->
                rewriting_relation Γ g g'
                
    ) /\ (
        forall (φ : OpenTerm),
            forall (g g' : GroundTerm),
                GroundTerm_satisfies_OpenTerm g φ ->
                rewriting_relation Γ g g' ->
                exists (φ' : OpenTerm),
                    φ' ∈ symbolic_interpreter φ /\
                    GroundTerm_satisfies_OpenTerm g' φ'
    )
.
