From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    varsof
    syntax_properties
.


Definition RewritingRule_wf1
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    : Type
:= 
    let vs1 : gset variable := vars_of (fr_scs r) in
    let vs2 : gset variable := vars_of (fr_from r) in
    (vs1 ⊆ vs2)
.

Definition RewritingRule_wf2'
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    : Type
:= 
    (vars_of (fr_to r) ⊆ vars_of (fr_from r))
.


(*
    This is known as 'weakly well-defined rule'
    in the literature.
*)
Definition RewritingRule_wf2
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    : Type
:= 
    forall (g : GroundTerm) (ρ : Valuation),
        satisfies ρ g (fr_from r) ->
        satisfies ρ () (fr_scs r) ->
        { g' : GroundTerm &
            satisfies ρ g' (fr_to r)
        }
.

Definition RewritingRule_wf
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    : Type
:=
    RewritingRule_wf1 r * RewritingRule_wf2 r
.

Definition RewritingTheory_wf
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    : Type
:=
    forall r, r ∈ Γ -> RewritingRule_wf r
.

Definition rewriting_relation_flat
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule Act))
    : GroundTerm -> GroundTerm -> Type
    := fun from to =>
        { r : _ & { a : _ & ((r ∈ Γ) * flattened_rewrites_to r from a to)%type}}
.

Definition not_stuck_flat
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule Act))
    (e : GroundTerm) : Type
:=
    { e' : _ & rewriting_relation_flat Γ e e' }
.

Definition flat_stuck
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule Act))
    (e : GroundTerm) : Type
:=
    notT (not_stuck_flat Γ e)
.


Definition FlatInterpreter
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule Act))
    : Type
    := GroundTerm -> option GroundTerm
.

Definition FlatInterpreter_sound'
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule Act))
    (interpreter : FlatInterpreter Γ)
    : Type
    := ((
        forall e1 e2,
            interpreter e1 = Some e2 ->
            rewriting_relation_flat Γ e1 e2
    )
    *
    (forall e,
        flat_stuck Γ e -> interpreter e = None)
    * (forall e,
        not_stuck_flat Γ e ->
        exists e', interpreter e = Some e')
    )%type
.


Definition FlatInterpreter_sound
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule Act))
    (interpreter : FlatInterpreter Γ)
    : Type
:= 
    RewritingTheory_wf Γ ->
    FlatInterpreter_sound' Γ interpreter
.
