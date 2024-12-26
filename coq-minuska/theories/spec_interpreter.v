From Minuska Require Import
    prelude
    spec
.


Definition not_stuck
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    (e : TermOver builtin_value) : Type
:=
    { e' : _ & { nv : NondetValue & rewriting_relation Γ program nv e e' } }
.

Definition stuck
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    (e : TermOver builtin_value) : Type
:=
    notT (not_stuck Γ program e)
.


Definition Interpreter
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    : Type
    := ProgramT -> NondetValue -> TermOver builtin_value -> option (TermOver builtin_value)
.

Definition Interpreter_ext
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    : Type
    := ProgramT -> NondetValue -> TermOver builtin_value -> option ((TermOver builtin_value)*nat)
.


Definition Interpreter_sound'
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (interpreter : Interpreter Γ)
    : Type
    := ((
        forall program e1 e2 nv,
            interpreter program nv e1 = Some e2 ->
            rewriting_relation Γ program nv e1 e2
    )
    *
    (forall program e,
        stuck Γ program e -> forall nv, interpreter program nv e = None)
    * (forall program e,
        not_stuck Γ program e ->
        exists e' (nv : NondetValue), interpreter program nv e = Some e')
    )%type
.

Definition RewritingRule2_wf1
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    : Type
:= 
    let vs1 : gset variable := vars_of (r_scs r) in
    let vs2 : gset variable := vars_of (r_from r) in
    (vs1 ⊆ vs2)
.

Definition RewritingRule2_wf2'
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    : Type
:= 
    (vars_of (r_to r) ⊆ vars_of (r_from r))
.


(*
    This is known as 'weakly well-defined rule'
    in the literature.
*)
Definition RewritingRule2_wf2
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    : Type
:= 
    forall (g : TermOver builtin_value) (ρ : Valuation2) (program : ProgramT) (nv : NondetValue),
        satisfies ρ g (r_from r) ->
        satisfies ρ (program, nv) (r_scs r) ->
        { g' : (TermOver builtin_value) &
            satisfies ρ (program, (nv,g')) (r_to r)
        }
.

Definition RewritingRule2_wf
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    : Type
:=
    RewritingRule2_wf1 r * RewritingRule2_wf2 r
.

Definition RewritingTheory2_wf
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    : Type
:=
    forall r, r ∈ Γ -> RewritingRule2_wf r
.


Definition Interpreter_sound
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (interpreter : Interpreter Γ)
    : Type
:= 
    RewritingTheory2_wf Γ ->
    Interpreter_sound' Γ interpreter
.

