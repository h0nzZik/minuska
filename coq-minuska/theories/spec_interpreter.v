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

Definition RewritingRule2_wf
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    : Prop
:=
    vars_of (r_scs r) ⊆ vars_of (r_from r)
    /\
    vars_of (r_to r) ⊆ vars_of (r_from r)
.

Definition RewritingTheory2_wf
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    : Prop
:=
    Forall RewritingRule2_wf Γ
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

