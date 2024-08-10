From Minuska Require Import
    prelude
    spec
.


Definition not_stuck
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (e : TermOver builtin_value) : Type
:=
    { e' : _ & { nv : NondetValue & rewriting_relation Γ nv e e' } }
.

Definition stuck
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (e : TermOver builtin_value) : Type
:=
    notT (not_stuck Γ e)
.


Definition Interpreter
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    : Type
    := NondetValue -> TermOver builtin_value -> option (TermOver builtin_value)
.

Definition Interpreter_sound'
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (interpreter : Interpreter Γ)
    : Type
    := ((
        forall e1 e2 nv,
            interpreter nv e1 = Some e2 ->
            rewriting_relation Γ nv e1 e2
    )
    *
    (forall e,
        stuck Γ e -> forall nv, interpreter nv e = None)
    * (forall e,
        not_stuck Γ e ->
        exists e' (nv : NondetValue), interpreter nv e = Some e')
    )%type
.


Definition Interpreter_sound
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (interpreter : Interpreter Γ)
    : Type
:= 
    (* TODO replace with RewritingTheory2_wf_alt *)
    RewritingTheory2_wf Γ ->
    Interpreter_sound' Γ interpreter
.

