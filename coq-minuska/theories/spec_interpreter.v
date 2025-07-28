From Minuska Require Import
    prelude
    spec
.


Definition not_stuck
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (program : ProgramT)
    (e : (TermOver builtin_value)*(hidden_data)) : Type
:=
    { e' : _ & { nv : NondetValue & rewriting_relation Γ program nv e e' } }
.

Definition stuck
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (program : ProgramT)
    (e : (TermOver builtin_value)*(hidden_data)) : Type
:=
    notT (not_stuck Γ program e)
.


Definition Interpreter
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    : Type
    := ProgramT -> NondetValue -> (TermOver builtin_value)*(hidden_data) -> option ((TermOver builtin_value)*(hidden_data))
.

Definition Interpreter_ext
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    : Type
    := ProgramT -> NondetValue -> (TermOver builtin_value)*(hidden_data) -> option (((TermOver builtin_value)*(hidden_data))*nat)
.


Definition Interpreter_sound'
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
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
    {Label : Set}
    (r : RewritingRule2 Label)
    : Prop
:=
    vars_of (r_scs r) ⊆ vars_of (r_from r)
    /\
    vars_of (r_to r) ⊆ vars_of (r_from r)
    /\
    vars_of (r_eff r) ⊆ vars_of (r_from r)
.

Definition RewritingTheory2_wf
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    : Prop
:=
    Forall RewritingRule2_wf Γ
.

Definition Interpreter_sound
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (interpreter : Interpreter Γ)
    : Type
:= 
    RewritingTheory2_wf Γ ->
    Interpreter_sound' Γ interpreter
.

