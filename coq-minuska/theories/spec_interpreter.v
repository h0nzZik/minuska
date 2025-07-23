From Minuska Require Import
    prelude
    spec
.


Definition not_stuck
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (program : ProgramT)
    (h : hidden_data)
    (e : TermOver builtin_value) : Type
:=
    { e' : _ & { nv : NondetValue & rewriting_relation Γ program h nv e e' } }
.

Definition stuck
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (program : ProgramT)
    (h : hidden_data)
    (e : TermOver builtin_value) : Type
:=
    notT (not_stuck Γ program h e)
.


Definition Interpreter
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    : Type
    := ProgramT -> hidden_data -> NondetValue -> TermOver builtin_value -> option (TermOver builtin_value)
.

Definition Interpreter_ext
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    : Type
    := ProgramT -> hidden_data -> NondetValue -> TermOver builtin_value -> option ((TermOver builtin_value)*nat)
.


Definition Interpreter_sound'
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (interpreter : Interpreter Γ)
    : Type
    := ((
        forall program h e1 e2 nv,
            interpreter program h nv e1 = Some e2 ->
            rewriting_relation Γ program h nv e1 e2
    )
    *
    (forall program h e,
        stuck Γ program h e -> forall nv, interpreter program h nv e = None)
    * (forall program h e,
        not_stuck Γ program h e ->
        exists e' (nv : NondetValue), interpreter program h nv e = Some e')
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

