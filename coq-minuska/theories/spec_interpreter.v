From Minuska Require Import
    prelude
    spec
.


Definition not_stuck
    {Σ : BackgroundModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (program : ProgramT)
    (e : (@TermOver' TermSymbol BasicValue)*(HiddenValue)) : Type
:=
    { e' : _ & { nv : NondetValue & rewriting_relation Γ program nv e e' } }
.

Definition stuck
    {Σ : BackgroundModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (program : ProgramT)
    (e : (@TermOver' TermSymbol BasicValue)*(HiddenValue)) : Type
:=
    notT (not_stuck Γ program e)
.


Definition Interpreter
    {Σ : BackgroundModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    : Type
    := ProgramT -> NondetValue -> (@TermOver' TermSymbol BasicValue)*(HiddenValue) -> option ((@TermOver' TermSymbol BasicValue)*(HiddenValue))
.

Definition Interpreter_ext
    {Σ : BackgroundModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    : Type
    := ProgramT -> NondetValue -> (@TermOver' TermSymbol BasicValue)*(HiddenValue) -> option (((@TermOver' TermSymbol BasicValue)*(HiddenValue))*nat)
.


Definition Interpreter_sound'
    {Σ : BackgroundModel}
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

Definition RewritingRule2'_wf
    {Bv Va Ts Fs Qs As Ms Ps Hps : Type}
    {_Ev : EqDecision Va}
    {_Cv : Countable Va}
    {Label : Set}
    (r : @RewritingRule2' Bv Va Ts Fs Qs As Ms Ps Hps Label)
    : Prop
:=
    vars_of (r_scs r) ⊆ vars_of (r_from r)
    /\
    vars_of (r_to r) ⊆ vars_of (r_from r)
    /\
    vars_of (r_eff r) ⊆ vars_of (r_from r)
.

Definition RewritingRule2_wf
    {Σ : BackgroundModel}
    {Label : Set}
    (r : RewritingRule2 Label)
    : Prop
:=
  RewritingRule2'_wf r
.

Definition RewritingTheory2'_wf
    {Bv Va Ts Fs Qs As Ms Ps Hps : Type}
    {_Ev : EqDecision Va}
    {_Cv : Countable Va}
    {Label : Set}
    (Γ : list (@RewritingRule2' Bv Va Ts Fs Qs As Ms Ps Hps Label))
    : Prop
:=
    Forall RewritingRule2'_wf Γ
.


Definition RewritingTheory2_wf
    {Σ : BackgroundModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    : Prop
:=
    RewritingTheory2'_wf Γ
.

Definition Interpreter_sound
    {Σ : BackgroundModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (interpreter : Interpreter Γ)
    : Type
:= 
    RewritingTheory2_wf Γ ->
    Interpreter_sound' Γ interpreter
.

