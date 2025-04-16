From Minuska Require Import
    prelude
    spec
.


Inductive Emptyset : Set := .

#[export]
Instance emptyset_eqdec : EqDecision Emptyset.
Proof.
    intros x y.
    destruct x, y.
Defined.

#[export]
Program Instance emptyset_fin : Finite Emptyset := {|
    enum := [];
|}.
Next Obligation.
    constructor.
Qed.
Next Obligation.
    destruct x.
Qed.
Fail Next Obligation.

Inductive TrivialPVA : Set := pv_error.

#[export]
Instance TrivialPVA_eqdec : EqDecision TrivialPVA.
Proof.
    ltac1:(solve_decision).
Defined.



#[export]
Program Instance TrivialPVA_fin : Finite TrivialPVA := {|
    enum := [pv_error];
|}.
Next Obligation.
    repeat constructor; ltac1:(set_solver).
Qed.
Next Obligation.
    destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.


Section sec.

    Context
        {symbol : Set}
        {symbols : Symbols symbol}
    .

    #[local]
    Instance mysignature : Signature := {|
        builtin_function_symbol
            := Emptyset ;
        builtin_predicate_symbol
            := Emptyset ;
    |}.

    Definition βover
        : ModelOver mysignature MyUnit TrivialPVA := {|
        builtin_function_interp
            := fun _ _ _ => t_over pv_error ;
        builtin_predicate_interp
            := fun _ _ _ => false ;
    |}.

    #[local]
    Instance β
        : @Model _ _ mysignature MyUnit := {|
        builtin_value
            := TrivialPVA ;
        builtin_model_over := βover ;
    |}.

End sec.

Definition builtins_binding : BuiltinsBinding := {|
    bb_function_names := [] ;
|}.

Definition inject_err
    {symbol : Type}
    :
    TrivialPVA
:=
    pv_error
.

Definition inject_bool
    {symbol : Type}
    (Fret : option TrivialPVA -> TrivialPVA)
    (b : bool)
    :
    TrivialPVA :=
    Fret None
.

Definition inject_Z
    {symbol : Type}
    (Fret : option TrivialPVA -> TrivialPVA)
    (z : Z)
    :
    TrivialPVA :=
    Fret None
.

Definition inject_string
    {symbol : Type}
    (Fret : option TrivialPVA -> TrivialPVA)
    (s : string)
    :
    TrivialPVA :=
    Fret None
.

Definition eject
    {symbol : Type}
    (v : TrivialPVA)
    :
    option (bool+(Z+(string+unit)))%type
    :=
    None
.