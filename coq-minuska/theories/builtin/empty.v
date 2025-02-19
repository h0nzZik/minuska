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


Inductive TrivialPVA : Set := pv_error.

#[export]
Instance TrivialPVA_eqdec : EqDecision TrivialPVA.
Proof.
    ltac1:(solve_decision).
Defined.

Section sec.

    Context
        {symbol : Set}
        {symbols : Symbols symbol}
    .


    #[local]
    Instance β
        : Builtin MyUnit := {|
        builtin_value
            := TrivialPVA ;
        builtin_function_symbol
            := Emptyset ;
        builtin_predicate_symbol
            := Emptyset ;
        builtin_function_interp
            := fun p => match p with end ;
        builtin_predicate_interp
            := fun p => match p with end ;
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