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


Section sec.

    Context
        {symbol : Set}
        {symbols : Symbols symbol}
    .

    #[local]
    Program Instance mysignature : Signature := {|
        builtin_function_symbol
            := Emptyset ;
        builtin_predicate_symbol
            := Emptyset ;
        bps_ar := fun _ => 0 ;
        bps_neg := fun _ => None;
    |}.
    Fail Next Obligation.

    Program Definition βover
        : ModelOver mysignature MyUnit Emptyset := {|
        builtin_function_interp
            := fun _ _ _ => None ;
        builtin_predicate_interp
            := fun _ _ _ => None ;
    |}.
    Fail Next Obligation.

    #[local]
    Instance β
        : @Model _ _ mysignature MyUnit := {|
        builtin_value
            := Emptyset ;
        builtin_model_over := βover ;
    |}.

End sec.

Definition builtins_binding : BuiltinsBinding := {|
    bb_function_names := [] ;
|}.

Definition inject_bool
    {symbol : Type}
    (Fret : option Emptyset -> Emptyset)
    (b : bool)
    :
    Emptyset :=
    Fret None
.

Definition inject_Z
    {symbol : Type}
    (Fret : option Emptyset -> Emptyset)
    (z : Z)
    :
    Emptyset :=
    Fret None
.

Definition inject_string
    {symbol : Type}
    (Fret : option Emptyset -> Emptyset)
    (s : string)
    :
    Emptyset :=
    Fret None
.

Definition eject
    {symbol : Type}
    (v : Emptyset)
    :
    option (bool+(Z+(string)))%type
    :=
    None
.