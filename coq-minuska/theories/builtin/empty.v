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


Section sec.

    Context
        {symbol : Set}
        {symbols : Symbols symbol}
    .

    Variant PredicateSymbol :=
    | ps_true
    .

    #[export]
    Instance PredicateSymbol_eqdec : EqDecision PredicateSymbol.
    Proof.
        ltac1:(solve_decision).
    Defined.


    #[local]
    Instance β
        : Builtin MyUnit := {|
        builtin_value
            := Emptyset ;
        builtin_function_symbol
            := Emptyset ;
        builtin_predicate_symbol
            := PredicateSymbol ;
        builtin_function_interp
            := fun p => match p with end ;
        builtin_predicate_interp
            := fun p => match p with | ps_true => fun _ _ => true end ;
        
        builtin_predicate_true := ps_true ;
        builtin_predicate_true_holds := fun _ => eq_refl ;
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
    option ((*bool+*)(Z+(string+unit)))%type
    :=
    None
.