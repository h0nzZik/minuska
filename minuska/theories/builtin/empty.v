From Minuska Require Import
    prelude
    spec
    pval_ocaml_binding
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

    #[local]
    Instance β
        : Builtin MyUnit := {|
        builtin_value
            := Emptyset ;
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

Definition inject_bool
    {symbol : Type}
    (b : bool)
    :
    option Emptyset :=
    None
.

Definition inject_Z
    {symbol : Type}
    (z : Z)
    :
    option Emptyset :=
    None
.

Definition inject_string
    {symbol : Type}
    (s : string)
    :
    option Emptyset :=
    None
.

Definition eject
    {symbol : Type}
    (v : Emptyset)
    :
    option (bool+(Z+(string+unit)))%type
    :=
    None
.