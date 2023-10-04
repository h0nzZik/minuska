From Minuska Require Import
    prelude
    spec_syntax
.

Inductive Emptyset : Set := .

#[export]
Instance emptyset_eqdec : EqDecision Emptyset.
Proof.
    intros x y.
    destruct x, y.
Defined.

Definition EmptyBuiltin
    (symbol : Set) {symbols : Symbols symbol} : Builtin := {|
    builtin_value
        := Emptyset ;
    builtin_unary_predicate
        := Emptyset ;
    builtin_binary_predicate
        := Emptyset ;
    builtin_unary_function
        := Emptyset ;
    builtin_binary_function
        := Emptyset ;
    builtin_unary_predicate_interp
        := fun p v => match p with end ;
    builtin_binary_predicate_interp
        := fun p v1 v2 => match p with end ;
    builtin_unary_function_interp
        := fun p v => match p with end ;
    builtin_binary_function_interp
        := fun p v1 v2 => match p with end ;
|}.
