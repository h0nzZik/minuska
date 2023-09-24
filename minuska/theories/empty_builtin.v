From stdpp Require Import base countable decidable list list_numbers gmap.

From Minuska Require Import minuska.

From Ltac2 Require Import Ltac2.

Inductive Emptyset : Set := .

#[export]
Instance emptyset_eqdec : EqDecision Emptyset.
Proof.
    intros x y.
    destruct x, y.
Defined.

Definition EmptyBuiltin {symbols : Symbols} : Builtin := {|
    builtin_value
        := Emptyset ;
    builtin_unary_predicate
        := Emptyset ;
    builtin_binary_predicate
        := Emptyset ;
    builtin_unary_predicate_interp
        := fun p v => match p with end ;
    builtin_binary_predicate_interp
        := fun p v1 v2 => match p with end ;
|}.
