From stdpp Require Import base.
From Ltac2 Require Import Ltac2.

Class Builtins := {
    builtin_value
        : Set ;
    builtin_unary_predicate_name
        : Set ;
    builtin_binary_predicate_name
        : Set ;
    builtin_unary_predicate_interp
        : builtin_unary_predicate_name -> builtin_value -> Prop ;

    builtin_binary_predicate_interp
        : builtin_binary_predicate_name -> builtin_value -> builtin_value -> Prop ;
}.
