From Minuska Require Import
    prelude
    spec
    model_algebra
    builtin.list_signature
    builtin.bool_model
    builtin.int_model
    builtin.list_model
.


Example example_list_int_model_1
    (TermSymbol : Type)
    (NondetValue : Type)
    :
    ValueAlgebra (bool+(simple_list_carrier Z)) NondetValue TermSymbol ListFunSymbol ListPredSymbol
:=
    small_model_of_relaxed (
        list_wrapper _ _ _ _ _ _ (int_relaxed_va TermSymbol NondetValue)
    )
.

(* About example_list_int_model_1. *)
