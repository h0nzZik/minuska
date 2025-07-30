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
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
    (NondetValue : Type)
    :
    Model list_signature NondetValue
:=
    model_of_relaxed (
        rmf_apply list_relaxed_functor (
            int_relaxed_model TermSymbol TermSymbols NondetValue
        )
    )
.
