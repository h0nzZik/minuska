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
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    :
    Model list_signature NondetValue
:=
    model_of_relaxed (
        rmf_apply list_relaxed_functor (
            int_relaxed_model symbol symbols NondetValue
        )
    )
.
