From Minuska Require Import
    prelude
    spec
.

Definition unit_hidden_signature
    (signature : Signature)
:
    HiddenSignature
:= {|
    AttributeSymbol := void ;
    MethodSymbol := void ;
    HiddenPredicateSymbol := void ;
|}.


Definition unit_hidden_model
    {symbol : Type}
    {symbols : Symbols symbol}
    (signature : Signature)
    (NondetValue : Type)
    (model : Model signature NondetValue)
:
    @HiddenModel symbol symbols signature (unit_hidden_signature signature) NondetValue model
:= {|
    hidden_data := unit ;
    hidden_init := tt;
    attribute_interpretation := fun a h args => None ;
    method_interpretation := fun m h args => None ;
    hidden_predicate_interpretation := fun p h args => None ;
|}.
