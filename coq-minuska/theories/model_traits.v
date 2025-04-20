From Minuska Require Import
    prelude
    spec
    model_functor
.


(* 
Class WithBoolTrait
    {symbol : Type}
    {symbols : Symbols symbol}
    {my_signature : Signature}
    {NondetValue : Type}
    (M : Model my_signature NondetValue)
:= {
    inject_bool :: CarrierInjection bool M ;
}.

Class WithIntTrait
    {symbol : Type}
    {symbols : Symbols symbol}
    {my_signature : Signature}
    {NondetValue : Type}
    (M : Model my_signature NondetValue)
:= {
    inject_int :: CarrierInjection Z M ;
}.

Class WithListTrait (Inner : Type)
    {symbol : Type}
    {symbols : Symbols symbol}
    {my_signature : Signature}
    {NondetValue : Type}
    (M : Model my_signature NondetValue)
:= {
    inject_list_inner :: CarrierInjection Inner M ;
    inject_list :: CarrierInjection (list Inner) M ;
}.
 *)
