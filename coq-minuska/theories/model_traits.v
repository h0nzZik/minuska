From Minuska Require Import
    prelude
    spec
    model_functor
.

Inductive ErrT :=
| et_error
.

#[export]
Instance ErrT_eqdec : EqDecision ErrT.
Proof.
    unfold RelDecision.
    intros [] []. left. reflexivity.
Defined.

#[export]
Program Instance ErrT_fin : Finite ErrT := {|
    enum := [et_error] ;
|}.
Next Obligation.
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.

(* 
Class WithErrTrait
    {symbol : Type}
    {symbols : Symbols symbol}
    {my_signature : Signature}
    {NondetValue : Type}
    (M : Model my_signature NondetValue)
:= {
    inject_error :: CarrierInjection ErrT M ;
}.

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
