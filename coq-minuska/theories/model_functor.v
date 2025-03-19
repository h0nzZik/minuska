From Minuska Require Import
    prelude
    spec
    model_algebra
.
(* 
#[global]
Arguments inject (FromT ToT) {Injection} _.

Class CarrierInjection
    {symbol : Type}
    {symbols : Symbols symbol}
    {my_signature : Signature}
    {NondetValue : Type}
    (FromT : Type)
    (M : Model my_signature NondetValue)
:= {
    carrier_inject : Injection FromT (@builtin_value _ _ _ _ M) ;
}.
     *)
(* 
Class CarrierInjection
    {symbol : Type}
    {symbols : Symbols symbol}
    {my_signature : Signature}
    {NondetValue : Type}
    (FromT : Type)
    (M : Model my_signature NondetValue)
:= {
    carinj_inject : FromT -> @builtin_value _ _ _ _ M ;
    carinj_inject__injective :: Inj (=) (=) carinj_inject ;
}. *)
(* 
#[global]
Arguments carinj_inject
    {symbol}
    {symbols my_signature}
    {NondetValue}
    {FromT} M {CarrierInjection} _
.
 *)

(* 
Class CarrierFunctorT := {
    cf_carrier
        : Type -> Type
    ;
    cf_carrier_eqdec
        : forall T,
            EqDecision T ->
            EqDecision (cf_carrier T)
    ;

    cf_from:
        forall (T FromT : Type)(f : FromT -> T),
            FromT -> (cf_carrier T)
    ;

    cf_from_inj:
        forall (T FromT : Type)(f : FromT -> T),
            Inj (=) (=) (cf_from T FromT f)
    ;

(* 
    cf_injection :
        forall       
            {my_signature : Signature}
            {NondetValue : Type}
            (FromT Carrier : Type)
            (Mo : ModelOver my_signature NondetValue Carier),
            CarrierInjection FromT M ->
            CarrierInjection , *)

}.

(* Print ModelOver.
Class ModelFunctorT := {
    mf_carrier : CarrierFunctorT ;



    (* [cf_carrier_inject] would be a monadic-like [return] *)
    (* cf_carrier_inject : forall (C : Type), C -> cf_carrier C ; *)
    (* cf_carrier_inject__inj :: forall (C : Type),  Inj (=) (=) (cf_carrier_inject C) ; *)
}. *)


 *)
