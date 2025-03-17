From Minuska Require Import
    prelude
    spec
.

Class CarrierFunctorT := {
    cf_carrier
        : Type -> Type
    ;
    cf_carrier_eqdec
        : forall T,
            EqDecision T ->
            EqDecision (cf_carrier T)
    ;
    (* [cf_carrier_inject] would be a monadic-like [return] *)
    (* cf_carrier_inject : forall (C : Type), C -> cf_carrier C ; *)
    (* cf_carrier_inject__inj :: forall (C : Type),  Inj (=) (=) (cf_carrier_inject C) ; *)
}.



