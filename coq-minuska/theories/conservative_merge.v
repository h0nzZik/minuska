From Minuska Require Import
    prelude
    spec
    model_algebra
.
(* 
Print StaticModel.
Check sum_eq_dec.
Check modelover_nv_lift.

Definition sm_merge (Σ1 Σ2 : StaticModel) : StaticModel :=
{|
    symbol := (@spec.symbol Σ1)+(@spec.symbol Σ2) ;
    symbols := {|
        symbol_eqdec := @sum_eq_dec _ (@spec.symbol_eqdec _ (@spec.symbols Σ1)) _ (@spec.symbol_eqdec _ (@spec.symbols Σ2)) ;
        symbol_countable := @sum_countable _ _ (@spec.symbol_countable _ (@spec.symbols Σ1)) _ _ (@spec.symbol_countable _ (@spec.symbols Σ2))
    |};
    NondetValue := (@spec.NondetValue Σ1)*(@spec.NondetValue Σ2) ;
    signature := signature_sum (@spec.signature Σ1) (@spec.signature Σ2) ;
    builtin := {|
        builtin_value := (@spec.builtin_value _ _ _ _ (@spec.builtin Σ1))+(@spec.builtin_value _ _ _ _ (@spec.builtin Σ2)) ;
        builtin_model_over :=
            modelover_sum
                (@spec.signature Σ1)
                (@spec.signature Σ2)
                ((@spec.NondetValue Σ1)*(@spec.NondetValue Σ2))
                ((@spec.builtin_value _ _ _ _ (@spec.builtin Σ1))+(@spec.builtin_value _ _ _ _ (@spec.builtin Σ2)))
                (modelover_nv_lift fst (@spec.builtin_model_over (@spec.symbol Σ1) (@spec.symbols Σ1) (@spec.signature Σ1) (@spec.NondetValue Σ1) _))
                (modelover_nv_lift snd (@spec.builtin_model_over (@spec.symbol Σ2) (@spec.symbols Σ2) (@spec.signature Σ2) (@spec.NondetValue Σ2) _));
    |};
|}. *)
