From Minuska Require Import
    prelude
    spec
    model_algebra
.
(* 
Print BackgroundModel.
Check sum_eq_dec.
Check modelover_nv_lift.

Definition sm_merge (Σ1 Σ2 : BackgroundModel) : BackgroundModel :=
{|
    TermSymbol := (@spec.TermSymbol Σ1)+(@spec.TermSymbol Σ2) ;
    TermSymbols := {|
        TermSymbol_eqdec := @sum_eq_dec _ (@spec.TermSymbol_eqdec _ (@spec.TermSymbols Σ1)) _ (@spec.TermSymbol_eqdec _ (@spec.TermSymbols Σ2)) ;
        TermSymbol_countable := @sum_countable _ _ (@spec.TermSymbol_countable _ (@spec.TermSymbols Σ1)) _ _ (@spec.TermSymbol_countable _ (@spec.TermSymbols Σ2))
    |};
    NondetValue := (@spec.NondetValue Σ1)*(@spec.NondetValue Σ2) ;
    signature := signature_sum (@spec.signature Σ1) (@spec.signature Σ2) ;
    builtin := {|
        BasicValue := (@spec.BasicValue _ _ _ _ (@spec.builtin Σ1))+(@spec.BasicValue _ _ _ _ (@spec.builtin Σ2)) ;
        builtin_model_over :=
            modelover_sum
                (@spec.signature Σ1)
                (@spec.signature Σ2)
                ((@spec.NondetValue Σ1)*(@spec.NondetValue Σ2))
                ((@spec.BasicValue _ _ _ _ (@spec.builtin Σ1))+(@spec.BasicValue _ _ _ _ (@spec.builtin Σ2)))
                (modelover_nv_lift fst (@spec.builtin_model_over (@spec.TermSymbol Σ1) (@spec.TermSymbols Σ1) (@spec.signature Σ1) (@spec.NondetValue Σ1) _))
                (modelover_nv_lift snd (@spec.builtin_model_over (@spec.TermSymbol Σ2) (@spec.TermSymbols Σ2) (@spec.signature Σ2) (@spec.NondetValue Σ2) _));
    |};
|}. *)
