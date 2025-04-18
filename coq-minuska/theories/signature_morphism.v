From Minuska Require Import
    prelude
    spec
.

#[local]
Arguments builtin_function_symbol (Signature) : clear implicits.
#[local]
Arguments builtin_predicate_symbol (Signature) : clear implicits.
#[local]
Arguments builtin_function_interp {symbol} {symbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.
#[local]
Arguments builtin_predicate_interp {symbol} {symbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.

Record SignatureMorphism (s1 s2 : Signature) := {
    function_symbol_morphism : (builtin_function_symbol s1) -> (builtin_function_symbol s2) ;
    predicate_symbol_morphism : (builtin_predicate_symbol s1) -> (builtin_predicate_symbol s2) ;
    sm_pred_ar : forall p, bps_ar (predicate_symbol_morphism p) = bps_ar p ;
    sm_pred_neg : forall p,
      bps_neg (predicate_symbol_morphism p) = predicate_symbol_morphism <$> (bps_neg p) ;
}.

Arguments function_symbol_morphism {s1 s2} s _.
Arguments predicate_symbol_morphism {s1 s2} s _.

Class SMInj {s1 s2 : Signature} (μ : SignatureMorphism s1 s2) := {
    smif :: Inj (=) (=) (function_symbol_morphism μ) ;
    smip :: Inj (=) (=) (predicate_symbol_morphism μ) ;
}.
