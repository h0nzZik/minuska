From Minuska Require Import
    prelude
    spec
.
(* 
#[local]
Arguments FunSymbol (Signature) : clear implicits.
#[local]
Arguments PredSymbol (Signature) : clear implicits.
#[local]
Arguments builtin_function_interp {TermSymbol} {TermSymbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.
#[local]
Arguments builtin_predicate_interp {TermSymbol} {TermSymbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.

Record SignatureMorphism (s1 s2 : Signature) := {
    function_TermSymbol_morphism : (FunSymbol s1) -> (FunSymbol s2) ;
    predicate_TermSymbol_morphism : (PredSymbol s1) -> (PredSymbol s2) ;
}.

Arguments function_TermSymbol_morphism {s1 s2} s _.
Arguments predicate_TermSymbol_morphism {s1 s2} s _.

Class SMInj {s1 s2 : Signature} (μ : SignatureMorphism s1 s2) := {
    smif :: Inj (=) (=) (function_TermSymbol_morphism μ) ;
    smip :: Inj (=) (=) (predicate_TermSymbol_morphism μ) ;
}. *)

(* TODO add hidden signature morphism *)
