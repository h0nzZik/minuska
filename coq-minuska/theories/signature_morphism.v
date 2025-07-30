From Minuska Require Import
    prelude
    spec
.

#[local]
Arguments FunctionSymbol (Signature) : clear implicits.
#[local]
Arguments PredicateSymbol (Signature) : clear implicits.
#[local]
Arguments builtin_function_interp {symbol} {symbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.
#[local]
Arguments builtin_predicate_interp {symbol} {symbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.

Record SignatureMorphism (s1 s2 : Signature) := {
    function_symbol_morphism : (FunctionSymbol s1) -> (FunctionSymbol s2) ;
    predicate_symbol_morphism : (PredicateSymbol s1) -> (PredicateSymbol s2) ;
}.

Arguments function_symbol_morphism {s1 s2} s _.
Arguments predicate_symbol_morphism {s1 s2} s _.

Class SMInj {s1 s2 : Signature} (μ : SignatureMorphism s1 s2) := {
    smif :: Inj (=) (=) (function_symbol_morphism μ) ;
    smip :: Inj (=) (=) (predicate_symbol_morphism μ) ;
}.

(* TODO add hidden signature morphism *)