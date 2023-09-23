From stdpp Require Import base countable decidable list list_numbers.
From Equations Require Import Equations.
From Ltac2 Require Import Ltac2.

Class Builtin := {
    builtin_value
        : Set ;
    builtin_value_eqdec
        :: EqDecision builtin_value ;
    builtin_unary_predicate_name
        : Set ;
    builtin_unary_predicate_name_eqdec
        :: EqDecision builtin_unary_predicate_name ;
    builtin_binary_predicate_name
        : Set ;
    builtin_binary_predicate_name_eqdec
        :: EqDecision builtin_binary_predicate_name ;
    builtin_unary_predicate_interp
        : builtin_unary_predicate_name -> builtin_value -> Prop ;
    builtin_binary_predicate_interp
        : builtin_binary_predicate_name -> builtin_value -> builtin_value -> Prop ;
}.

Class Variables := {
    variable : Set ;
    variable_eqdec :: EqDecision variable ;
    variable_countable :: Countable variable ;
    variable_infinite :: Infinite variable ;
}.

Class Symbols := {
    symbol : Set ;
    symbol_eqdec :: EqDecision symbol ;
}.

Class Signature := {
    builtin :: Builtin ;
    variables :: Variables ;
    symbols :: Symbols ;
}.

(* Model elements over given signature *)
Inductive Element {Σ : Signature} :=
| el_builtin (b : builtin_value)
| el_app (s : symbol) (args : list Element)
.

Fixpoint element_size {Σ : Signature} (e : Element) :=
match e with
| el_builtin b => 1
| el_app s args => 1 + sum_list_with element_size args
end.

Equations? element_eqdec' {Σ : Signature} (e1 e2 : Element)
    : {e1 = e2} + {e1 <> e2}
    by struct e1
:=
    element_eqdec' (el_builtin b1) (el_builtin b2)
    := if (decide (b1 = b2)) then left _ else right _  ;
    element_eqdec' (el_builtin _) (el_app _ _)
    := right _ ;
    element_eqdec' (el_app _ _) (el_builtin _)
    := right _ ;
    element_eqdec' (el_app s1 args1) (el_app s2 args2)
    := if (decide (s1 = s2)) then
        (if (@decide (args1 = args2) _) then left _ else right _)
        else right _ 
.
Proof.
    unfold Decision.
    apply list_eqdec.
    unfold EqDec. intros x y.
    apply element_eqdec'.
Defined.

#[export]
Instance Element_eqdec {Σ : Signature}
    : EqDecision Element
.
Proof.
    intros e1 e2.
    apply element_eqdec'.
Defined.

