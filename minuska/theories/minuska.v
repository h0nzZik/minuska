From stdpp Require Import base countable decidable list list_numbers.
From Equations Require Import Equations.
From Ltac2 Require Import Ltac2.

Class Builtin := {
    builtin_value
        : Set ;
    builtin_value_eqdec
        :: EqDecision builtin_value ;
    builtin_unary_predicate
        : Set ;
    builtin_unary_predicate_eqdec
        :: EqDecision builtin_unary_predicate ;
    builtin_binary_predicate
        : Set ;
    builtin_binary_predicate_eqdec
        :: EqDecision builtin_binary_predicate ;
    builtin_unary_predicate_interp
        : builtin_unary_predicate -> builtin_value -> Prop ;
    builtin_binary_predicate_interp
        : builtin_binary_predicate -> builtin_value -> builtin_value -> Prop ;
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

Inductive AtomicProposition {Σ : Signature} :=
| ap1 (p : builtin_unary_predicate) (x : variable)
| ap2 (p : builtin_binary_predicate) (x y : variable)
.

#[export]
Instance atomicProposition_eqdec {Σ : Signature}
    : EqDecision AtomicProposition
.
Proof.
    ltac1:(solve_decision).
Defined.

Inductive Constraint {Σ : Signature} :=
| c_True
| c_atomic (ap : AtomicProposition)
| c_and (c1 c2 : Constraint)
| c_not (c : Constraint)
.

#[export]
Instance constraint_eqdec {Σ : Signature}
    : EqDecision Constraint
.
Proof.
    ltac1:(solve_decision).
Defined.

Inductive Pattern {Σ : Signature} :=
| pat_builtin (b : builtin_value)
| pat_app (s : symbol) (args : list Pattern)
| pat_var (v : variable)
| pat_requires (p : Pattern) (c : Constraint)
.

Equations? pattern_eqdec' {Σ : Signature} (p1 p2 : Pattern)
    : {p1 = p2} + {p1 <> p2}
    by struct p1
:=
    pattern_eqdec' (pat_builtin b1) (pat_builtin b2)
    := if (decide (b1 = b2)) then left _ else right _  ;
    pattern_eqdec' (pat_app s1 args1) (pat_app s2 args2)
    := if (decide (s1 = s2)) then
        (if (@decide (args1 = args2) _) then left _ else right _)
        else right _ ;
    pattern_eqdec' (pat_var v1) (pat_var v2)
    := if (decide (v1 = v2)) then left _ else right _  ;
    pattern_eqdec' (pat_requires p1 c1) (pat_requires p2 c2)
    := if (@decide (p1 = p2) _) then
        (if (decide (c1 = c2)) then left _ else right _)
       else right _  ;
    pattern_eqdec' _ _ := right _
.
Proof.
    {
        unfold Decision.
        apply list_eqdec.
        unfold EqDec. intros x y.
        apply pattern_eqdec'.
    }
    {
        apply pattern_eqdec'.
    }
Defined.



