From stdpp Require Import base countable decidable list list_numbers gmap.
From Equations Require Import Equations.
Set Equations Transparent.
Require Import Wellfounded.
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

(*Derive NoConfusion Subterm EqDec for Element.*)

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

(*Derive NoConfusion Subterm EqDec for Pattern.*)

Fixpoint pattern_size {Σ : Signature} (φ : Pattern) :=
match φ with
| pat_builtin _ => 1
| pat_app s args => 1 + sum_list_with pattern_size args
| pat_var _ => 1
| pat_requires p' _ => 1 + pattern_size p'
end.

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


Definition Valuation {Σ : Signature}
    := gmap variable builtin_value
.

Definition val_satisfies_ap
    {Σ : Signature} (ρ : Valuation) (ap : AtomicProposition)
    : Prop :=
match ap with
| ap1 p x =>
    match ρ !! x with
    | None => False
    | Some vx => builtin_unary_predicate_interp p vx
    end
| ap2 p x y =>
    match ρ !! x, ρ !! y with
    | Some vx, Some vy => builtin_binary_predicate_interp p vx vy
    | _,_ => False
    end
end
.

Fixpoint val_satisfies_c
    {Σ : Signature} (ρ : Valuation) (c : Constraint)
    : Prop :=
match c with
| c_True => True
| c_atomic ap => val_satisfies_ap ρ ap
| c_and c1 c2 => val_satisfies_c ρ c1 /\ val_satisfies_c ρ c2
| c_not c' => ~ val_satisfies_c ρ c'
end.

Section with_signature.
    Context
        {Σ : Signature}
        (ρ : Valuation)
    .

    Equations element_satisfies_pattern'
         (φ : Pattern) (e : Element) : Prop
        by (*wf (@Pattern_subterm Σ)*) struct φ (*wf (pattern_size φ)*) :=
    element_satisfies_pattern' (pat_builtin b2) (el_builtin b1)
        := b1 = b2 ;
    element_satisfies_pattern' (pat_var x) (el_builtin b)
        := ρ !! x = Some b ;
    element_satisfies_pattern' (pat_app s2 φs) (el_app s1 es)
        := s1 = s2
        /\ length es = length φs
        /\ elements_satisfies_patterns' φs es ;
    element_satisfies_pattern' (pat_requires φ' c) e 
        := element_satisfies_pattern' φ' e 
        /\ val_satisfies_c ρ c ;
    element_satisfies_pattern' _ _ := False ;
    where
    elements_satisfies_patterns'
        (φs : list Pattern) (es : list Element) : Prop
        by struct φs (*wf (sum_list_with pattern_size φs)*) :=
    elements_satisfies_patterns' [] []
        := True ;
    elements_satisfies_patterns' (φ::φs') (e::es')
        := element_satisfies_pattern' φ e
        /\ elements_satisfies_patterns' φs' es' ;
    elements_satisfies_patterns' (e'::es') [] := False ;
    elements_satisfies_patterns' [] (e'::es') := False
    .

End with_signature.

Definition element_satisfies_pattern_in_valuation
    {Σ : Signature} (e : Element) (φ : Pattern) (ρ : Valuation)
    : Prop :=
    element_satisfies_pattern' ρ φ e
.

