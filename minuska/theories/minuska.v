From stdpp Require Import base countable decidable list list_numbers gmap.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
Set Equations Transparent.

Require Import Wellfounded.
From Ltac2 Require Import Ltac2.

(* Convert Equations eq decision to stdpp's eq decision*)
#[export]
Instance EquationsEqdec
    (T : Type)
    {dec : Equations.Prop.Classes.EqDec T}:
    EqDecision T
.
Proof.
    intros x y.
    apply eq_dec.
Defined.


Class Variables (variable : Set) := {
    variable_eqdec :: EqDecision variable ;
    variable_countable :: Countable variable ;
    variable_infinite :: Infinite variable ;
}.

Class Symbols (symbol : Set) := {
    symbol_eqdec :: EqDecision symbol ;
    symbol_countable :: Countable symbol ;
}.

(* Model elements *)
Inductive Element' (symbol : Set) (builtin : Set) :=
| el_builtin (b : builtin)
| el_sym (s : symbol)
| el_app (e1 e2 : Element' symbol builtin)
.

Equations Derive NoConfusion for Element'.

#[export]
Instance Element'_eqdec
    {A : Set}
    {symbols : Symbols A}
    (T : Set)
    {T_dec : EqDecision T}
    : EqDecision (Element' A T)
.
Proof.
    ltac1:(solve_decision).
Defined.

Arguments el_app {symbol builtin}%type_scope e1 e2.
Arguments el_builtin {symbol builtin}%type_scope b.
Arguments el_sym {symbol}%type_scope {builtin}%type_scope s.

Equations element'_to_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {T_eqdec : EqDecision builtin}
    {T_countable : Countable builtin}
    (e : Element' symbol builtin)
    : gen_tree (builtin+symbol)%type
:=
    element'_to_gen_tree _ _ (el_builtin b)
    := GenLeaf (inl _ b) ;
    
    element'_to_gen_tree _ _ (el_sym s)
    := GenLeaf (inr _ s) ;
    
    element'_to_gen_tree _ _ (el_app e1 e2)
    := GenNode 0 [(element'_to_gen_tree symbol builtin e1);(element'_to_gen_tree symbol builtin e2)]
.

Equations element'_from_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {builtin_eqdec : EqDecision builtin}
    {builtin_countable : Countable builtin}
    (t : gen_tree (builtin+symbol)%type)
    :  option (Element' symbol builtin)
:=
    element'_from_gen_tree _ _ (GenLeaf (inl _ b))
    := Some (el_builtin b);
    
    element'_from_gen_tree _ _ (GenLeaf (inr _ s))
    := Some (el_sym s);
    
    element'_from_gen_tree _ _ (GenNode 0 [x;y])
    with ((element'_from_gen_tree symbol builtin x), (element'_from_gen_tree symbol builtin y)) => {
        | (Some e1, Some e2) := Some (el_app e1 e2) ;
        | (_, _) := None
    };
    element'_from_gen_tree _ _ _
    := None
.

Lemma element'_to_from_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {builtin_eqdec : EqDecision builtin}
    {builtin_countable : Countable builtin}
    (e : Element' symbol builtin)
    : element'_from_gen_tree symbol builtin (element'_to_gen_tree symbol builtin e) = Some e
.
Proof.
    ltac1:(funelim (element'_to_gen_tree symbol builtin e)).
    { reflexivity. }
    { reflexivity. }
    { cbn. ltac1:(simp element'_from_gen_tree). rewrite H. rewrite H0. reflexivity. }
Qed.

#[export]
Instance element'_countable
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {builtin_eqdec : EqDecision builtin}
    {builtin_countable : Countable builtin}
    : Countable (Element' symbol builtin)
.
Proof.
    apply inj_countable
    with
        (f := (element'_to_gen_tree symbol builtin ))
        (g := element'_from_gen_tree symbol builtin)
    .
    intros x.
    apply element'_to_from_gen_tree.
Qed.


Class Builtin {symbol : Set} {symbols : Symbols symbol} := {
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
        : builtin_unary_predicate 
        -> (Element' symbol builtin_value)
        -> Prop ;
    builtin_binary_predicate_interp
        : builtin_binary_predicate 
        -> (Element' symbol builtin_value)
        -> (Element' symbol builtin_value)
        -> Prop ;
}.

Class Signature := {
    symbol : Set ;
    variable : Set ;
    symbols :: Symbols symbol ;
    builtin :: Builtin ;
    variables :: Variables variable ;
}.

Definition Element {Σ : Signature}
    := Element' symbol builtin_value
.

#[export]
Instance Element_eqdec {Σ : Signature}
    : EqDecision Element
.
Proof.
    intros e1 e2.
    apply Element'_eqdec.
    apply builtin_value_eqdec.
Defined.

Inductive AtomicProposition {Σ : Signature} :=
| ap1 (p : builtin_unary_predicate) (x : variable)
| ap2 (p : builtin_binary_predicate) (x y : variable)
.

Equations Derive NoConfusion for AtomicProposition.

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

Equations Derive NoConfusion for Constraint.

#[export]
Instance constraint_eqdec {Σ : Signature}
    : EqDecision Constraint
.
Proof.
    ltac1:(solve_decision).
Defined.

Inductive Pattern {Σ : Signature} :=
| pat_builtin (b : builtin_value)
| pat_sym (s : symbol)
| pat_app (e1 e2 : Pattern)
| pat_var (x : variable)
| pat_requires (p : Pattern) (c : Constraint)
| pat_requires_match (p : Pattern) (v : variable) (p2 : Pattern)
.

Equations Derive NoConfusion for Pattern.

#[export]
Instance Pattern_eqdec {Σ : Signature}
    : EqDecision Pattern
.
Proof.
    ltac1:(solve_decision).
Defined.

Fixpoint pattern_size {Σ : Signature} (φ : Pattern) :=
match φ with
| pat_builtin _ => 1
| pat_sym _ => 1
| pat_app e1 e2 => 1 + pattern_size e1 + pattern_size e2
| pat_var _ => 1
| pat_requires p' _ => 1 + pattern_size p'
| pat_requires_match p v p2 => 1 + pattern_size p + pattern_size p2
end.

Definition Valuation {Σ : Signature}
    := gmap variable Element
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
    element_satisfies_pattern' (pat_sym s1) (el_sym s2)
        := s1 = s2 ;
    element_satisfies_pattern' (pat_var x) e
        := ρ !! x = Some e ;
    element_satisfies_pattern' (pat_app p1 p2) (el_app e1 e2)
        := element_satisfies_pattern' p1 e1
        /\ element_satisfies_pattern' p2 e2 ;
    element_satisfies_pattern' (pat_requires φ' c) e 
        := element_satisfies_pattern' φ' e 
        /\ val_satisfies_c ρ c ;
    element_satisfies_pattern' (pat_requires_match φ x φ') e with (ρ !! x) => {
        | None := False;
        | Some e2 := element_satisfies_pattern' φ e 
            /\ element_satisfies_pattern' φ' e2;
    };
    element_satisfies_pattern' _ _ := False
    .
End with_signature.

Definition element_satisfies_pattern_in_valuation
    {Σ : Signature} (e : Element) (φ : Pattern) (ρ : Valuation)
    : Prop :=
    element_satisfies_pattern' ρ φ e
.

Record LocalRewrite {Σ : Signature} := {
    lr_from : Pattern ;
    lr_to : Pattern ;
}.

Equations Derive NoConfusion for LocalRewrite.

#[export]
Instance localRewrite_eqdec {Σ : Signature}
    : EqDecision LocalRewrite
.
Proof.
    ltac1:(solve_decision).
Defined.

Inductive LR : Set := LR_Left | LR_Right.

Definition lr_satisfies
    {Σ : Signature} (left_right : LR) (e : Element) (lr : LocalRewrite) (ρ : Valuation)
    : Prop :=
match left_right with
| LR_Left =>
    element_satisfies_pattern_in_valuation e (lr_from lr) ρ
| LR_Right =>
    element_satisfies_pattern_in_valuation e (lr_to lr) ρ
end
.

Inductive RewritingRule {Σ : Signature} :=
| rr_local_rewrite (lr : LocalRewrite)
| rr_builtin (b : builtin_value)
| rr_app (r1 r2 : RewritingRule)
| rr_var (v : variable)
| rr_requires (r : RewritingRule) (c : Constraint)
| rr_requires_match (r : RewritingRule) (v : variable) (p2 : Pattern) 
.

Equations Derive NoConfusion for RewritingRule.

#[export]
Instance RewritingRule_eqdec {Σ : Signature}
    : EqDecision RewritingRule
.
Proof.
    ltac1:(solve_decision).
Defined.

Section sec.
    Context
        {Σ : Signature}
        (left_right : LR)
        (ρ : Valuation)
    .

    Equations rr_satisfies
        (r : RewritingRule) (e : Element)
        : Prop
        by struct r
    :=
        rr_satisfies (rr_local_rewrite lr) e
        := lr_satisfies left_right e lr ρ ;

        rr_satisfies (rr_builtin b1) (el_builtin b2)
        := b1 = b2 ;

        rr_satisfies (rr_var x) e
        := ρ !! x = Some e ;

        rr_satisfies (rr_app r1 r2) (el_app e1 e2)
        := rr_satisfies r1 e1 /\ rr_satisfies r2 e2 ;

        rr_satisfies (rr_requires r c) e 
        := rr_satisfies r e 
        /\ val_satisfies_c ρ c ;

        rr_satisfies (rr_requires_match r x φ') e with (ρ !! x) => {
        | None := False;
        | Some e2 := rr_satisfies r e 
            /\ element_satisfies_pattern' ρ φ' e2;
        } ;

        rr_satisfies _ _ := False ;
    .
End sec.

Definition rewrites_in_valuation_to
    {Σ : Signature} (ρ : Valuation) (r : RewritingRule) (from to : Element)
    : Prop
:= rr_satisfies LR_Left ρ r from
/\ rr_satisfies LR_Right ρ r to
.

Definition rewrites_to
    {Σ : Signature} (r : RewritingRule) (from to : Element)
    : Prop
:= exists ρ, rewrites_in_valuation_to ρ r from to
.

Definition RewritingTheory {Σ : Signature}
    := list RewritingRule
.

Definition rewriting_relation
    {Σ : Signature}
    (Γ : RewritingTheory)
    : relation Element
    := fun from to =>
        exists r, r ∈ Γ /\ rewrites_to r from to
.

Definition not_stuck
    {Σ : Signature}
    (Γ : RewritingTheory)
    (e : Element) : Prop
:= exists e', rewriting_relation Γ e e'.

Definition stuck
    {Σ : Signature}
    (Γ : RewritingTheory)
    (e : Element) : Prop
:= not (not_stuck Γ e).


Definition Interpreter
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Type
    := Element -> option Element
.

Definition Interpreter_sound
    {Σ : Signature}
    (Γ : RewritingTheory)
    (interpreter : Interpreter Γ)
    : Prop
    := forall e,
        stuck Γ e -> interpreter e = None
    /\ forall e,
        not_stuck Γ e ->
        exists e', interpreter e = Some e'
.

Definition Explorer
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Type
    := Element -> list Element
.

Definition Explorer_sound
    {Σ : Signature}
    (Γ : RewritingTheory)
    (explorer : Explorer Γ)
    : Prop
    := forall (e e' : Element),
        e' ∈ explorer e <-> rewriting_relation Γ e e'
.

