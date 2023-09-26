From stdpp Require Import base countable decidable gmap list list_numbers numbers.
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

Inductive AppliedSymbol (symbol : Set) (builtin : Set) :=
| aps_sym (s : symbol)
| aps_app_builtin (aps : AppliedSymbol symbol builtin) (b : builtin) 
| aps_app_aps (aps : AppliedSymbol symbol builtin) (x : AppliedSymbol symbol builtin)
.

Equations Derive NoConfusion for AppliedSymbol.

Arguments aps_sym {symbol builtin}%type_scope s.
Arguments aps_app_builtin {symbol builtin}%type_scope aps b.
Arguments aps_app_aps {symbol builtin}%type_scope aps x.

#[export]
Instance appliedSymbol_eqdec
    {symbol : Set}
    {symbols : Symbols symbol}
    (builtin : Set)
    {builtin_dec : EqDecision builtin}
    : EqDecision (AppliedSymbol symbol builtin)
.
Proof.
    ltac1:(solve_decision).
Defined.

Equations appliedSymbol_to_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {T_eqdec : EqDecision builtin}
    {T_countable : Countable builtin}
    (a : AppliedSymbol symbol builtin)
    : gen_tree symbol
:=
    appliedSymbol_to_gen_tree _ _ (aps_sym s)
    := GenLeaf s ;

    appliedSymbol_to_gen_tree _ _ (aps_app_builtin aps b)
    := (
        let x := (encode (0, encode b)) in
        GenNode (Pos.to_nat x) ([appliedSymbol_to_gen_tree symbol builtin aps;appliedSymbol_to_gen_tree symbol builtin aps(* we duplicate it to make the reverse simpler*)])
    ) ;

    appliedSymbol_to_gen_tree _ _ (aps_app_aps aps1 aps2)
    := (
        let xd := (1, encode 0) in
        let x := (encode xd) in
        GenNode (Pos.to_nat x) ([appliedSymbol_to_gen_tree _ _ aps1; appliedSymbol_to_gen_tree _ _ aps2])
    )
.

Equations appliedSymbol_of_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {T_eqdec : EqDecision builtin}
    {T_countable : Countable builtin}
    (t : gen_tree symbol)
    : option (AppliedSymbol symbol builtin)
:=
    appliedSymbol_of_gen_tree _ _ (GenLeaf s)
    := Some (aps_sym s);
      
    appliedSymbol_of_gen_tree _ _ (GenNode n [gt1;gt2])
    with (@decode (nat*positive) _ _ (Pos.of_nat n)) => {
        | Some (0, pb) with (@decode builtin _ _ pb) => {
            | Some b with (appliedSymbol_of_gen_tree symbol builtin gt1) => {
                | Some as1 := Some (aps_app_builtin as1 b)
                | _ := None
            }
            | _ := None
        }
        | Some (1, _) with appliedSymbol_of_gen_tree symbol builtin gt1, appliedSymbol_of_gen_tree symbol builtin gt2 => {
            | Some aps1, Some aps2 := Some (aps_app_aps aps1 aps2)
            | _, _ := None
        }
        | _ := None
    };
    appliedSymbol_of_gen_tree _ _ _
    := None
.
(* Opaque appliedSymbol_of_gen_tree. *)

Lemma appliedSymbol_of_to_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {T_eqdec : EqDecision builtin}
    {T_countable : Countable builtin}
    (a : AppliedSymbol symbol builtin)
    : appliedSymbol_of_gen_tree symbol builtin (appliedSymbol_to_gen_tree symbol builtin a) = Some a
.
Proof.
    ltac1:(funelim (appliedSymbol_to_gen_tree symbol builtin a)).
    {
        ltac1:(rewrite <- Heqcall).
        ltac1:(simp appliedSymbol_of_gen_tree).
        reflexivity.
    }
    {
        ltac1:(rewrite <- Heqcall).
        clear Heqcall.
        ltac1:(simp appliedSymbol_of_gen_tree).
        ltac1:(rewrite ! Pos2Nat.id, decode_encode).
        unfold appliedSymbol_of_gen_tree_clause_2.
        unfold appliedSymbol_of_gen_tree_clause_2_clause_1.
        rewrite decode_encode.
        ltac1:(rewrite H).
        unfold appliedSymbol_of_gen_tree_clause_2_clause_1_clause_1.
        reflexivity.
    }
    {
        ltac1:(rewrite <- Heqcall).
        clear Heqcall.
        ltac1:(simp appliedSymbol_of_gen_tree).
        ltac1:(rewrite ! Pos2Nat.id, decode_encode).
        unfold appliedSymbol_of_gen_tree_clause_2.
        unfold appliedSymbol_of_gen_tree_clause_2_clause_2.
        unfold appliedSymbol_of_gen_tree_clause_2_clause_2_clause_1.
        ltac1:(rewrite H).
        ltac1:(rewrite H0).
        reflexivity.
    }
Qed.

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


(* Model elements *)
Inductive Element' (symbol : Set) (builtin : Set) :=
| el_builtin (b : builtin)
| el_appsym (s : AppliedSymbol symbol builtin)
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


Arguments el_appsym {symbol builtin}%type_scope s.
Arguments el_builtin {symbol builtin}%type_scope b.

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

    builtin_unary_function
        : Set ;
    builtin_unary_function_eqdec
        :: EqDecision builtin_unary_function ;

    builtin_binary_function
        : Set ;
    builtin_binary_function_eqdec
        :: EqDecision builtin_binary_function ;

    builtin_unary_predicate_interp
        : builtin_unary_predicate 
        -> (Element' symbol builtin_value)
        -> Prop ;

    builtin_binary_predicate_interp
        : builtin_binary_predicate 
        -> (Element' symbol builtin_value)
        -> (Element' symbol builtin_value)
        -> Prop ;
    
    builtin_unary_function_interp
        : builtin_unary_function
        -> (Element' symbol builtin_value)
        -> builtin_value ;

    builtin_binary_function_interp
        : builtin_binary_function
        -> (Element' symbol builtin_value)
        -> (Element' symbol builtin_value)
        -> builtin_value ;
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


Inductive FunTerm'
    (symbol : Set) (builtin : Set) (unary_function : Set) (binary_function : Set) :=
| ft_builtin (b : builtin)
| ft_unary (f : unary_function) (e : Element' symbol builtin)
| ft_binary (f : binary_function) (e1 : Element' symbol builtin) (e2 : Element' symbol builtin)
.

Equations Derive NoConfusion for FunTerm'.


(* TODO rename to RhsTerm *)
Inductive SimplePattern {Σ : Signature} :=
| spat_builtin (b : builtin_value)
| spat_sym (s : symbol)
| spat_app (e1 e2 : SimplePattern)
| spat_var (x : variable)
.

Equations Derive NoConfusion for SimplePattern.

#[export]
Instance SimplePattern_eqdec {Σ : Signature}
    : EqDecision SimplePattern
.
Proof.
    ltac1:(solve_decision).
Defined.

Fixpoint simplePattern_size {Σ : Signature} (φ : SimplePattern) :=
match φ with
| spat_builtin _ => 1
| spat_sym _ => 1
| spat_app e1 e2 => 1 + simplePattern_size e1 + simplePattern_size e2
| spat_var _ => 1
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

    Equations element_satisfies_simple_pattern'
         (φ : SimplePattern) (e : Element) : Prop
        by (*wf (@Pattern_subterm Σ)*) struct φ (*wf (pattern_size φ)*) :=
    element_satisfies_simple_pattern' (spat_builtin b2) (el_builtin b1)
        := b1 = b2 ;
    
    element_satisfies_simple_pattern' (spat_sym s1) (el_sym s2)
        := s1 = s2 ;
    
    element_satisfies_simple_pattern' (spat_var x) e
        := ρ !! x = Some e ;
    
    element_satisfies_simple_pattern' (spat_app p1 p2) (el_app e1 e2)
        := element_satisfies_simple_pattern' p1 e1
        /\ element_satisfies_simple_pattern' p2 e2 ;
    
    element_satisfies_simple_pattern' _ _ := False
    .

End with_signature.

Definition element_satisfies_pattern_in_valuation
    {Σ : Signature} (e : Element) (φ : Pattern) (ρ : Valuation)
    : Prop :=
    element_satisfies_pattern' ρ φ e
.

Definition element_satisfies_simple_pattern_in_valuation
    {Σ : Signature} (e : Element) (φ : SimplePattern) (ρ : Valuation)
    : Prop :=
    element_satisfies_simple_pattern' ρ φ e
.


Record LocalRewrite {Σ : Signature} := {
    lr_from : Pattern ;
    lr_to : SimplePattern ;
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
    element_satisfies_simple_pattern_in_valuation e (lr_to lr) ρ
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

Definition rule_weakly_well_defined
    {Σ : Signature}
    (r : RewritingRule)
    : Prop
    := forall from ρ, rr_satisfies LR_Left ρ r from ->
        exists to, rr_satisfies LR_Right ρ r to
.

Definition rewrites_to
    {Σ : Signature} (r : RewritingRule) (from to : Element)
    : Prop
:= exists ρ, rewrites_in_valuation_to ρ r from to
.

Definition RewritingTheory {Σ : Signature}
    := list RewritingRule
.

Definition thy_weakly_well_defined
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Prop
    := forall r, r ∈ Γ -> rule_weakly_well_defined r.


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
    := (forall e,
        stuck Γ e -> interpreter e = None)
    /\ (thy_weakly_well_defined Γ ->
        forall e,
        not_stuck Γ e ->
        exists e', interpreter e = Some e')
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




