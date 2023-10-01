From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.micromega Require Import Lia.

From stdpp Require Import base countable decidable gmap sets list list_numbers numbers.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
Set Equations Transparent.

Require Import Wellfounded.
From Ltac2 Require Import Ltac2.

Add Search Blacklist "_graph_mut".
Add Search Blacklist "_graph_rect".
Add Search Blacklist "_graph_equation".
Add Search Blacklist "FunctionalElimination_".

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

Inductive AppliedOperator' (operator : Set) (operand : Set) :=
| ao_operator (s : operator)
| ao_app_operand
    (aps : AppliedOperator' operator operand) (b : operand) 
| ao_app_ao
    (aps : AppliedOperator' operator operand)
    (x : AppliedOperator' operator operand)
.

Equations Derive NoConfusion for AppliedOperator'.

Arguments ao_operator {operator operand}%type_scope s.
Arguments ao_app_operand {operator operand}%type_scope aps b.
Arguments ao_app_ao {operator operand}%type_scope aps x.

#[export]
Instance AppliedOperator'_eqdec
    {symbol : Set}
    {symbols : Symbols symbol}
    (builtin : Set)
    {builtin_dec : EqDecision builtin}
    : EqDecision (AppliedOperator' symbol builtin)
.
Proof.
    ltac1:(solve_decision).
Defined.

Equations AppliedOperator'_to_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {T_eqdec : EqDecision builtin}
    {T_countable : Countable builtin}
    (a : AppliedOperator' symbol builtin)
    : gen_tree symbol
:=
    AppliedOperator'_to_gen_tree _ _ (ao_operator s)
    := GenLeaf s ;

    AppliedOperator'_to_gen_tree _ _ (ao_app_operand aps b)
    := (
        let x := (encode (0, encode b)) in
        GenNode (Pos.to_nat x) ([AppliedOperator'_to_gen_tree symbol builtin aps;AppliedOperator'_to_gen_tree symbol builtin aps(* we duplicate it to make the reverse simpler*)])
    ) ;

    AppliedOperator'_to_gen_tree _ _ (ao_app_ao aps1 aps2)
    := (
        let xd := (1, encode 0) in
        let x := (encode xd) in
        GenNode (Pos.to_nat x) ([AppliedOperator'_to_gen_tree _ _ aps1; AppliedOperator'_to_gen_tree _ _ aps2])
    )
.
Opaque AppliedOperator'_to_gen_tree.

Equations AppliedOperator'_of_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {T_eqdec : EqDecision builtin}
    {T_countable : Countable builtin}
    (t : gen_tree symbol)
    : option (AppliedOperator' symbol builtin)
:=
    AppliedOperator'_of_gen_tree _ _ (GenLeaf s)
    := Some (ao_operator s);
      
    AppliedOperator'_of_gen_tree _ _ (GenNode n [gt1;gt2])
    with (@decode (nat*positive) _ _ (Pos.of_nat n)) => {
        | Some (0, pb) with (@decode builtin _ _ pb) => {
            | Some b with (AppliedOperator'_of_gen_tree symbol builtin gt1) => {
                | Some as1 := Some (ao_app_operand as1 b)
                | _ := None
            }
            | _ := None
        }
        | Some (1, _) with AppliedOperator'_of_gen_tree symbol builtin gt1, AppliedOperator'_of_gen_tree symbol builtin gt2 => {
            | Some aps1, Some aps2 := Some (ao_app_ao aps1 aps2)
            | _, _ := None
        }
        | _ := None
    };
    AppliedOperator'_of_gen_tree _ _ _
    := None
.
Opaque AppliedOperator'_of_gen_tree.

Lemma AppliedOperator'_of_to_gen_tree
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {T_eqdec : EqDecision builtin}
    {T_countable : Countable builtin}
    (a : AppliedOperator' symbol builtin)
    : AppliedOperator'_of_gen_tree symbol builtin (AppliedOperator'_to_gen_tree symbol builtin a) = Some a
.
Proof.
    ltac1:(funelim (AppliedOperator'_to_gen_tree symbol builtin a)).
    {
        ltac1:(simp AppliedOperator'_to_gen_tree).
        ltac1:(simp AppliedOperator'_of_gen_tree).
        reflexivity.
    }
    {
        ltac1:(simp AppliedOperator'_to_gen_tree).
        ltac1:(simp AppliedOperator'_of_gen_tree).
        ltac1:(rewrite ! Pos2Nat.id decode_encode).
        unfold AppliedOperator'_of_gen_tree_clause_2.
        unfold AppliedOperator'_of_gen_tree_clause_2_clause_1.
        rewrite decode_encode.
        ltac1:(rewrite H).
        unfold AppliedOperator'_of_gen_tree_clause_2_clause_1_clause_1.
        reflexivity.
    }
    {
        ltac1:(simp AppliedOperator'_to_gen_tree).
        ltac1:(simp AppliedOperator'_of_gen_tree).
        ltac1:(rewrite ! Pos2Nat.id decode_encode).
        unfold AppliedOperator'_of_gen_tree_clause_2.
        unfold AppliedOperator'_of_gen_tree_clause_2_clause_2.
        unfold AppliedOperator'_of_gen_tree_clause_2_clause_2_clause_1.
        ltac1:(rewrite H).
        ltac1:(rewrite H0).
        reflexivity.
    }
Qed.

#[export]
Instance appliedSymbol_countable
    (symbol : Set)
    {symbols : Symbols symbol}
    (builtin : Set)
    {builtin_eqdec : EqDecision builtin}
    {builtin_countable : Countable builtin}
    : Countable (AppliedOperator' symbol builtin)
.
Proof.
    apply inj_countable
    with
        (f := (AppliedOperator'_to_gen_tree symbol builtin ))
        (g := AppliedOperator'_of_gen_tree symbol builtin)
    .
    intros x.
    apply AppliedOperator'_of_to_gen_tree.
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
        -> (AppliedOperator' symbol builtin_value)
        -> Prop ;

    builtin_binary_predicate_interp
        : builtin_binary_predicate 
        -> (AppliedOperator' symbol builtin_value)
        -> (AppliedOperator' symbol builtin_value)
        -> Prop ;
    
    builtin_unary_function_interp
        : builtin_unary_function
        -> (AppliedOperator' symbol builtin_value)
        -> (AppliedOperator' symbol builtin_value) ;

    builtin_binary_function_interp
        : builtin_binary_function
        -> (AppliedOperator' symbol builtin_value)
        -> (AppliedOperator' symbol builtin_value)
        -> (AppliedOperator' symbol builtin_value) ;
}.

Class Signature := {
    symbol : Set ;
    variable : Set ;
    symbols :: Symbols symbol ;
    builtin :: Builtin ;
    variables :: Variables variable ;
}.

Definition Element {Σ : Signature}
    := AppliedOperator' symbol builtin_value
.

#[export]
Instance Element_eqdec {Σ : Signature}
    : EqDecision Element
.
Proof.
    intros e1 e2.
    apply AppliedOperator'_eqdec.
    apply builtin_value_eqdec.
Defined.


Definition AppliedSymbol {Σ : Signature}
    := AppliedOperator' symbol builtin_value
.

#[export]
Instance AppliedSymbol_eqdec {Σ : Signature}
    : EqDecision AppliedSymbol
.
Proof.
    intros e1 e2.
    apply AppliedOperator'_eqdec.
    apply builtin_value_eqdec.
Defined.

Inductive AtomicProposition {Σ : Signature} :=
| ap1 (p : builtin_unary_predicate) (x : variable)
| ap2 (p : builtin_binary_predicate) (x y : variable)
.

Equations Derive NoConfusion for AtomicProposition.

Definition vars_of_AP
    {Σ : Signature}
    (ap : AtomicProposition)
    : gset variable :=
match ap with
| ap1 _ x => {[x]}
| ap2 _ x y => {[x;y]}
end.

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

Fixpoint vars_of_Constraint
    { Σ : Signature }
    (c : Constraint)
    : gset variable :=
match c with
| c_True => ∅
| c_atomic ap => vars_of_AP ap
| c_and c1 c2 => vars_of_Constraint c1 ∪ vars_of_Constraint c2
| c_not c' => vars_of_Constraint c'
end.

#[export]
Instance constraint_eqdec {Σ : Signature}
    : EqDecision Constraint
.
Proof.
    ltac1:(solve_decision).
Defined.

Inductive BuiltinOrVar {Σ : Signature} :=
| bov_builtin (b : builtin_value)
| bov_variable (x : variable)
.

#[export]
Instance BuiltinOrVar_eqdec {Σ : Signature}
    : EqDecision BuiltinOrVar
.
Proof.
    ltac1:(solve_decision).
Defined.

(* TODO: rename to LhsPattern *)
Inductive Pattern {Σ : Signature} :=
| pat_aop (o : AppliedOperator' symbol BuiltinOrVar)
| pat_requires (p : Pattern) (c : Constraint)
| pat_requires_match (p : Pattern) (v : variable) (p2 : Pattern)
.

Equations Derive NoConfusion for Pattern.

Fixpoint vars_of_aosb
    {Σ : Signature}
    (o : AppliedOperator' symbol BuiltinOrVar)
    : gset variable :=
match o with
| ao_operator _ => ∅
| ao_app_operand o' (bov_builtin _) => vars_of_aosb o'
| ao_app_operand o' (bov_variable x) => {[x]} ∪ vars_of_aosb o'
| ao_app_ao o1 o2 => vars_of_aosb o1 ∪ vars_of_aosb o2
end.

Fixpoint vars_of_Pattern
    {Σ : Signature}
    (φ : Pattern)
    : gset variable :=
match φ with
| pat_aop o => vars_of_aosb o
| pat_requires φ' c => vars_of_Pattern φ' ∪ vars_of_Constraint c
| pat_requires_match φ' x φ'' =>
    {[x]} ∪ vars_of_Pattern φ' ∪ vars_of_Pattern φ''
end
.

#[export]
Instance Pattern_eqdec {Σ : Signature}
    : EqDecision Pattern
.
Proof.
    ltac1:(solve_decision).
Defined.

Fixpoint pattern_size {Σ : Signature} (φ : Pattern) :=
match φ with
| pat_aop _ => 1
| pat_requires p' _ => 1 + pattern_size p'
| pat_requires_match p v p2 => 1 + pattern_size p + pattern_size p2
end.

Inductive FunTerm
    {Σ : Signature}
    :=
| ft_element (e : Element)
| ft_variable (x : variable)
| ft_unary (f : builtin_unary_function) (t : FunTerm)
| ft_binary (f : builtin_binary_function) (t1 : FunTerm) (t2 : FunTerm)
.

Equations Derive NoConfusion for FunTerm.

#[export]
Instance FunTerm_eqdec {Σ : Signature}
    : EqDecision (FunTerm)
.
Proof.
    ltac1:(solve_decision).
Defined.

Fixpoint vars_of_FunTerm
    {Σ : Signature}
    (t : FunTerm)
    : gset variable :=
match t with
| ft_element _ => ∅
| ft_variable x => {[x]}
| ft_unary _ t' => vars_of_FunTerm t'
| ft_binary _ t1 t2 => vars_of_FunTerm t1 ∪ vars_of_FunTerm t2
end.

(* Do we want to be able to return the whole configuration
   from a builtin function? If so, then we need
   the `rpat_ft` constructor.
   But currently we cannot afford that, because then
   a RhsPattern could concretize to a single builtin,
   and the builtin could be applied to something else,
   which is undesirable. But that is very unfortunate,
   because it would mean that we cannot do local rewrites
   to builtins. Hmm...
*)
Inductive RhsPattern {Σ : Signature} := 
| rpat_ft (t : FunTerm)
| rpat_op (op : AppliedOperator' symbol FunTerm)
.

Equations Derive NoConfusion for RhsPattern.

#[export]
Instance RhsPattern_eqdec {Σ : Signature}
    : EqDecision RhsPattern
.
Proof.
    ltac1:(solve_decision).
Defined.

Print AppliedOperator'.

Fixpoint vars_of_AppliedOperator_sym_fterm
    {Σ : Signature}
    (op : AppliedOperator' symbol FunTerm)
    : gset variable :=
match op with
| ao_operator _ => ∅
| ao_app_operand aps' o =>
    vars_of_AppliedOperator_sym_fterm aps' ∪ vars_of_FunTerm o
| ao_app_ao aps1 aps2 =>
    vars_of_AppliedOperator_sym_fterm aps1 ∪ vars_of_AppliedOperator_sym_fterm aps2
end.

Definition vars_of_RhsPattern
    {Σ : Signature}
    (φ : RhsPattern)
    : gset variable :=
match φ with
| rpat_op op => vars_of_AppliedOperator_sym_fterm op
| rpat_ft t => vars_of_FunTerm t
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

    Equations funTerm_evaluate
        (t : FunTerm) : option Element
        by struct t :=
    
    funTerm_evaluate (ft_element e) := Some e ;

    funTerm_evaluate (ft_variable x) := ρ !! x ;

    (* TODO use fmap and "do notation"*)
    funTerm_evaluate (ft_unary f t) with (funTerm_evaluate t) => {
        | Some e := Some (builtin_unary_function_interp f e)
        | None := None
    } ;

    funTerm_evaluate (ft_binary f t1 t2) with (funTerm_evaluate t1), (funTerm_evaluate t2) => {
        | Some e1, Some e2 := Some (builtin_binary_function_interp f e1 e2)
        | _, _ := None
    }
    .

    #[global]
    Opaque funTerm_evaluate.

    (*Equations Derive Subterm for Pattern.*)

    Inductive aosb_satisfies_aosbf:
        AppliedOperator' symbol builtin_value ->
        AppliedOperator' symbol BuiltinOrVar ->
        Prop :=
    
    | asa_sym:
        forall s,
            aosb_satisfies_aosbf
                (ao_operator s)
                (ao_operator s)
    
    | asa_builtin:
        forall φ b v,
            aosb_satisfies_aosbf φ v ->
            aosb_satisfies_aosbf
                (ao_app_operand φ b)
                (ao_app_operand v (bov_builtin b))
    
    | asa_app:
        forall φ1 φ2 v1 v2,
            aosb_satisfies_aosbf φ1 v1 ->
            aosb_satisfies_aosbf φ2 v2 ->
            aosb_satisfies_aosbf
                (ao_app_ao φ1 φ2)
                (ao_app_ao v1 v2)
    .

    Inductive element_satisfies_pattern:
        Element -> Pattern -> Prop :=

    | esp_op :
        forall e φ,
            aosb_satisfies_aosbf e φ ->
            element_satisfies_pattern e (pat_aop φ)
    
    | esp_req:
        forall e φ c,
            element_satisfies_pattern e φ ->
            vars_of_Constraint c ⊆ vars_of_Pattern φ ->
            val_satisfies_c ρ c ->
            element_satisfies_pattern e (pat_requires φ c)

    | esp_req_match :
        forall φ x φ' e e2,
            (ρ !! x) = Some e2 ->
            element_satisfies_pattern e φ  ->
            element_satisfies_pattern e2 φ' ->
            element_satisfies_pattern
                e
                (pat_requires_match φ x φ')
    .

    Inductive aosb_satisfies_aosf:
        AppliedOperator' symbol builtin_value ->
        AppliedOperator' symbol FunTerm
        -> Prop :=

    | asaosf_sym :
        forall s,
            aosb_satisfies_aosf
                (ao_operator s)
                (ao_operator s)

    | asaosf_app_operand_1 :
        forall aps1 t aps1' b,
            aosb_satisfies_aosf aps1' aps1  ->
            funTerm_evaluate t = Some (el_builtin b) ->
            aosb_satisfies_aosf
                (ao_app_operand aps1' b)
                (ao_app_operand aps1 t)

    | asaosf_app_operand_2 :
        forall aps1 t aps1' v,
            aosb_satisfies_aosf aps1' aps1 ->
            funTerm_evaluate t = Some (el_appsym v) ->
            aosb_satisfies_aosf
                (ao_app_ao aps1' v)
                (ao_app_operand aps1 t)

    | asaosf_app_aps :
        forall aps1 aps2 aps1' aps2',
            aosb_satisfies_aosf aps1' aps1 ->
            aosb_satisfies_aosf aps2' aps2 ->
            aosb_satisfies_aosf
                (ao_app_ao aps1' aps2')
                (ao_app_ao aps1 aps2)
    .

    Inductive element_satisfies_rhs_pattern:
        Element -> RhsPattern -> Prop :=
    | esrp_ft:
        forall e t,
            funTerm_evaluate t = Some e ->
            element_satisfies_rhs_pattern
                e
                (rpat_ft t)
    | esrp_op:
        forall aps op,
            aosb_satisfies_aosf aps op ->
            element_satisfies_rhs_pattern
                (el_appsym aps)
                (rpat_op op)
    .

End with_signature.

Lemma funTerm_evalute_total_iff
    {Σ : Signature}
    (t : FunTerm)
    (ρ : Valuation)
    :
    (∃ e:Element, funTerm_evaluate ρ t = Some e)
    <->
    ( vars_of_FunTerm t ⊆ dom ρ )
.
Proof.
    induction t; cbn.
    {
        split; intros H.
        {
            apply empty_subseteq.
        }
        {
            exists e.
            ltac1:(simp funTerm_evaluate).
            reflexivity.
        }
    }
    {
        split; intros H.
        {
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            rewrite elem_of_singleton in Hx0.
            subst x0.
            destruct H as [e H].
            ltac1:(simp funTerm_evaluate in H).
            ltac1:(fold_classes).
            ltac1:(rewrite elem_of_dom).
            exists e. exact H.
        }
        {
            rewrite elem_of_subseteq in H.
            specialize (H x).
            rewrite elem_of_singleton in H.
            specialize (H erefl).
            ltac1:(rewrite elem_of_dom in H).
            unfold is_Some in H.
            destruct H as [e H].
            exists e.
            ltac1:(simp funTerm_evaluate in H).
        }
    }
    {
        ltac1:(simp funTerm_evaluate).
        unfold funTerm_evaluate_clause_3.
        ltac1:(rewrite <- IHt).
        split; intros [e H].
        {
            ltac1:(case_match).
            {
                ltac1:(rewrite <- H0).
                eexists.
                exact H0.
            }
            {
                inversion H.
            }
        }
        {
            eexists. rewrite H. reflexivity.
        }
    }
    {
        rewrite union_subseteq.
        ltac1:(rewrite <- IHt1).
        ltac1:(rewrite <- IHt2).
        split; intros H.
        {
            destruct H as [e H].
            ltac1:(simp funTerm_evaluate in H).
            unfold funTerm_evaluate_clause_4_clause_1 in H.
            (repeat ltac1:(case_match)); ltac1:(simplify_eq /=);
                split; eexists; reflexivity.
        }
        {
            destruct H as [[e1 H1] [e2 H2]].
            ltac1:(simp funTerm_evaluate).
            unfold funTerm_evaluate_clause_4_clause_1.
            rewrite H1.
            rewrite H2.
            eexists. reflexivity.
        }
    }
Qed.

Record LocalRewrite {Σ : Signature} := {
    lr_from : Pattern ;
    lr_to : RhsPattern ;
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

Lemma lhs_sat_impl_good_valuation
    {Σ : Signature} e φ ρ:
    element_satisfies_pattern ρ e φ ->
    vars_of_Pattern φ ⊆ dom ρ
.
Proof.
    intros H.
    induction H; cbn; try (ltac1:(set_solver)).
    { 
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        rewrite elem_of_singleton in Hx0.
        subst.
        ltac1:(rewrite elem_of_dom).
        exists e.
        exact H.
    }
    {
        ltac1:(rewrite !union_subseteq).
        repeat split; try assumption.
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        rewrite elem_of_singleton in Hx0.
        subst.
        ltac1:(rewrite elem_of_dom).
        exists e2.
        exact H.
    }
Qed.


Lemma good_valuation_impl_rhs_sat_helper
    {Σ : Signature} φ ρ:
    vars_of_AppliedOperator_sym_fterm φ ⊆ dom ρ ->
    exists e, aosb_satisfies_aosf ρ e φ
.
Proof.
    induction φ; cbn; intros H.
    {
        eexists. econstructor.
    }
    {
        rewrite union_subseteq in H.
        destruct H as [H1 H2]; cbn.
        specialize (IHφ H1).
        ltac1:(rewrite -funTerm_evalute_total_iff in H2).
        destruct IHφ as [e1 IHφ].
        destruct H2 as [e2 He2]; cbn.
        destruct e2; cbn.
        {
            eexists. econstructor.
            apply IHφ.
            exact He2.
        }
        {
            eexists. apply asaosf_app_operand_2.
            { apply IHφ. }
            { apply He2. }
        }
    }
    {
        rewrite union_subseteq in H.
        destruct H as [H1 H2].
        specialize (IHφ1 H1).
        specialize (IHφ2 H2).
        destruct IHφ1 as [e1 IHφ1].
        destruct IHφ2 as [e2 IHφ2].
        eexists. econstructor.
        { apply IHφ1. }
        { apply IHφ2. }
    }
Qed.

Lemma good_valuation_impl_rhs_sat
    {Σ : Signature} φ ρ:
    vars_of_RhsPattern φ ⊆ dom ρ ->
    exists e, element_satisfies_rhs_pattern ρ e φ
.
Proof.
    destruct φ; cbn.
    {
        intros H.
        ltac1:(rewrite -funTerm_evalute_total_iff in H).
        destruct H as [e H].
        exists e.
        constructor.
        exact H.
    }
    {
        intros H.
        apply good_valuation_impl_rhs_sat_helper in H.
        destruct H as [e H].
        eexists. econstructor. 
        apply H.
    }
Qed.


Definition lr_satisfies
    {Σ : Signature} (left_right : LR) (e : Element) (lr : LocalRewrite) (ρ : Valuation)
    : Prop :=
match left_right with
| LR_Left =>
    element_satisfies_pattern ρ e (lr_from lr)
| LR_Right =>
    element_satisfies_rhs_pattern ρ e (lr_to lr)
end
.

Print Pattern.
Inductive RewritingRule {Σ : Signature} :=
| rr_local_rewrite (lr : LocalRewrite)
| rr_builtin (b : builtin_value)
| rr_app (r1 r2 : RewritingRule)
| rr_var (v : variable)
| rr_sym (s : symbol)
| rr_requires (r : RewritingRule) (c : Constraint)
| rr_requires_match (r : RewritingRule) (v : variable) (p2 : Pattern) 
.

Equations Derive NoConfusion for RewritingRule.

Fixpoint RewritingRule_size {Σ : Signature} (r : RewritingRule) : nat :=
match r with
| rr_local_rewrite _ => 1
| rr_builtin _ => 1
| rr_app r1 r2 => 1 + RewritingRule_size r1 + RewritingRule_size r2
| rr_var _ => 1
| rr_sym _ => 1
| rr_requires r _ => 1 + RewritingRule_size r
| rr_requires_match r _ _ => 1 + RewritingRule_size r
end.

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

    Print Pattern.

    Inductive rr_satisfies :
        RewritingRule -> Element -> Prop :=
        
    | rr_sat_local :
        forall e lr
            (Hvars : vars_of_RhsPattern (lr_to lr) ⊆ vars_of_Pattern (lr_from lr))
            (Hsat : lr_satisfies left_right e lr ρ),
            rr_satisfies (rr_local_rewrite lr) e
    
    | rr_sat_builtin :
        forall b,
            rr_satisfies (rr_builtin b) (el_builtin b)

    | rr_sat_var :
        forall x e
            (Hlookup : ρ !! x = Some e),
            rr_satisfies (rr_var x) e
    
    | rr_sat_sym :
        forall s,
            rr_satisfies (rr_sym s) (el_appsym (ao_operator s))
    
    | rr_sat_app_1 :
        forall φ1 φ2 aps1 aps2
            (Hsat1 : rr_satisfies φ1 (el_appsym aps1))
            (Hsat2 : rr_satisfies φ2 (el_appsym aps2)),
            rr_satisfies (rr_app φ1 φ2) (el_appsym (ao_app_ao aps1 aps2))
    
    | rr_sat_app_2 :
        forall φ1 φ2 aps1 b2
            (Hsat1 : rr_satisfies φ1 (el_appsym aps1))
            (Hsat2 : rr_satisfies φ2 (el_builtin b2)),
            rr_satisfies (rr_app φ1 φ2) (el_appsym (ao_app_operand aps1 b2))
    
    | rr_sat_req :
        forall r c e
            (Hsat1 : rr_satisfies r e)
            (Hsat2 : (val_satisfies_c ρ c  \/ left_right = LR_Right)),
            rr_satisfies (rr_requires r c) e
    
    | rr_sat_req_match :
        forall r x φ' e e2
            (Hsat1 : rr_satisfies r e)
            (Hlookup : ρ !! x = Some e2)
            (Hsat2 : (element_satisfies_pattern ρ e2 φ' \/ left_right = LR_Right)),
            rr_satisfies (rr_requires_match r x φ') e
    .

End sec.
(*
Lemma rr_weakly_well_defined_0 {Σ : Signature} rr ρ aps:
    rr_satisfies LR_Left ρ rr (el_appsym aps) ->
    ∃ aps', rr_satisfies LR_Right ρ rr (el_appsym aps').
Proof.
    intros H.
    induction H; cbn.
    {
        destruct lr; cbn in *.
        apply lhs_sat_impl_good_valuation in Hsat.
        assert (Hvars2 : vars_of_RhsPattern lr_to0 ⊆ dom ρ).
        { ltac1:(set_solver). }
        apply good_valuation_impl_rhs_sat in Hvars2.
        destruct Hvars2 as [e' He'].
        eexists. econstructor; cbn.
        { ltac1:(set_solver). }
        { apply He'. }
    }
Qed.
*)
Lemma rr_weakly_well_defined {Σ : Signature} rr ρ e:
    rr_satisfies LR_Left ρ rr e ->
    ∃ e', rr_satisfies LR_Right ρ rr e'.
Proof.
    intros H.
    induction H; cbn.
    {
        destruct lr; cbn in *.
        apply lhs_sat_impl_good_valuation in Hsat.
        assert (Hvars2 : vars_of_RhsPattern lr_to0 ⊆ dom ρ).
        { ltac1:(set_solver). }
        apply good_valuation_impl_rhs_sat in Hvars2.
        destruct Hvars2 as [e' He'].
        eexists. econstructor; cbn.
        { ltac1:(set_solver). }
        { apply He'. }
    }
    {
        eexists. econstructor.
    }
    {
        eexists. econstructor. apply Hlookup.
    }
    {
        eexists. econstructor.
    }
    {
        destruct IHrr_satisfies1 as [e1 He1].
        destruct IHrr_satisfies2 as [e2 He2].
        (* eexists (el_appsym ?[aps']). *)
        destruct e1.
        {
            inversion He1; subst;
                        eexists;
            apply rr_sat_app_2.
            {
                econstructor.
                { exact Hvars. }
                {}
            }
        }
        eexists.
        apply rr_sat_app_1.
        {}
        destruct e1, e2.
        { eexists. apply rr_sat_app_2. }
        eexists.
        apply rr_sat_app_2.
        { apply He1. }
        { apply He2. }
    }
    {

    }

Qed.

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
    := (forall e,
        stuck Γ e -> interpreter e = None)
    /\ (forall e,
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




