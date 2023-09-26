From Coq Require Import ssreflect ssrfun ssrbool.
From Coq.Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable decidable finite list list_numbers gmap strings.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
Set Equations Transparent.

Require Import Wellfounded.
From Ltac2 Require Import Ltac2.

From Minuska Require Import tactics minuska.

(*
#[export]
Instance rr_satisfies_dec
    {Σ : Signature}
    (left_right : LR)
    (ρ : Valuation)
    (r : RewritingRule)
    (e : Element)
    : Decision (rr_satisfies left_right ρ r e)
.
Proof. Admitted.
*)

Section with_decidable_signature.
    Context
        {Σ : Signature}
        (up_dec : forall p e, Decision (builtin_unary_predicate_interp p e))
        (bp_dec : forall p e1 e2, Decision (builtin_binary_predicate_interp p e1 e2))
    .

    #[export]
    Instance val_satisfies_ap_dec
        ρ ap
        : Decision (val_satisfies_ap ρ ap)
    .
    Proof.
        destruct ap; cbn; repeat (ltac1:(case_match));
            try (solve[right; intros []]).
        {
            apply _.
        }
        {
            apply _.
        }
    Defined.

    #[export]
    Instance val_satisfies_c_dec
        ρ c
        : Decision (val_satisfies_c ρ c)
    .
    Proof.
        revert ρ.
        induction c; intros ρ; cbn.
        { left. exact I. }
        { apply _. }
        { apply and_dec; auto with nocore. }
        { apply not_dec. apply IHc. }
    Defined.

    Fixpoint evaluate_rhs_pattern
        (ρ : Valuation)
        (φ : RhsPattern)
        : option Element :=
    match φ with
    | spat_builtin v => Some (el_builtin v)
    | spat_sym s => Some (el_appsym (aps_operator s))
    | spat_app φ1 φ2 =>
        let oe1 : option Element := (evaluate_rhs_pattern ρ φ1) in
        let oe2 : option Element := (evaluate_rhs_pattern ρ φ2) in
        match oe1,oe2 with
        | Some (el_appsym aps1), Some (el_appsym aps2) =>
            Some (el_appsym (aps_app_aps aps1 aps2))
        | Some (el_appsym aps1), Some (el_builtin b) =>
            Some (el_appsym (aps_app_operand aps1 b))
        | _,_ => None
        end
    | spat_var x => ρ !! x (* Is this necessary when we have FunTerms? *)
    | spat_ft t => funTerm_evaluate ρ t
    end
    .

    Lemma evaluate_rhs_pattern_correct
        (φ : RhsPattern)
        (ρ : Valuation)
        (e : Element)
        : evaluate_rhs_pattern ρ φ = Some e ->
        element_satisfies_rhs_pattern_in_valuation e φ ρ
    .
    Proof.
        intros H.
        unfold element_satisfies_rhs_pattern_in_valuation.

        ltac1:(funelim (element_satisfies_rhs_pattern' ρ φ e));
            ltac1:(simp element_satisfies_rhs_pattern');
            simpl in *.
        all: try (solve[ltac1:(simplify_eq /=);
            try reflexivity;
            repeat ltac1:(case_match);
            ltac1:(simplify_eq /=);
            try ltac1:(naive_solver)]).

    Qed.

    Fixpoint evaluate_pattern
        (ρ : Valuation)
        (φ : Pattern)
        : option Element :=
    match φ with
    | pat_builtin v => Some (el_builtin v)
    | pat_sym s => Some (el_sym s)
    | pat_app φ1 φ2 =>
        let oe1 := (evaluate_pattern ρ φ1) in
        let oe2 := (evaluate_pattern ρ φ2) in
        match oe1,oe2 with
        | Some e1, Some e2 =>
            Some (el_app e1 e2)
        | _,_ => None
        end
    | pat_var x => ρ !! x
    | pat_requires φ' c =>
        if (base.decide (val_satisfies_c ρ c))
        then
            evaluate_pattern ρ φ'
        else
            None
    | pat_requires_match φ x φ' =>
        match (evaluate_pattern ρ φ') with
        | None => None
        | Some e =>
            if (decide (ρ !! x = Some e))
            then evaluate_pattern ρ φ
            else None
        end        
    end
    .


    Lemma evaluate_pattern_correct
        (φ : Pattern)
        (ρ : Valuation)
        (e : Element)
        : evaluate_pattern ρ φ = Some e ->
        element_satisfies_pattern_in_valuation e φ ρ
    .
    Proof.
        intros H.
        unfold element_satisfies_pattern_in_valuation.
        ltac1:(funelim (element_satisfies_pattern' ρ φ e));
            cbn; ltac1:(simp evaluate_pattern in H); cbn in *;
            try (solve [inversion H; subst; reflexivity]).
        {
            repeat ltac1:(case_match); inversion H.
        }
        {
            repeat ltac1:(case_match); inversion H.
        }
        {
            repeat ltac1:(case_match);
                try (inversion H; subst; clear H);
                try (inversion H1; subst; clear H1).
            ltac1:(naive_solver).
        }
        {
            unfold decide,is_left in H0.
            repeat ltac1:(case_match); repeat split; try (ltac1:(naive_solver)).
        }
        {
            destruct Heqcall.
            unfold decide,is_left in H1.
            (repeat ltac1:(case_match)); (ltac1:(naive_solver)).
        }
        {
            unfold is_left,decide in H.
            (repeat ltac1:(case_match)); (ltac1:(naive_solver)).
        }
    Qed.

    Fixpoint rhs_evaluate_rule
        (ρ : Valuation)
        (r : RewritingRule)
        : option Element :=
    match r with
    | rr_local_rewrite lr =>
        evaluate_simple_pattern ρ (lr_to lr)
    | rr_builtin b => Some (el_builtin b)
    | rr_app r1 r2 =>
        let oe1 := rhs_evaluate_rule ρ r1 in
        let oe2 := rhs_evaluate_rule ρ r2 in
        match oe1,oe2 with
        | Some e1, Some e2 => Some (el_app e1 e2)
        | _,_ => None
        end
    | rr_var x => ρ !! x
    (* We CANNOT ignore requires clauses when evaluating RHS*)
    | rr_requires r' c =>
        if (decide (val_satisfies_c ρ c)) then rhs_evaluate_rule ρ r' else None
    | rr_requires_match r' x φ =>
        match (evaluate_pattern ρ φ) with
        | None => None
        | Some e => if (decide (ρ !! x = Some e)) then None else None
        end
    end
    .

    Lemma rhs_evaluate_rule_correct
        (r : RewritingRule)
        (ρ : Valuation)
        (e : Element)
        : rhs_evaluate_rule ρ r = Some e ->
        rr_satisfies LR_Right ρ r e
    .
    Proof.
        intros H.
        ltac1:(funelim (rr_satisfies LR_Right ρ r e));
            cbn in *;
            unfold decide,is_left in *;
            try (solve [(repeat ltac1:(case_match)); try ltac1:(naive_solver)]).
        {
            apply evaluate_simple_pattern_correct.
            exact H.
        }
    Qed.

    Definition lhs_match_one
        (e : Element)
        (r : RewritingRule)
        : option Valuation
    .
    Admitted.

    Lemma lhs_match_one_Some
        (e : Element)
        (r : RewritingRule)
        (ρ : Valuation)
        :
        lhs_match_one e r = Some ρ <->
        rr_satisfies LR_Left ρ r e
    .
    Proof. Admitted.

    Lemma lhs_match_one_None
        (e : Element)
        (r : RewritingRule)
        :
        lhs_match_one e r = None <-> 
        ~ exists (ρ : Valuation),
            rr_satisfies LR_Left ρ r e
    .
    Proof.
    Admitted.


    Definition thy_lhs_match_one
        (e : Element)
        (Γ : RewritingTheory)
        : option (RewritingRule * Valuation)%type
        := let vs : list (option Valuation) := lhs_match_one e <$> Γ in
        let found : option (nat * option Valuation) := list_find is_Some vs in
        match found with
        | None => None
        | Some (_, None) => None
        | Some (n, Some v) => (
            match Γ !! n with
            | Some r => Some (r, v)
            | None => None
            end)
        end
    .

    Lemma thy_lhs_match_one_None
        (e : Element)
        (Γ : RewritingTheory)
        :
        thy_lhs_match_one e Γ = None ->
        ~ exists (r : RewritingRule) (ρ : Valuation),
            r ∈ Γ /\ rr_satisfies LR_Left ρ r e
    .
    Proof.
        unfold thy_lhs_match_one.
        intros H [r [ρ [Hin HContra]]].
        destruct (list_find is_Some (lhs_match_one e <$> Γ)) eqn:Heqfound.
        {
            destruct p as [n oρ].
            rewrite list_find_Some in Heqfound.
            ltac1:(destruct Heqfound as [Hfound [HSome HFirst]]).
            destruct oρ.
            {
                subst. clear HFirst.
                destruct (Γ !! n) eqn:Heq.
                { inversion H. }
                clear H. clear HSome.
                rewrite list_lookup_fmap in Hfound.
                ltac1:(rewrite Heq in Hfound).
                cbn in Hfound.
                inversion Hfound.
            }
            {
                inversion HSome. inversion H0.
            }
        }
        {
            clear H.
            rewrite list_find_None in Heqfound.
            rewrite Forall_forall in Heqfound.
            specialize (Heqfound (Some ρ)).
            ltac1:(rewrite elem_of_list_fmap in Heqfound).
            ltac1:(feed specialize Heqfound).
            {
                exists r.
                split.
                {
                    symmetry.
                    apply lhs_match_one_Some.
                    exact HContra.
                }
                {
                    exact Hin.
                }
            }
            {
                unfold is_Some.
                exists ρ. reflexivity.
            }
            exact Heqfound.
        }
    Qed.


    Lemma thy_lhs_match_one_Some
        (e : Element)
        (Γ : RewritingTheory)
        (r : RewritingRule)
        (ρ : Valuation)
        :
        thy_lhs_match_one e Γ = Some (r, ρ) ->
        r ∈ Γ /\ rr_satisfies LR_Left ρ r e
    .
    Proof.
        intros H.
        unfold thy_lhs_match_one in H.
        unfold is_Some in H.
        (repeat ltac1:(case_match)); subst.
        {
            inversion H; subst; clear H.
            ltac1:(rewrite list_find_Some in H0).
            ltac1:(rewrite list_lookup_fmap in H0).
            ltac1:(rewrite H3 in H0).
            ltac1:(rewrite fmap_Some in H0).
            ltac1:(destruct_and!).
            destruct_ex!.
            ltac1:(destruct_and!).
            ltac1:(simplify_eq /=).
            symmetry in H0.
            ltac1:(rewrite lhs_match_one_Some in H0).
            split>[()|apply H0].
            apply elem_of_list_lookup_2 in H3.
            exact H3.
        }
        {
            inversion H.
        }
        {
            inversion H.
        }
        {
            inversion H.
        }
    Qed.

    Definition naive_interpreter
        (Γ : RewritingTheory)
        (e : Element)
        : option Element
    :=
        let oρ : option (RewritingRule*Valuation) := thy_lhs_match_one e Γ in
        match oρ with
        | None => None
        | Some (r,ρ) => (rhs_evaluate_rule ρ r)
        end
    .

    Lemma naive_interpreter_sound
        (Γ : RewritingTheory)
     : Interpreter_sound Γ (naive_interpreter Γ).
    Proof.
        split.
        {
            unfold naive_interpreter.
            unfold Interpreter_sound.
            unfold stuck,not_stuck.
            intros e Hstuck.
            destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
            {
                destruct p as [r ρ].
                {
                    apply thy_lhs_match_one_Some in Hmatch.
                    destruct Hmatch as [Hin Hsat].
                    ltac1:(rewrite -lhs_match_one_Some in Hsat).
                    unfold rewriting_relation, rewrites_to in Hstuck.
                    destruct (rhs_evaluate_rule ρ r) eqn:Heval; cbn in *.
                    {
                        apply lhs_match_one_Some in Hsat.
                        apply rhs_evaluate_rule_correct in Heval.
                        ltac1:(exfalso).
                        apply Hstuck. clear Hstuck.
                        unfold rewrites_in_valuation_to.
                        exists e0.
                        exists r.
                        split.
                        { exact Hin. }
                        exists ρ.
                        split; assumption.
                    }
                    {
                        reflexivity.
                    }
                }
            }
            {
                reflexivity.
            }
        }
        {
            intros Hwwd e Hnotstuck.
            unfold naive_interpreter.
            destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
            {
                destruct p as [r ρ]; cbn in *.
                apply thy_lhs_match_one_Some in Hmatch.
                destruct Hmatch as [Hin Hsat].
                destruct (rhs_evaluate_rule ρ r) eqn:Heval.
                {
                    exists e0. reflexivity.
                }
                {
                    ltac1:(exfalso).
                    unfold thy_weakly_well_defined in Hwwd.
                    specialize (Hwwd r Hin).
                    unfold rule_weakly_well_defined in Hwwd.
                    specialize (Hwwd e ρ Hsat).
                    destruct Hwwd as [e' Hsate'].
                    Search rhs_evaluate_rule.
                }
                Search rhs_evaluate_rule.
            }
        }
    Qed.

End with_decidable_signature.
