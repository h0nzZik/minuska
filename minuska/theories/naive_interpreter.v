
From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    flattened
    flatten
    basic_matching
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.

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



    Definition use_left (og1 og2: option GroundTerm): option GroundTerm :=
    match og1, og2 with
    | None, None => None
    | Some g1, None => Some g1
    | None, Some g2 => Some g2
    | Some g1, Some g2 => Some g1
    end.

    Definition valuations_compatible (ρ1 ρ2 : Valuation) : Prop
        := Forall (fun k => ρ1 !! k = ρ2 !! k) (elements (dom ρ1 ∩ dom ρ2))
    .

    Instance valautions_compatible_dec:
        forall ρ1 ρ2, Decision (valuations_compatible ρ1 ρ2)
    .
    Proof.
        intros.
        unfold valuations_compatible.
        ltac1:(solve_decision).
    Defined.

    (* TODO fix the case when ρ1 ≡ ρ2 ≡ {[x → 2]} *)
    Definition merge_valuations (ρ1 ρ2 : Valuation)
        : option Valuation :=
    if decide (valuations_compatible ρ1 ρ2)
    then
        Some (merge use_left ρ1 ρ2)
    else
        None
    .

    (* what if we match against `s x x` ?  *)
    Fixpoint ApppliedOperator'_try_match_AppliedOperator'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Operand1 -> Operand2 -> option Valuation)
        (matches_app_1 :
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            option Valuation
        )
        (matches_app_2 :
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            option Valuation
        )
        (x : AppliedOperator' Operator Operand1)
        (y : AppliedOperator' Operator Operand2)
        : option Valuation :=
    match x, y with
    | ao_operator a1, ao_operator a2 =>
        if decide (a1 = a2) then Some ∅ else None
    | ao_operator _, ao_app_operand _ _ => None
    | ao_operator _, ao_app_ao _ _ => None
    | ao_app_operand _ _ , ao_operator _ => None
    | ao_app_operand app1 o1, ao_app_operand app2 o2 =>
        ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2;
        ρ2 ← matches o1 o2;
        merge_valuations ρ1 ρ2

    | ao_app_operand app1 o1, ao_app_ao app2 o2 =>
        ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2 ;
        ρ2 ← matches_app_1 o1 o2;
        merge_valuations ρ1 ρ2

    | ao_app_ao app1 o1, ao_operator _ => None

    | ao_app_ao app1 o1, ao_app_operand app2 o2 =>
        ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2 ;
        ρ2 ← matches_app_2 o1 o2;
        merge_valuations ρ1 ρ2

    | ao_app_ao app1 o1, ao_app_ao app2 o2 =>
        ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2 ;
        ρ2 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            o1
            o2 ;
        merge_valuations ρ1 ρ2
    end.

    Definition ApppliedOperatorOr'_try_match_AppliedOperatorOr'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Operand1 -> Operand2 -> option Valuation)
        (matches_app_1 :
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            option Valuation
        )
        (matches_app_2 :
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            option Valuation
        )
        (x : AppliedOperatorOr' Operator Operand1)
        (y : AppliedOperatorOr' Operator Operand2)
        : option Valuation :=
    match x, y with
    | aoo_app _ _ app1, aoo_app _ _ app2 =>
        ApppliedOperator'_try_match_AppliedOperator'
            Operator
            Operand1 Operand2
            matches matches_app_1 matches_app_2
            app1 app2
    | aoo_app _ _ app1, aoo_operand _ _ o2 =>
        matches_app_2 app1 o2
    | aoo_operand _ _ o1, aoo_app _ _ app2 =>
        matches_app_1 o1 app2
    | aoo_operand _ _ o1, aoo_operand _ _ o2 =>
        matches o1 o2
    end.

    

    Definition GroundTerm_try_match_OpenTerm:
        GroundTerm -> OpenTerm -> option Valuation :=
        ApppliedOperatorOr'_try_match_AppliedOperatorOr'
            symbol
            builtin_value
            BuiltinOrVar
            (builtin_value_try_match_BuiltinOrVar)
            (fun x y => None)
            (pure_GroundTerm_try_match_BuiltinOrVar)
    .

    
    Definition evaluate_match
        (ρ : Valuation)
        (m : Match)
        : bool :=
    match m with
    | mkMatch _ x φ =>
        match ρ !! x with
        | None => false
        | Some g => GroundTerm_matches_OpenTerm ρ g φ
        end
    end.

    Definition evaluate_sc
        (ρ : Valuation)
        (sc : SideCondition)
        : bool :=
    match sc with
    | sc_constraint c =>
        bool_decide (val_satisfies_c ρ c)
    | sc_match m =>
        evaluate_match ρ m
    end.

    Definition evaluate_rhs_pattern
            (ρ : Valuation)
            (φ : AppliedOperatorOr' symbol Expression)
            : option GroundTerm :=
        let f : Expression -> option GroundTerm
            := (Expression_evaluate ρ) in
        let fφ  : AppliedOperatorOr' symbol (option GroundTerm)
            := f <$> φ in 
        let cfφ : option (AppliedOperatorOr' symbol GroundTerm)
            := AppliedOperatorOr'_collapse_option fφ in
        cfφ' ← cfφ;
        let flat := AppliedOperatorOr'_symbol_A_to_OpenTermB id cfφ' in
        Some flat
    .

    Definition rewrite_with
        (r : FlattenedRewritingRule)
        (g : GroundTerm)
        : option GroundTerm
    :=
        ρ ← GroundTerm_try_match_OpenTerm g (fr_from r);
        if decide (Forall (evaluate_sc ρ) (fr_scs r)) then
            evaluate_rhs_pattern ρ (fr_to r)
        else None
    .

    Definition vars_of_valuation (ρ : Valuation) : gset variable :=
        dom ρ
    .


    Lemma pure_GroundTerm_try_match_BuiltinOrVar_correct a b ρ:
        pure_GroundTerm_try_match_BuiltinOrVar a b = Some ρ ->
        pure_GroundTerm_matches_BuiltinOrVar ρ a b = true
    .
    Proof.
        unfold pure_GroundTerm_matches_BuiltinOrVar.
        unfold pure_GroundTerm_try_match_BuiltinOrVar.
        destruct b; intros H; inversion H.
        subst.
        unfold bool_decide.
        ltac1:(case_match); try reflexivity.
        clear H0 H.
        ltac1:(rewrite lookup_insert in n).
        ltac1:(contradiction n).
        reflexivity.
    Qed.

    Lemma evaluate_rhs_pattern_correct
        (φ : RhsPattern)
        (ρ : Valuation)
        (g : GroundTerm)
        : evaluate_rhs_pattern ρ φ = Some g <->
        GroundTerm_satisfies_RhsPattern ρ g φ
    .
    Proof.
        unfold evaluate_rhs_pattern.
        rewrite bind_Some.
        
        ltac1:(
            under [fun e => _]functional_extensionality => e
        ).
        {
            ltac1:(rewrite inj_iff).
            ltac1:(over).
        }
        unfold GroundTerm_satisfies_RhsPattern.
        destruct φ; cbn.
        {
            cbn.
            ltac1:(
                under [fun e => _]functional_extensionality => e
            ).
            {
                ltac1:(rewrite bind_Some).
                ltac1:(
                    under [fun e' => _]functional_extensionality => e'
                ).
                {
                    ltac1:(rewrite inj_iff).
                    ltac1:(over).
                }
                ltac1:(over).
            }
            destruct g; cbn.
            {
                rewrite <- aoxyo_satisfies_aoxzo_comp_iff.
                cbn.
                rewrite -> aoxy_satisfies_aoxz_comp_iff.

                split; intros H.
                {
                    destruct H as [e H].
                    destruct H as [H1 H2].
                    destruct H1 as [e' [H11 H12]].
                    cbn in *.
                    subst.
                    cbn in *.
                    inversion H2; subst; clear H2.
                    cbn in *.
                    inversion H11; subst; clear H11.
                    revert e' H0.
                    induction ao; intros e' H0.
                    {
                        cbn in *.
                        inversion H0; subst; clear H0.
                        constructor.
                    }
                    {
                        cbn in *.
                        rewrite bind_Some in H0.
                        destruct H0 as [x [H1 H2]].
                        rewrite bind_Some in H2.
                        destruct H2 as [x0 H2].
                        destruct H2 as [H2 H3].
                        inversion H3; subst; clear H3.
                        cbn.
                        destruct x0.
                        {
                            constructor.
                            cbn in *.
                            apply IHao.
                            apply H1.
                            cbn.
                            apply H2.
                        }
                        {
                            constructor.
                            cbn in *.
                            apply IHao.
                            apply H1.
                            cbn.
                            apply H2.
                        }
                    }
                    {
                        cbn in *.
                        rewrite bind_Some in H0.
                        destruct H0 as [x [H1 H2]].
                        rewrite bind_Some in H2.
                        destruct H2 as [x0 H2].
                        destruct H2 as [H2 H3].
                        inversion H3; subst; clear H3.
                        specialize (IHao1 _ H1).
                        specialize (IHao2 _ H2).
                        cbn.
                        constructor; assumption.
                    }
                }
                {
                    remember (fun (v:builtin_value) (e':Expression) =>
                        match Expression_evaluate ρ e' with
                        | Some v' => v'
                        | None => aoo_operand _ _ v
                        end
                    ) as zipper.
                    remember (fun (s1 s2 : symbol) => s1) as symleft.
                    remember (fun (g : AppliedOperator' symbol builtin_value) (e' : Expression) =>
                        (aoo_app symbol _ g)
                    ) as f1.
                    remember (fun (b : builtin_value) (et : AppliedOperator' symbol Expression) =>
                        (aoo_operand symbol _ b)
                    ) as f2.
                    remember (AppliedOperator'_zipWith symleft zipper f1 f2 ao0 ao) as zipped.
                    exists (aoo_app _ _ zipped).
                    cbn.
                    split.
                    {
                        exists zipped.
                        subst.
                        repeat constructor.
                        clear -H.


                        induction H.
                        {
                            cbn.
                            reflexivity.
                        }
                        {
                            cbn in H0.
                            cbn.
                            rewrite bind_Some.
                            cbn.
                            ltac1:(
                                under [fun e => _]functional_extensionality => e
                            ).
                            {
                                ltac1:(rewrite bind_Some).
                                ltac1:(
                                    under [fun e' => _]functional_extensionality => e'
                                ).
                                {
                                    ltac1:(rewrite inj_iff).
                                    ltac1:(over).
                                }
                                ltac1:(over).
                            }
                            cbn in *.
                            eexists.
                            split>[apply IHaoxy_satisfies_aoxz|].
                            eexists.
                            split>[apply H0|].
                            apply f_equal.
                            rewrite H0.
                            reflexivity.
                        }
                        {
                            cbn in H0.
                            cbn.
                            rewrite bind_Some.
                            cbn in *.
                            ltac1:(
                                under [fun e => _]functional_extensionality => e
                            ).
                            {
                                ltac1:(rewrite bind_Some).
                                ltac1:(
                                    under [fun e' => _]functional_extensionality => e'
                                ).
                                {
                                    ltac1:(rewrite inj_iff).
                                    ltac1:(over).
                                }
                                ltac1:(over).
                            }
                            cbn in *.
                            eexists.
                            split>[apply IHaoxy_satisfies_aoxz|].
                            eexists.
                            split>[apply H0|].
                            reflexivity.
                        }
                        {
                            cbn in H0.
                            cbn.
                            rewrite bind_Some.
                            cbn in *.
                            ltac1:(
                                under [fun e => _]functional_extensionality => e
                            ).
                            {
                                ltac1:(rewrite bind_Some).
                                ltac1:(
                                    under [fun e' => _]functional_extensionality => e'
                                ).
                                {
                                    ltac1:(rewrite inj_iff).
                                    ltac1:(over).
                                }
                                ltac1:(over).
                            }
                            cbn in *.
                            eexists.
                            split>[apply IHaoxy_satisfies_aoxz1|].
                            eexists.
                            split>[apply IHaoxy_satisfies_aoxz2|].
                            reflexivity.
                        }
                    }
                    {
                        subst. cbn.
                        apply f_equal.
                        induction H.
                        {
                            cbn. reflexivity.
                        }
                        {
                            cbn in *.
                            rewrite H0.
                            rewrite IHaoxy_satisfies_aoxz.
                            reflexivity.
                        }
                        {
                            cbn in *.
                            rewrite IHaoxy_satisfies_aoxz.
                            reflexivity.
                        }
                        {
                            cbn in *.
                            rewrite IHaoxy_satisfies_aoxz1.
                            rewrite IHaoxy_satisfies_aoxz2.
                            reflexivity.
                        }
                    }
                }
            }
            {
                rewrite <- aoxyo_satisfies_aoxzo_comp_iff.
                cbn.
                split; intros H.
                {
                    destruct H as [e H].
                    destruct H as [H1 H2].
                    destruct H1 as [e' [H11 H12]].
                    subst. cbn in *.
                    inversion H2.
                }
                {
                    inversion H.
                }
            }
        }
        {
            ltac1:(
                under [fun e => _]functional_extensionality => e
            ).
            {
                ltac1:(rewrite bind_Some).
                ltac1:(
                    under [fun e' => _]functional_extensionality => e'
                ).
                {
                    ltac1:(rewrite inj_iff).
                    ltac1:(over).
                }
                ltac1:(over).
            }
            ltac1:(rewrite -aoxyo_satisfies_aoxzo_comp_iff).
            cbn.
            destruct g; cbn.
            {
                split; intros H.
                {
                    destruct H as [e H].
                    destruct H as [[e' [H'1 H'2]] H].
                    subst.
                    cbn in H.
                    subst.
                    assumption.
                }
                {
                    eexists.
                    split.
                    {
                        eexists. split>[|reflexivity].
                        apply H.
                    }
                    {
                        cbn. reflexivity.
                    }
                }
            }
            {
                split; intros H.
                {
                    destruct H as [e H].
                    destruct H as [[e' [H'1 H'2]] H].
                    subst.
                    cbn in H.
                    subst.
                    assumption.
                }
                {
                    eexists.
                    split.
                    {
                        eexists. split>[|reflexivity].
                        apply H.
                    }
                    {
                        cbn. reflexivity.
                    }
                }
            }
        }
    Qed.

    Lemma builtin_value_try_match_BuiltinOrVar_correct
        b bov ρ:
        builtin_value_try_match_BuiltinOrVar b bov = Some ρ ->
        builtin_value_matches_BuiltinOrVar ρ b bov = true
        /\ ( (bov = bov_builtin b) \/ (∃ x, bov = bov_variable x /\ ρ !! x = Some (aoo_operand _ _ b)))
    .
    Proof.
        destruct bov; cbn;
          unfold is_left; repeat (ltac1:(case_match)); subst;
          unfold bool_decide; repeat (ltac1:(case_match)); subst;
          intros HH; inversion HH; subst; clear HH; try reflexivity;
          try ltac1:(congruence); subst; repeat split;
          try (solve [left; reflexivity]).
        all: try (
            ltac1:(rewrite lookup_insert in H);
            inversion H; subst; clear H;
            ltac1:(congruence)
        ).
        {
            ltac1:(rewrite lookup_insert in H).
            inversion H; subst; clear H.
            right.
            eexists.
            split>[reflexivity|].
            ltac1:(rewrite lookup_insert).
            reflexivity.
        }
    Qed.

    #[export]
    Instance Valuation_lookup : Lookup variable GroundTerm Valuation.
    Proof.
        apply gmap_lookup.
    Defined.
    
    Lemma merge_valuations_correct (ρ1 ρ2 ρ : Valuation):
        merge_valuations ρ1 ρ2 = Some ρ ->
        map_subseteq ρ1 ρ /\
        map_subseteq ρ2 ρ
    .
    Proof.
        unfold merge_valuations.
        unfold is_left.
        destruct (decide (valuations_compatible ρ1 ρ2)) as [Hcompat|Hnocompat]; intros H.
        {
            inversion H; subst; clear H.
            unfold valuations_compatible in Hcompat.
            rewrite Forall_forall in Hcompat; cbn.
            ltac1:(setoid_rewrite <- elem_of_list_In in Hcompat).
            ltac1:(setoid_rewrite elem_of_elements in Hcompat).
            unfold map_subseteq.
            unfold map_included.
            unfold map_relation.
            unfold option_relation.
            fold (@Valuation Σ) in *.
            fold (@Valuation_lookup) in *.
            split; intros i;
                destruct (ρ1 !! i) eqn:Hρ1i;
                destruct (ρ2 !! i) eqn:Hρ2i;
                destruct (merge use_left ρ1 ρ2 !! i) eqn:Hmergei;
                ltac1:(rewrite Hmergei);
                try (exact I);
                ltac1:(rewrite lookup_merge in Hmergei);
                unfold diag_None in Hmergei;
                specialize (Hcompat i);
                ltac1:(rewrite Hρ1i in Hmergei);
                ltac1:(rewrite Hρ2i in Hmergei);
                unfold use_left in Hmergei;
                ltac1:(simplify_eq /=);
                try reflexivity
            .
            ltac1:(ospecialize (Hcompat _)).
            {
                rewrite elem_of_intersection.
                do 2 ltac1:(rewrite elem_of_dom).
                split; eexists.
                {
                    apply Hρ1i.
                }
                {
                    apply Hρ2i.
                }
            }
            ltac1:(congruence).
        }
        {
            inversion H.
        }
    Qed.

    Lemma builtin_value_matches_BuiltinOrVar_monotone
        (ρ ρ' : Valuation)
        b bov:
        map_subseteq ρ ρ' ->
        builtin_value_matches_BuiltinOrVar ρ b bov = true ->
        builtin_value_matches_BuiltinOrVar ρ' b bov = true
    .
    Proof.
        destruct bov; cbn; auto with nocore.
        unfold map_subseteq,map_included,map_relation,option_relation.
        intros H.
        specialize (H x).
        unfold bool_decide.
        unfold Valuation,Valuation_lookup,GroundTerm,GroundTerm' in *.
        unfold Valuation_lookup in *.
        destruct (ρ !! x) eqn:Heq1, (ρ' !! x) eqn:Heq2; subst; auto.
    Qed.

    Lemma pure_GroundTerm_matches_BuiltinOrVar_monotone
        (ρ ρ' : Valuation)
        g bov:
        map_subseteq ρ ρ' ->
        pure_GroundTerm_matches_BuiltinOrVar ρ g bov ->
        pure_GroundTerm_matches_BuiltinOrVar ρ' g bov
    .
    Proof.
        unfold pure_GroundTerm_matches_BuiltinOrVar.
        destruct bov; cbn; auto with nocore.
        unfold map_subseteq,map_included,map_relation,option_relation.
        intros H.
        specialize (H x).
        unfold bool_decide.
        unfold Valuation,Valuation_lookup,GroundTerm,GroundTerm' in *.
        unfold Valuation_lookup in *.
        destruct (ρ !! x) eqn:Heq1, (ρ' !! x) eqn:Heq2; subst; auto.
    Qed.


    Lemma matches_monotone
        (ρ ρ' : Valuation)
        (a : AppliedOperator' symbol builtin_value)
        (b : AppliedOperator' symbol BuiltinOrVar)
        :
        map_subseteq ρ ρ' ->
        @ApppliedOperator'_matches_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_matches_BuiltinOrVar
            (fun _ _ _ => false)
            pure_GroundTerm_matches_BuiltinOrVar
            ρ a b = true ->

        @ApppliedOperator'_matches_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_matches_BuiltinOrVar
            (fun _ _ _ => false)
            pure_GroundTerm_matches_BuiltinOrVar
            ρ' a b = true
    .
    Proof.
        revert a.
        induction b; intros a HH1 HH2; destruct a; simpl in *;
            try assumption.
        {
            apply andb_true_iff in HH2.
            destruct HH2 as [HH21 HH22].
            rewrite IHb.
            cbn.
            eapply builtin_value_matches_BuiltinOrVar_monotone.
            { apply HH1. }
            { apply HH22. }
            { apply HH1. }
            { exact HH21. }
        }
        {
            apply andb_true_iff in HH2.
            destruct HH2 as [HH21 HH22].
            rewrite IHb.
            cbn.
            eapply pure_GroundTerm_matches_BuiltinOrVar_monotone.
            { apply HH1. }
            { apply HH22. }
            { apply HH1. }
            { exact HH21. }
        }
        {
            rewrite andb_comm in HH2.
            cbn in HH2.
            ltac1:(exfalso; congruence).
        }
        {
            apply andb_true_iff in HH2.
            destruct HH2 as [HH21 HH22].
            rewrite IHb1. rewrite IHb2. reflexivity.
            assumption. assumption. assumption. assumption.
        }
    Qed.

    Lemma merge_valuations_empty_r x:
        merge_valuations x ∅ = Some x
    .
    Proof.
        unfold merge_valuations.
        ltac1:(case_match).
        {
            clear H.
            apply f_equal.
            rewrite <- merge_Some.
            intros i.
            unfold use_left.
            ltac1:(case_match).
            {
                ltac1:(rewrite lookup_empty).
                reflexivity.
            }
            {
                ltac1:(rewrite lookup_empty).
                reflexivity.
            }
            reflexivity.
        }
        {
            unfold is_left in H.
            ltac1:(case_match).
            { inversion H. }
            ltac1:(exfalso).
            apply n.
            unfold Valuation.
            unfold valuations_compatible.
            ltac1:(rewrite dom_empty_L).
            rewrite intersection_empty_r_L.
            rewrite elements_empty.
            apply Forall_nil.
        }
    Qed.

    Lemma merge_valuations_empty_l x:
        merge_valuations ∅ x = Some x
    .
    Proof.
        unfold merge_valuations.
        ltac1:(case_match).
        {
            clear H.
            apply f_equal.
            rewrite <- merge_Some.
            intros i.
            unfold use_left.
            repeat ltac1:(case_match);
                try reflexivity.
            {
                ltac1:(rewrite lookup_empty in H).
                inversion H.
            }
            {
                ltac1:(rewrite lookup_empty in H).
                inversion H.
            }
            reflexivity.
        }
        {
            unfold is_left in H.
            ltac1:(case_match).
            { inversion H. }
            ltac1:(exfalso).
            apply n.
            unfold Valuation.
            unfold valuations_compatible.
            ltac1:(rewrite dom_empty_L).
            rewrite intersection_empty_l_L.
            rewrite elements_empty.
            apply Forall_nil.
        }
    Qed.

    Lemma ApppliedOperatorOr'_try_match_AppliedOperatorOr'_correct
        (ρ ρ' : Valuation)
        (a : AppliedOperator' symbol builtin_value)
        (b : AppliedOperator' symbol BuiltinOrVar)
        :
        map_subseteq ρ ρ' ->
        @ApppliedOperator'_try_match_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_try_match_BuiltinOrVar
            (fun _ _ => None)
            pure_GroundTerm_try_match_BuiltinOrVar
            a b = Some ρ ->

        @ApppliedOperator'_matches_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_matches_BuiltinOrVar
            (fun _ _ _ => false)
            pure_GroundTerm_matches_BuiltinOrVar
            ρ' a b = true
    .
    Proof.
        revert b ρ ρ'.
        induction a; intros b' ρ ρ' HH H; destruct b'; cbn in *; intros.
        {
            intros.
            unfold is_left in *.
            unfold bool_decide.
            repeat ltac1:(case_match); subst; simpl;
                try reflexivity; ltac1:(congruence).
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
        {
            rewrite bind_Some in H.
            destruct H as [x [H21 H22]].
            rewrite bind_Some in H22.
            destruct H22 as [x0 [H221 H222]].

            assert (H221' := H221).
            apply builtin_value_try_match_BuiltinOrVar_correct in H221.
            assert (H222' := H222).
            apply merge_valuations_correct in H222'.
            destruct H222' as [Hsub1 Hsub2].
            destruct H221 as [H2211 H2212].
            cbn.
            destruct H2212 as [HH1|HH2].
            {
                subst.
                cbn.
                unfold bool_decide.
                repeat ltac1:(case_match).
                rewrite andb_true_r.
                (*
                eapply matches_monotone.
                { apply HH. }
                *)
                clear e H.
                cbn in *.
                clear H2211.
                destruct (decide (b = b))>[|ltac1:(congruence)].
                cbn in *.
                inversion H221'; subst; clear H221'.
                clear e.
                rewrite merge_valuations_empty_r in H222.
                inversion H222; subst; clear H222.
                clear Hsub2.
                clear Hsub1.
                specialize (IHa b' ρ ρ' HH).
                apply IHa.
                apply H21.
                ltac1:(congruence).
            }
            {
                destruct HH2 as [x1 [HH3 HH4]].
                subst.
                cbn in *.
                inversion H221'; subst; clear H221'.
                ltac1:(rewrite lookup_insert in H2211).
                clear H2211.
                assert (Htmp: ρ' !! x1 = Some (aoo_operand symbol builtin_value b)).
                {
                    clear -Hsub2 HH.
                    unfold map_subseteq in *.
                    unfold map_included in *.
                    unfold map_relation in *.
                    unfold option_relation in *.
                    specialize (HH x1).
                    specialize (Hsub2 x1).
                    repeat ltac1:(case_match); subst;
                        ltac1:(rewrite lookup_insert in H);
                        inversion H; subst; clear H;
                        try assumption;
                        try ltac1:(contradiction).
                }
                unfold Valuation_lookup in *.
                rewrite Htmp.
                unfold bool_decide.
                ltac1:(case_match); try reflexivity; try ltac1:(congruence).
                clear e H.
                clear HH4.
                assert (Htmp2 := IHa b').
                remember (ApppliedOperator'_matches_AppliedOperator' symbol builtin_value
                    BuiltinOrVar builtin_value_matches_BuiltinOrVar
                    (λ (_ : Valuation) (_ : builtin_value) (_ : AppliedOperator'
                    symbol
                    BuiltinOrVar),
                    false)
                    pure_GroundTerm_matches_BuiltinOrVar)
                as f.
                remember (ApppliedOperator'_try_match_AppliedOperator' symbol
                    builtin_value BuiltinOrVar
                    builtin_value_try_match_BuiltinOrVar
                    (λ (_ : builtin_value) (_ : AppliedOperator' symbol
                    BuiltinOrVar),
                    None)
                    pure_GroundTerm_try_match_BuiltinOrVar)
                as g.
                apply Htmp2 with (ρ' := ρ') in H21.
                {
                    rewrite H21. reflexivity.
                }
                {
                    eapply transitivity.
                    { apply Hsub1. }
                    { apply HH. }
                }
            }
        }
        {
            rewrite bind_Some in H.
            destruct H as [x [H21 H22]].
            inversion H22.
        }
        {
            inversion H.
        }
        {
            rewrite bind_Some in H.
            destruct H as [x [H21 H22]].
            rewrite bind_Some in H22.
            destruct H22 as [x0 [H221 H222]].
            (* TODO: need a lemma about correctness of pure_GroundTerm_try_match_BuiltinOrVar *)
            apply pure_GroundTerm_try_match_BuiltinOrVar_correct in H221.
            assert (Hmv := H222).
            apply merge_valuations_correct in Hmv.
            destruct Hmv as [Hsub1 Hsub2].
            assert (Hxrho': map_subseteq x ρ').
            {
                eapply transitivity.
                apply Hsub1.
                apply HH.
            }
            apply pure_GroundTerm_matches_BuiltinOrVar_monotone with (ρ' := ρ') in H221.
            {
                rewrite H221.
                clear H221.
                remember (ApppliedOperator'_try_match_AppliedOperator' symbol
                    builtin_value BuiltinOrVar
                    builtin_value_try_match_BuiltinOrVar
                    (λ (_ : builtin_value) (_ : AppliedOperator' symbol
                    BuiltinOrVar),
                    None)
                    pure_GroundTerm_try_match_BuiltinOrVar)
                as f.
                specialize (IHa1 b' x ρ' Hxrho' H21).
                rewrite IHa1.
                reflexivity.
            }
            {
                eapply transitivity.
                apply Hsub2.
                apply HH.
            }
        }
        {
            rewrite bind_Some in H.
            destruct H as [x [H21 H22]].
            rewrite bind_Some in H22.
            destruct H22 as [x0 [H221 H222]].
            assert (Hsub := H222).
            apply merge_valuations_correct in Hsub.
            destruct Hsub as [Hsub1 Hsub2].
            assert (Hxρ' : map_subseteq x ρ').
            {
                eapply transitivity.
                apply Hsub1.
                apply HH.
            }
            assert (Hx0ρ' : map_subseteq x0 ρ').
            {
                eapply transitivity.
                apply Hsub2.
                apply HH.
            }
            remember (
                ApppliedOperator'_matches_AppliedOperator' symbol builtin_value
                BuiltinOrVar builtin_value_matches_BuiltinOrVar
                (λ (_ : Valuation) (_ : builtin_value) (_ : AppliedOperator'
                symbol
                BuiltinOrVar),
                false)
                pure_GroundTerm_matches_BuiltinOrVar )
            as f.
            remember (ApppliedOperator'_try_match_AppliedOperator' symbol
                builtin_value BuiltinOrVar
                builtin_value_try_match_BuiltinOrVar
                (λ (_ : builtin_value) (_ : AppliedOperator' symbol
                BuiltinOrVar),
                None)
                pure_GroundTerm_try_match_BuiltinOrVar)
            as g.
            apply andb_true_iff.
            ltac1:(naive_solver).
        }
        Unshelve.
        all: apply map_subseteq_po.
    Qed.

    Lemma builtin_value_try_match_BuiltinOrVar_complete a b ρ:
        builtin_value_matches_BuiltinOrVar ρ a b ->
        ∃ ρ',
            vars_of_valuation ρ' = (vars_of_BoV b) /\
            map_subseteq ρ' ρ /\
            builtin_value_try_match_BuiltinOrVar a b = Some ρ'
    .
    Proof.
        unfold builtin_value_matches_BuiltinOrVar.
        unfold builtin_value_try_match_BuiltinOrVar.
        unfold bool_decide.
        destruct b.
        {
            repeat ltac1:(case_match); subst; try ltac1:(congruence);
                intros _.
            {
                exists ∅.
                cbn.
                split>[reflexivity|].
                split>[|reflexivity].
                cbn.
                unfold Valuation.
                apply map_empty_subseteq.
            }
            {
                inversion H0.
            }
        }
        {
            destruct (ρ!!x) eqn:Hρx.
            {
                destruct a0.
                {
                    intros H; inversion H.
                }
                {
                    ltac1:(case_match).
                    {
                        intros _.
                        exists (<[x:=aoo_operand symbol builtin_value a]> ∅).
                        cbn.
                        unfold vars_of_valuation.
                        split.
                        {
                            ltac1:(rewrite insert_empty).
                            cbn.
                            unfold map_to_list.
                            unfold Valuation.
                            rewrite dom_singleton_L.
                            reflexivity.
                        }
                        split>[|reflexivity].
                        unfold map_subseteq.
                        unfold map_included.
                        unfold map_relation.
                        unfold option_relation.
                        intros i.
                        destruct (decide (i = x)).
                        {
                            subst.
                            ltac1:(rewrite lookup_insert).
                            clear H.
                            ltac1:(rewrite Hρx).
                            reflexivity.
                        }
                        {
                            ltac1:(rewrite lookup_insert_ne).
                            {
                                intros HContra; apply n; subst; reflexivity.
                            }
                            {
                                ltac1:(rewrite lookup_empty).
                                ltac1:(case_match); exact I.
                            }
                        }
                    }
                    {
                        intros H'; inversion H'.
                    }
                }
            }
            {
                intros H; inversion H.
            }
        }
    Qed.

    Lemma merge_use_left_subseteq (ρ1 ρ2 : Valuation):
        map_subseteq ρ1 ρ2 ->
        merge use_left ρ1 ρ2 = ρ2
    .
    Proof.
        unfold map_subseteq.
        unfold map_included.
        unfold map_relation.
        unfold option_relation.
        intros H.
        apply map_subseteq_po.
        {
            unfold Valuation.
            unfold Valuation_lookup.
            rewrite map_subseteq_spec.
            intros i x Hix.
            rewrite lookup_merge in Hix.
            unfold diag_None in Hix.
            unfold use_left in Hix.
            ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
            {
                specialize (H i).
                rewrite H0 in H.
                rewrite H1 in H.
                subst.
                reflexivity.
            }
            {
                specialize (H i).
                rewrite H0 in H.
                rewrite H1 in H.
                inversion H.
            }
        }
        {
            unfold Valuation.
            unfold Valuation_lookup.
            rewrite map_subseteq_spec.
            intros i x Hix.
            rewrite lookup_merge.
            unfold diag_None.
            unfold use_left.
            ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
            specialize (H i).
            rewrite H1 in H.
            rewrite H0 in H.
            subst.
            reflexivity.
        }
    Qed.

    Lemma omap_Some (ρ : Valuation):
        omap [eta Some] ρ = ρ
    .
    Proof.
        rewrite <- map_fmap_alt.
        rewrite map_fmap_id.
        reflexivity.
    Qed.

    Lemma ApppliedOperatorOr'_try_match_AppliedOperatorOr'_complete
        (ρ : Valuation)
        (a : AppliedOperator' symbol builtin_value)
        (b : AppliedOperator' symbol BuiltinOrVar)
        :
        @ApppliedOperator'_matches_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_matches_BuiltinOrVar
            (fun _ _ _ => false)
            pure_GroundTerm_matches_BuiltinOrVar
            ρ a b = true ->
        ∃ ρ',
            vars_of_valuation ρ' = vars_of_aosb b /\
            map_subseteq ρ' ρ /\
            @ApppliedOperator'_try_match_AppliedOperator'
                symbol _ builtin_value BuiltinOrVar
                builtin_value_try_match_BuiltinOrVar
                (fun _ _ => None)
                pure_GroundTerm_try_match_BuiltinOrVar
                a b = Some ρ'
    .
    Proof.
        remember (ApppliedOperator'_matches_AppliedOperator' symbol builtin_value
            BuiltinOrVar builtin_value_matches_BuiltinOrVar
            (λ (_ : Valuation) (_ : builtin_value) (_ : AppliedOperator'
            symbol
            BuiltinOrVar),
            false)
            pure_GroundTerm_matches_BuiltinOrVar)
        as f.
        remember (ApppliedOperator'_try_match_AppliedOperator' symbol
            builtin_value BuiltinOrVar
            builtin_value_try_match_BuiltinOrVar
            (λ (_ : builtin_value) (_ : AppliedOperator' symbol
            BuiltinOrVar),
            None)
            pure_GroundTerm_try_match_BuiltinOrVar)
        as g.

        revert ρ b.
        induction a; intros ρ b''.
        {
            subst f. cbn. unfold bool_decide.
            repeat ltac1:(case_match); subst;
                intros H; try (ltac1:(congruence)).
            clear H.
            cbn.
            unfold is_left.
            repeat ltac1:(case_match).
            {
                exists ∅.
                unfold vars_of_valuation.
                unfold Valuation.
                rewrite dom_empty_L.
                split>[reflexivity|].
                split>[|reflexivity].
                unfold Valuation.
                apply map_empty_subseteq.
            }
            { ltac1:(exfalso; congruence). }
            { ltac1:(exfalso; congruence). }
            { ltac1:(exfalso; congruence). }
        }
        {
            rewrite Heqf.
            rewrite Heqg.
            cbn.
            destruct b''.
            {
                intros H; inversion H.
            }
            {
                intros H.
                rewrite andb_true_iff in H.
                destruct H as [H1 H2].
                rewrite <- Heqf in H1.
                specialize (IHa ρ b'' H1).
                destruct IHa as [ρ' [IH0 [IH1 IH2]]].
                rewrite <- Heqg.
                apply builtin_value_try_match_BuiltinOrVar_complete in H2.
                destruct H2 as [ρ'' [Hρ''0 [Hρ''1 Hρ''2]]].
                rewrite IH2.
                cbn.
                rewrite Hρ''2.
                cbn.
                destruct b0.
                {
                    cbn in *.
                    unfold is_left in *.
                    destruct (decide (b = b0)).
                    {
                        subst. inversion Hρ''2; subst; clear Hρ''2.
                        cbn.
                        rewrite <- IH0.
                        exists ρ'.
                        split>[reflexivity|].
                        split.
                        { exact IH1. }
                        apply merge_valuations_empty_r.
                    }
                    {
                        inversion Hρ''2.
                    }
                }
                {
                    cbn in *.
                    inversion Hρ''2; subst; clear Hρ''2.
                    destruct (ρ' !! x) eqn:Hρ'x.
                    {
                        exists ρ'.
                        cbn.
                        repeat split.
                        {
                            unfold vars_of_valuation.
                            cbn.
                            unfold Valuation.
                            unfold Valuation_lookup.
                            rewrite <- IH0.
                            unfold vars_of_valuation.
                            clear -Hρ'x.
                            apply leibniz_equiv.
                            ltac1:(cut (x ∈ dom ρ')).
                            {
                                ltac1:(set_solver).
                            }
                            unfold Valuation.
                            unfold Valuation_lookup.
                            rewrite elem_of_dom.
                            exists g.
                            exact Hρ'x.
                        }
                        {
                            exact IH1.
                        }
                        {
                            (*clear -Hρ'x.*)
                            unfold merge_valuations.
                            unfold decide,is_left.
                            repeat ltac1:(case_match).
                            {
                                apply f_equal.
                                clear H0 H.
                                unfold valuations_compatible in *.
                                rewrite Forall_forall in v.
                                specialize (v x).
                                ltac1:(rewrite <- elem_of_list_In in v).
                                rewrite elem_of_elements in v.
                                rewrite elem_of_intersection in v.
                                ltac1:(do 2 rewrite elem_of_dom in v).
                                ltac1:(ospecialize (v _)).
                                split; eexists.
                                {
                                    apply Hρ'x.
                                }
                                {
                                    ltac1:(rewrite lookup_insert).
                                    reflexivity.
                                }
                                ltac1:(rewrite lookup_insert in v).
                                ltac1:(rewrite Hρ'x in v).
                                inversion v; subst; clear v.
                                clear Hρ''0.
                                unfold Valuation.
                                ltac1:(
                                    erewrite <- insert_merge_r
                                ).
                                rewrite merge_empty_r.
                                unfold use_left, compose.
                                cbn.
                                rewrite omap_Some.
                                rewrite insert_id.
                                { reflexivity. }
                                { apply Hρ'x. }
                                {
                                    unfold use_left.
                                    ltac1:(rewrite Hρ'x).
                                    reflexivity.
                                }
                            }
                            {
                                inversion H.
                            }
                            {
                                inversion H.
                            }
                            {
                                clear H0 H.
                                unfold valuations_compatible in *.
                                rewrite Forall_forall in n.
                                ltac1:(contradiction n).
                                clear n. intros x0.
                                rewrite <- elem_of_list_In.
                                rewrite elem_of_elements.
                                rewrite elem_of_intersection.
                                intros [HH1 HH2].
                                unfold Valuation.
                                unfold Valuation_lookup.
                                ltac1:(rewrite elem_of_dom in HH1).
                                ltac1:(rewrite elem_of_dom in HH2).
                                destruct HH1 as [g' Hg'].
                                destruct HH2 as [g'' Hg''].
                                destruct (decide (x = x0)).
                                {
                                    subst.
                                    ltac1:(rewrite lookup_insert in Hg'').
                                    inversion Hg''; subst; clear Hg''.
                                    ltac1:(rewrite Hρ'x in Hg').
                                    inversion Hg'; subst; clear Hg'.
                                    rewrite lookup_insert.
                                    clear -IH1 Hρ''1 Hρ'x.
                                    unfold map_subseteq in *.
                                    unfold map_included in *.
                                    unfold map_relation in *.
                                    unfold option_relation in *.
                                    specialize (IH1 x0).
                                    specialize (Hρ''1 x0).
                                    ltac1:(rewrite Hρ'x in IH1).
                                    ltac1:(rewrite lookup_insert in Hρ''1).
                                    unfold Valuation in *.
                                    unfold Valuation_lookup in *.
                                    destruct (ρ !! x0) eqn:Hρx0.
                                    {
                                        subst.
                                        exact Hρ'x.
                                    }
                                    {
                                        inversion IH1.
                                    }
                                }
                                {
                                    unfold Valuation in *.
                                    rewrite lookup_insert_ne in Hg''.
                                    {
                                        rewrite lookup_empty in Hg''.
                                        inversion Hg''.
                                    }
                                    {
                                        assumption.
                                    }
                                }
                            }
                        }
                    }
                    {
                        exists (<[x := aoo_operand _ _ b]>ρ').
                        cbn.
                        repeat split.
                        {
                            unfold vars_of_valuation.
                            cbn.
                            unfold Valuation.
                            unfold Valuation_lookup.
                            ltac1:(rewrite dom_insert_L).
                            ltac1:(set_solver).
                        }
                        {
                            unfold map_subseteq in *.
                            unfold map_included in *.
                            unfold map_relation in *.
                            unfold option_relation in *.
                            intros i.
                            unfold Valuation.
                            unfold Valuation_lookup.
                            destruct (decide (i = x)).
                            {
                                subst.
                                rewrite lookup_insert.
                                specialize (Hρ''1 x).
                                unfold Valuation in *.
                                rewrite lookup_insert in Hρ''1.
                                apply Hρ''1.
                            }
                            {
                                rewrite lookup_insert_ne.
                                {
                                    clear Hρ''0.
                                    specialize (Hρ''1 x).
                                    ltac1:(rewrite lookup_insert in Hρ''1).
                                    destruct (ρ !! x) eqn:Hρx.
                                    {
                                        ltac1:(rewrite Hρx in Hρ''1).
                                        subst.
                                        unfold Valuation in *.
                                        unfold Valuation_lookup in *.
                                        specialize (IH1 i).
                                        apply IH1.
                                    }
                                    {
                                        ltac1:(rewrite Hρx in Hρ''1).
                                        inversion Hρ''1.
                                    }
                                }
                                {
                                    apply nesym.
                                    assumption.
                                }
                            }
                        }
                        {

                            unfold merge_valuations,is_left.
                            repeat ltac1:(case_match).
                            {
                                apply f_equal.
                                clear H0 H.
                                unfold valuations_compatible in *.
                                clear v.
                                unfold Valuation.
                                ltac1:(
                                    erewrite <- insert_merge_r
                                ).
                                {
                                    rewrite merge_empty_r.
                                    unfold use_left, compose.
                                    cbn.
                                    rewrite omap_Some.
                                    reflexivity.
                                }
                                {
                                    unfold use_left.
                                    unfold Valuation.
                                    unfold Valuation_lookup.
                                    ltac1:(rewrite Hρ'x).
                                    reflexivity.
                                }
                            }
                            {
                                inversion H.
                            }
                            {
                                inversion H.
                            }
                            {
                                clear H0 H.
                                unfold valuations_compatible in *.
                                rewrite Forall_forall in n.
                                ltac1:(contradiction n).
                                clear n. intros x0.
                                rewrite <- elem_of_list_In.
                                rewrite elem_of_elements.
                                rewrite elem_of_intersection.
                                intros [HH1 HH2].
                                unfold Valuation.
                                unfold Valuation_lookup.
                                ltac1:(rewrite elem_of_dom in HH1).
                                ltac1:(rewrite elem_of_dom in HH2).
                                destruct HH1 as [g' Hg'].
                                destruct HH2 as [g'' Hg''].
                                destruct (decide (x = x0)).
                                {
                                    subst.
                                    ltac1:(rewrite lookup_insert in Hg'').
                                    inversion Hg''; subst; clear Hg''.
                                    ltac1:(rewrite Hρ'x in Hg').
                                    inversion Hg'.
                                }
                                {
                                    unfold Valuation in *.
                                    rewrite lookup_insert_ne in Hg''.
                                    {
                                        rewrite lookup_empty in Hg''.
                                        inversion Hg''.
                                    }
                                    {
                                        assumption.
                                    }
                                }
                            }
                        }
                    }
                }
            }
            {
                intros HH.
                rewrite andb_false_r in HH.
                inversion HH.
            }
        }
        {
            rewrite Heqf.
            rewrite Heqg.            
            cbn.
            destruct b''.
            {
                intros HH; inversion HH.
            }
            {
                intros HH.
                cbn.
                destruct b; cbn in *.
                {
                    rewrite andb_false_r in HH.
                    inversion HH.
                }
                {
                    rewrite andb_true_iff in HH.
                    destruct HH as [HH1 HH2].
                    rewrite bool_decide_eq_true in HH2.
                    ltac1:(setoid_rewrite bind_Some).
                    rewrite <- Heqf in HH1.
                    specialize (IHa1 _ _ HH1).
                    destruct IHa1 as [ρ' [Hρ'1 [Hρ'2 Hρ'3]]].
                    destruct (ρ' !! x) eqn:Hρ'x.
                    {
                        assert (g0 = (aoo_app symbol builtin_value a2)).
                        {
                            clear -HH2 Hρ'x Hρ'2.
                            unfold map_subseteq in *.
                            unfold map_included in *.
                            unfold map_relation in *.
                            unfold option_relation in *.
                            specialize (Hρ'2 x).
                            ltac1:(rewrite Hρ'x in Hρ'2).
                            ltac1:(rewrite HH2 in Hρ'2).
                            exact Hρ'2.
                        }
                        subst g0.
                        exists ρ'.
                        repeat split.
                        {
                            rewrite <- Hρ'1.
                            clear -Hρ'x.
                            unfold vars_of_valuation.
                            rewrite set_eq.
                            intros x0.
                            unfold Valuation.
                            rewrite elem_of_dom.
                            rewrite elem_of_union.
                            split; intros H.
                            {
                                destruct H as [v'' H].
                                rewrite elem_of_dom.
                                right.
                                exists v''.
                                apply H.
                            }
                            {
                                destruct H as [H|H].
                                {
                                    rewrite elem_of_singleton in H.
                                    inversion H; subst; clear H.
                                    eexists. apply Hρ'x.
                                }
                                {
                                    rewrite elem_of_dom in H.
                                    exact H.
                                }
                            }
                        }
                        {
                            exact Hρ'2.
                        }
                        {
                            exists ρ'.
                            split.
                            {
                                rewrite <- Heqg.
                                exact Hρ'3.
                            }
                            {
                                unfold merge_valuations.
                                unfold is_left.
                                ltac1:(repeat case_match).
                                {
                                    clear H0 H.
                                    apply f_equal.
                                    apply map_eq.
                                    intros i.
                                    rewrite lookup_merge.
                                    unfold diag_None.
                                    unfold Valuation in *.
                                    unfold Valuation_lookup in *.
                                    destruct (ρ' !! i) eqn:Hρ'i.
                                    {
                                        cbn.
                                        destruct (decide (i = x)).
                                        {
                                            subst i.
                                            rewrite lookup_insert.
                                            reflexivity.
                                        }
                                        {
                                            rewrite lookup_insert_ne.
                                            {
                                                rewrite lookup_empty.
                                                reflexivity.
                                            }
                                            {
                                                apply nesym. assumption.
                                            }
                                        }
                                    }
                                    {
                                                                                cbn.
                                        destruct (decide (i = x)).
                                        {
                                            subst i.
                                            rewrite Hρ'i in Hρ'x.
                                            inversion Hρ'x.
                                        }
                                        {
                                            rewrite lookup_insert_ne.
                                            {
                                                rewrite lookup_empty.
                                                reflexivity.
                                            }
                                            {
                                                apply nesym. assumption.
                                            }
                                        }
                                    }
                                }
                                {
                                    inversion H.
                                }
                                {
                                    inversion H.
                                }
                                {
                                    clear H0 H.
                                    ltac1:(contradiction n).
                                    clear n.
                                    unfold valuations_compatible.
                                    rewrite Forall_forall.
                                    intros x0.
                                    rewrite <- elem_of_list_In.
                                    rewrite elem_of_elements.
                                    rewrite elem_of_intersection.
                                    intros [HE1 HE2].
                                    ltac1:(rewrite elem_of_dom in HE2).
                                    destruct HE2 as [x'' Hx''].
                                    destruct (decide (x0 = x)).
                                    {
                                        subst.
                                        unfold Valuation.
                                        rewrite lookup_insert.
                                        ltac1:(rewrite lookup_insert in Hx'').
                                        ltac1:(rewrite Hρ'x).
                                        reflexivity.
                                    }
                                    {
                                        unfold Valuation.
                                        rewrite lookup_insert_ne.
                                        {
                                            ltac1:(rewrite lookup_insert_ne in Hx'').
                                            {
                                                apply nesym. assumption.
                                            }
                                            {
                                                ltac1:(rewrite lookup_empty in Hx'').
                                                inversion Hx''.
                                            }
                                        }
                                        {
                                            apply nesym. assumption.
                                        }
                                    }
                                }
                            }
                        }
                    }
                    {
                        exists (<[x := aoo_app _ _ a2]>ρ').
                        repeat split.
                        {
                            unfold vars_of_valuation.
                            rewrite set_eq.
                            intros x0.
                            ltac1:(rewrite elem_of_dom).
                            ltac1:(rewrite elem_of_union).
                            ltac1:(rewrite elem_of_singleton).
                            unfold is_Some.
                            split; intros HHH.
                            {
                                destruct HHH as [v Hv].
                                destruct (decide (x0 = x)).
                                {
                                    subst. left. reflexivity.
                                }
                                {
                                    right.
                                    ltac1:(rewrite lookup_insert_ne in Hv).
                                    {
                                        apply nesym. assumption.
                                    }
                                    {
                                        rewrite <- Hρ'1.
                                        unfold vars_of_valuation.
                                        ltac1:(rewrite elem_of_dom).
                                        exists v. exact Hv.
                                    }
                                }
                            }
                            {
                                destruct HHH as [HHH|HHH].
                                {
                                    subst.
                                    eexists.
                                    ltac1:(rewrite lookup_insert).
                                    reflexivity.
                                }
                                {
                                    destruct (decide (x0 = x)).
                                    {
                                        subst.
                                        eexists.
                                        unfold Valuation.
                                        rewrite lookup_insert.
                                        reflexivity.
                                    }
                                    {
                                        rewrite <- Hρ'1 in HHH.
                                        unfold vars_of_valuation in HHH.
                                        ltac1:(rewrite elem_of_dom in HHH).
                                        destruct HHH as [myx Hmyx].
                                        eexists.
                                        unfold Valuation.
                                        rewrite lookup_insert_ne.
                                        {
                                            apply Hmyx.
                                        }
                                        {
                                            apply nesym. assumption.
                                        }
                                    }
                                }
                            }
                        }
                        {
                            unfold map_subseteq in *.
                            unfold map_included in *.
                            unfold map_relation in *.
                            unfold option_relation in *.
                            intros i.
                            destruct (decide (x = i)).
                            {
                                subst.
                                unfold Valuation.
                                rewrite lookup_insert.
                                ltac1:(rewrite HH2).
                                reflexivity.
                            }
                            {
                                unfold Valuation.
                                rewrite lookup_insert_ne.
                                {
                                    apply Hρ'2.
                                }
                                {
                                    assumption.
                                }    
                            }
                        }
                        {
                            rewrite <- Heqg.
                            exists ρ'.
                            split.
                            {
                                apply Hρ'3.
                            }
                            {
                                unfold merge_valuations,is_left.
                                ltac1:(repeat case_match).
                                {
                                    apply f_equal.
                                    clear H0 H.
                                    unfold Valuation.
                                    ltac1:(
                                        erewrite <- insert_merge_r
                                    ).
                                    {
                                        rewrite merge_empty_r.
                                        unfold flip,use_left,compose.
                                        cbn.
                                        rewrite omap_Some.
                                        reflexivity.
                                    }
                                    {
                                        unfold use_left.
                                        ltac1:(rewrite Hρ'x).
                                        reflexivity.
                                    }
                                }
                                {
                                    inversion H.
                                }
                                {
                                    inversion H.
                                }
                                {
                                    clear H0 H.
                                    ltac1:(contradiction n).
                                    clear n.
                                    unfold valuations_compatible.
                                    rewrite Forall_forall.
                                    intros x0.
                                    rewrite <- elem_of_list_In.
                                    rewrite elem_of_elements.
                                    rewrite elem_of_intersection.
                                    unfold Valuation.
                                    do 2 (rewrite elem_of_dom).
                                    intros [HHH1 HHH2].
                                    destruct HHH1 as [v1 Hv1].
                                    destruct HHH2 as [v2 Hv2].
                                    destruct (decide (x = x0)).
                                    {
                                        subst x.
                                        rewrite lookup_insert.
                                        rewrite lookup_insert in Hv2.
                                        inversion Hv2; subst; clear Hv2.
                                        ltac1:(rewrite Hρ'x in Hv1).
                                        inversion Hv1.
                                    }
                                    {
                                        rewrite lookup_insert_ne.
                                        {
                                            rewrite lookup_insert_ne in Hv2.
                                            {
                                                rewrite lookup_empty in Hv2.
                                                inversion Hv2.
                                            }
                                            {
                                                assumption.
                                            }
                                        }
                                        {
                                            assumption.
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            {
                rewrite andb_true_iff.
                intros [H1 H2].
                rewrite <- Heqf in H1.
                rewrite <- Heqf in H2.
                specialize (IHa1 _ _ H1).
                specialize (IHa2 _ _ H2).
                destruct IHa1 as [ρ1 Hρ1].
                destruct IHa2 as [ρ2 Hρ2].
                destruct Hρ1 as [Hρ11 [Hρ12 Hρ13]].
                destruct Hρ2 as [Hρ21 [Hρ22 Hρ23]].
                ltac1:(setoid_rewrite bind_Some).
                ltac1:(setoid_rewrite bind_Some).
                cbn.
                rewrite <- Hρ11.
                rewrite <- Hρ21.
                unfold merge_valuations,is_left.
                exists ((merge use_left ρ1 ρ2)).


                split.
                {
                    unfold vars_of_valuation.
                    rewrite set_eq.
                    intros x.
                    unfold Valuation.
                    rewrite elem_of_dom.
                    rewrite elem_of_union.
                    do 2 (rewrite elem_of_dom).
                    split; intros HH.
                    {
                        destruct HH as [v Hv].
                        rewrite lookup_merge in Hv.
                        unfold diag_None in Hv.
                        unfold Valuation in *.
                        unfold is_Some.
                        destruct (ρ1 !! x) eqn:ρ1x.
                        {
                            left.
                            eexists.
                            reflexivity.
                        }
                        {
                            destruct (ρ2 !! x) eqn:ρ2x.
                            {
                                right.
                                eexists.
                                reflexivity.
                            }
                            {
                                inversion Hv.
                            }
                        }
                    }
                    {
                        rewrite lookup_merge.
                        unfold diag_None.
                        unfold Valuation in *.
                        destruct HH as [HH|HH].
                        {
                            destruct HH as [x' Hx'].
                            rewrite Hx'.
                            unfold use_left,is_Some.
                            cbn. exists x'.
                            destruct (ρ2 !! x); reflexivity.
                        }
                        {
                            destruct HH as [x' Hx'].
                            rewrite Hx'.
                            unfold use_left,is_Some.
                            exists x'. cbn.
                            destruct (ρ1 !! x) eqn:Hρ1x.
                            {
                                clear - Hρ12 Hρ22 Hx' Hρ1x.
                                unfold map_subseteq in *.
                                unfold map_included in *.
                                unfold map_relation in *.
                                unfold option_relation in *.
                                specialize (Hρ12 x).
                                specialize (Hρ22 x).
                                rewrite Hρ1x in Hρ12.
                                rewrite Hx' in Hρ22.
                                destruct (ρ!!x) eqn:Hρx.
                                {
                                    ltac1:(congruence).
                                }
                                {
                                    inversion Hρ12.
                                }
                            }
                            {
                                reflexivity.
                            }
                        }
                    }
                }
                {
                    split.
                    {
                        clear -Hρ12 Hρ22.
                        unfold map_subseteq in *.
                        unfold map_included in *.
                        unfold map_relation in *.
                        unfold option_relation in *.
                        intros i.
                        specialize (Hρ12 i).
                        specialize (Hρ22 i).
                        rewrite lookup_merge.
                        unfold diag_None.
                        unfold use_left.
                        unfold Valuation in *.
                        unfold Valuation_lookup in *.
                        destruct (ρ1 !! i) eqn:Hρ1i;
                            destruct (ρ2 !! i) eqn:Hρ2i;
                            destruct (ρ !! i) eqn:Hρi;
                            try (exact I);
                            try (solve [subst;reflexivity]);
                            try assumption
                        .
                    }
                    {
                        exists ρ1.
                        split>[subst;assumption|].
                        exists ρ2.
                        split>[subst;assumption|].
                        ltac1:(repeat case_match);
                            try reflexivity.
                        {
                            inversion H.
                        }
                        {
                            ltac1:(contradiction n).
                            clear n H0 H.
                            clear - Hρ12 Hρ22.
                            unfold valuations_compatible.
                            rewrite Forall_forall.
                            intros x.
                            rewrite <- elem_of_list_In.
                            rewrite elem_of_elements.
                            rewrite elem_of_intersection.
                            do 2 ltac1:(rewrite elem_of_dom).
                            unfold is_Some.
                            intros [[x1 H1] [x2 H2]].
                            unfold map_subseteq in *.
                            unfold map_included in *.
                            unfold map_relation in *.
                            unfold option_relation in *.
                            specialize (Hρ12 x).
                            specialize (Hρ22 x).
                            rewrite H1 in Hρ12.
                            rewrite H2 in Hρ22.
                            unfold Valuation in *.
                            destruct (ρ !! x) eqn:Hρx.
                            {
                                ltac1:(congruence).
                            }
                            {
                                inversion Hρ12.
                            }
                        }
                    }
                }
            }
        }
    Qed.

    Definition apply_match
        (ρ : Valuation)
        (m : Match)
        : option Valuation
    :=
        t ← ρ !! (m_variable m);
        ρ' ← GroundTerm_try_match_OpenTerm t (m_term m);
        merge_valuations ρ ρ'
    .

    Definition apply_match'
        (oρ : option Valuation)
        (m : Match)
        : option Valuation
    := ρ ← oρ; apply_match ρ m .

    Definition reduce_matches
        (oρ : option Valuation)
        (matches : list Match)
        : option Valuation
    :=
        fold_left apply_match' matches oρ
    .

    Definition valuation_satisfies_all_matches
        (ρ : Valuation) (l : list Match) : Prop
    :=
        ∀ x ot, (mkMatch _ x ot) ∈ l ->
        ∃ t, ρ !! x = Some t /\
        GroundTerm_matches_OpenTerm ρ t ot
    .

    Lemma valuation_satisfies_all_matches_perm
        (l1 l2 : list Match) (ρ : Valuation)
    : l1 ≡ₚ l2 ->
        valuation_satisfies_all_matches ρ l1
        -> valuation_satisfies_all_matches ρ l2
    .
    Proof.
        intros Hp.
        unfold valuation_satisfies_all_matches.
        intros H1 x ot Hin.
        specialize (H1 x ot).
        apply H1.
        rewrite Hp.
        exact Hin.
    Qed.

    Lemma order_enabled_first_nil initial_vars:
        order_enabled_first initial_vars [] = ([],[])
    .
    Proof.
        ltac1:(simp order_enabled_first).
        unfold order_enabled_first_unfold_clause_1.
        simpl.
        reflexivity.
    Qed.


    Definition vars_of_lm
        (lm : list Match)
        : gset variable
    :=
       union_list (vars_of_OpenTerm <$> (m_term <$> lm))
    .

    Inductive nicely_ordered
        : gset variable -> list Match -> Prop
    :=
    | no_empty: forall initial, nicely_ordered initial []
    | no_cons: forall initial x xs,
        (m_variable x) ∈ initial ->
        nicely_ordered (initial ∪ (vars_of_OpenTerm (m_term x))) xs ->
        nicely_ordered
            initial
            (x::xs)
    .

    Lemma nicely_ordered_mono i1 i2 l:
        i1 ⊆ i2 ->
        nicely_ordered i1 l ->
        nicely_ordered i2 l
    .
    Proof.
        intros H1 H2.
        revert i1 i2 H1 H2.
        induction l; intros i1 i2 H1 H2.
        {
            constructor.
        }
        {
            inversion H2; subst; clear H2.
            constructor.
            { ltac1:(set_solver). }
            eapply IHl>[|apply H5].
            ltac1:(set_solver).
        }
    Qed.

    Lemma nicely_ordered_cons initial x l:
        nicely_ordered initial (x::l)
        <-> (
            (m_variable x) ∈ initial /\
            nicely_ordered (initial ∪ (vars_of_OpenTerm (m_term x))) l
        )
    .
    Proof.
        split; intros H.
        {
            inversion H; subst; clear H.
            split.
            {
                clear -H3. ltac1:(set_solver).
            }
            {
                eapply nicely_ordered_mono>[|apply H4].
                clear. ltac1:(set_solver).
            }
        }
        {
            destruct H as [H1 H2].
            apply no_cons; assumption.
        }
    Qed.


    Lemma nicely_ordered_app initial l1 l2:
        nicely_ordered initial (l1 ++ l2)
        <->
        (nicely_ordered initial l1 /\
         nicely_ordered (initial ∪ (vars_of_lm l1)) l2)
    .
    Proof.
        revert l2 initial.
        induction l1; intros l2 initial.
        {
            unfold vars_of_lm.
            do 2 (rewrite fmap_nil).
            rewrite union_list_nil.
            rewrite union_empty_r_L.
            simpl.
            split.
            {
                intros H.
                split.
                { apply no_empty. }
                exact H.
            }
            {
                intros [_ H].
                exact H.
            }
        }
        {
            unfold vars_of_lm.
            do 2 (rewrite fmap_cons).
            simpl.
            do 2 (rewrite nicely_ordered_cons).
            rewrite IHl1.
            clear IHl1 up_dec bp_dec.
            unfold vars_of_lm.
            unfold union_list.
            rewrite foldr_fmap.
            simpl.
            rewrite union_assoc_L.
            ltac1:(naive_solver).
        }
    Qed.

    Lemma enables_match_mono vs1 vs2 m:
        vs1 ⊆ vs2 ->
        enables_match vs1 m ->
        enables_match vs2 m
    .
    Proof.
        unfold enables_match.
        ltac1:(set_solver).
    Qed.

    Lemma nicely_ordered_all_enable_match vs l m:
        nicely_ordered vs l ->
        m ∈ l ->
        ∃ vs', vs ⊆ vs' /\
            enables_match vs' m
    .
    Proof.
        intros Hord Hin.
        apply elem_of_list_split in Hin.
        destruct Hin as [l1 [l2 Hl1l2]].
        subst l.
        rewrite nicely_ordered_app in Hord.
        destruct Hord as [_ Hml2].
        rewrite nicely_ordered_cons in Hml2.
        destruct Hml2 as [Hmin Hl2].
        unfold enables_match.
        eexists.
        split>[|apply Hmin].
        ltac1:(clear; set_solver).
    Qed.

    Lemma nicely_ordered_all_enable_match' vs l i m:
        nicely_ordered vs l ->
        l !! i = Some m ->
        enables_match (vs ∪ vars_of_lm (take i l)) m
    .
    Proof.
        intros Hord Hin.
        assert (Hlt := Hin).
        apply lookup_lt_Some in Hlt.   
        rewrite <- (take_drop (i)) in Hord.
        rewrite <- (take_drop (S i) l) in Hin.
        rewrite nicely_ordered_app in Hord.
        destruct Hord as [_ Hord].
        rewrite lookup_app in Hin.
        rewrite lookup_take in Hin>[|ltac1:(lia)].
        remember (l !! i) as om.
        destruct om.
        {
            inversion Hin; subst; clear Hin.
            symmetry in Heqom.
            apply elem_of_list_split_length in Heqom.
            destruct Heqom as [l1 [l2 [H1 H2]]].
            subst.
            clear Hlt.
            rewrite drop_app_length in Hord.
            rewrite nicely_ordered_cons in Hord.
            destruct Hord as [H1 H2].
            unfold enables_match.
            apply H1.
        }
        {
            ltac1:(exfalso).
            clear -Heqom Hlt.
            symmetry in Heqom.
            apply lookup_ge_None_1 in Heqom.
            ltac1:(lia).
        }
    Qed.

    Lemma nicely_ordered_exists_enables_match vs ms l':
        l' ≡ₚ ms ->
        ms <> [] ->
        nicely_ordered vs l' ->
        (∃ i g vs',
            ms !! i = Some g
            /\ enables_match vs' g
            /\ vs ⊆ vs'
        )
    .
    Proof.
        intros Hperm Hnotnil Hno.
        destruct ms.
        {
            ltac1:(contradiction Hnotnil).
            reflexivity.
        }
        clear Hnotnil.
        apply Permutation_vs_cons_inv in Hperm.
        destruct Hperm as [l1 [l2 Hl1l2]].
        subst l'.
        apply nicely_ordered_all_enable_match with (m := m) in Hno.
        {
            destruct Hno as [vs' [Hsub Hen]].
            exists 0.
            exists m.
            exists vs'.
            cbn.
            split>[reflexivity|].
            split>[exact Hen|].
            apply Hsub.
        }
        {
            clear. ltac1:(set_solver).
        }
    Qed.

    Lemma can_be_ordered_implies_choose_Some
        vs ms ms':
        ms <> [] ->
        ms' ≡ₚ ms ->
        nicely_ordered vs ms' ->
        ∃ mlm,
        choose_first_enabled_match vs ms = Some mlm
    .
    Proof.
        intros Hnotnil Hperm Hordered.
        assert (Hnotnil': ms' <> []).
        {
            clear -Hnotnil Hperm.
            intros HContra.
            apply Hnotnil.
            subst ms'.
            apply Permutation_nil.
            exact Hperm.
        }
        destruct ms'.
        {
            ltac1:(contradiction Hnotnil').
            reflexivity.
        }
        clear Hnotnil' Hnotnil.
        symmetry in Hperm.
        apply Permutation_vs_cons_inv in Hperm.
        destruct Hperm as [l' [l'' Hms]].
        subst ms.
        inversion Hordered; subst; clear Hordered.
        remember (choose_first_enabled_match vs l') as o.
        destruct o as [[[idx m'] lm' ]|].
        {
            exists (idx,m', lm'++m::l'').
            unfold choose_first_enabled_match in Heqo.
            unfold choose_first_enabled_match.
            symmetry in Heqo.
            rewrite bind_Some in Heqo.
            destruct Heqo as [[idx' Midx] [HH1 HH2]].
            inversion HH2; subst; clear HH2.
            rewrite bind_Some.
            exists (idx, m').
            split.
            {
                apply list_find_app_l.
                exact HH1.
            }
            apply f_equal.
            rewrite list_find_Some in HH1.
            destruct HH1 as [Hl'idx HH1].
            rewrite delete_take_drop.
            rewrite delete_take_drop.
            rewrite <- app_assoc.
            rewrite firstn_app.
            apply lookup_lt_Some in Hl'idx as HH2.
            destruct l'.
            { simpl in HH2. ltac1:(lia). }
            simpl.
            ltac1:(f_equal).
            rewrite <- app_assoc.
            apply f_equal.
            simpl in HH2.
            assert (Hexp0: idx - (S (length l')) = 0).
            {
                ltac1:(lia).
            }
            rewrite Hexp0.
            clear Hexp0.
            simpl.
            rewrite drop_app_le.
            {
                reflexivity.
            }
            {
                ltac1:(lia).
            }
        }
        exists (length l', m, l' ++ l'').
        unfold choose_first_enabled_match.
        rewrite bind_Some.
        exists ((length l'), m).
        unfold choose_first_enabled_match in Heqo.
        symmetry in Heqo.
        rewrite bind_None in Heqo.
        destruct Heqo as [Heqo|Heqo].
        {
            rewrite list_find_None in Heqo.
            split.
            {
                rewrite list_find_Some.
                split.
                {
                    rewrite lookup_app_r.
                    {
                        rewrite Nat.sub_diag.
                        simpl.
                        reflexivity.
                    }
                    {
                        ltac1:(lia).
                    }
                }
                {
                    rewrite Forall_forall in Heqo.
                    split.
                    {
                        apply H2.
                    }
                    intros i y HH1 HH2.
                    apply Heqo.
                    rewrite <- elem_of_list_In.
                    rewrite lookup_app_l in HH1>[|apply HH2].
                    rewrite elem_of_list_lookup.
                    exists i.
                    exact HH1.
                }
            }
            {
                rewrite delete_middle.
                reflexivity.
            }
        }
        {
            destruct Heqo as [[i' m'] [HH1 HH2]].
            inversion HH2.
        }
    Qed.

    Lemma order_enabled_first_1_nicely_ordered
        initial l :
        nicely_ordered initial (order_enabled_first initial l).1
    .
    Proof.
        ltac1:(funelim (order_enabled_first initial l)).
        {
            rewrite <- Heqcall.
            clear Heqcall H1.
            repeat ltac1:(case_match).
            simpl. simpl in H0.
            constructor.
            {
                clear -H.
                unfold choose_first_enabled_match in H.
                rewrite bind_Some in H.
                destruct H as [[x m] [H1 H2]].
                inversion H2; subst; clear H2.
                rewrite list_find_Some in H1.
                destruct H1 as [H1 [H2 H3]].
                unfold enables_match in H2.
                apply H2.
            }
            {
                apply H0.
            }
        }
        {
            rewrite <- Heqcall.
            simpl.
            constructor.
        }
    Qed.

    Lemma choose_first_enabled_match_lookup vs l i m rest:
        choose_first_enabled_match vs l = Some (i, m, rest) ->
        l !! i = Some m
    .
    Proof.
        intros H.
        unfold choose_first_enabled_match in H.
        rewrite bind_Some in H.
        destruct H as [[i' m'] [H1 H2]].
        inversion H2; subst; clear H2.
        rewrite list_find_Some in H1.
        apply H1.
    Qed.

    Lemma choose_first_enabled_match_elem_of vs l i m rest:
        choose_first_enabled_match vs l = Some (i, m, rest) ->
        m_variable m ∈ vs
    .
    Proof.
        intros H.
        unfold choose_first_enabled_match in H.
        rewrite bind_Some in H.
        destruct H as [[i' m'] [H1 H2]].
        inversion H2; subst; clear H2.
        rewrite list_find_Some in H1.
        apply H1.
    Qed.

    Lemma choose_first_really_first vs l i m rest:
        choose_first_enabled_match vs l = Some (i, m, rest) ->
        Forall (λ x : Match, ¬ enables_match vs x) (take i l)
    .
    Proof.
        intros H.
        unfold choose_first_enabled_match in H.
        rewrite bind_Some in H.
        destruct H as [[i' m'] [H1 H2]].
        inversion H2; subst; clear H2.
        rewrite list_find_Some in H1.
        destruct H1 as [H1 [H2 H3]].
        rewrite Forall_forall.
        intros x Hx.
        rewrite <- elem_of_list_In in Hx.
        
        assert (Htmp: (i <= length l)).
        {
            apply lookup_lt_Some in H1.
            ltac1:(lia).
        }
        rewrite elem_of_list_lookup in Hx.
        destruct Hx as [i0 Hx].
        apply lookup_lt_Some in Hx as Htmp2.
        rewrite take_length in Htmp2.
        eapply H3 with (j := i0).
        {
            rewrite lookup_take in Hx.
            {
                apply Hx.
            }
            {
                ltac1:(lia).    
            }
        }
        {
            ltac1:(lia).
        }
    Qed.

    Lemma delete_preserves_orderability
        vs l l' i m:
        l ≡ₚ l' ->
        nicely_ordered vs l' ->
        m_variable m ∈ vs ->
        l !! i = Some m ->
        exists l'',
            delete i l ≡ₚ l'' /\
            nicely_ordered vs (m::l'')
    .
    Proof.
        intros Hperm Hno Hmvs Hli.
        apply elem_of_list_split_length in Hli.
        destruct Hli as [l1 [l2 [H1 Hlen]]].
        subst l i.
        rewrite delete_middle.
        symmetry in Hperm.
        apply Permutation_vs_elt_inv in Hperm as Hperm'.
        destruct Hperm' as [l'1 [l'2 H]].
        subst l'.
        rewrite nicely_ordered_app in Hno.
        rewrite nicely_ordered_cons in Hno.
        apply Permutation_app_inv in Hperm.
        ltac1:(setoid_rewrite nicely_ordered_cons).
        exists (l'1 ++ l'2).
        split.
        { symmetry. assumption. }
        split>[assumption|].
        rewrite nicely_ordered_app.
        destruct Hno as [H1 [H2 H3]].
        split.
        {
            eapply nicely_ordered_mono>[|apply H1].
            ltac1:(set_solver).
        }
        {
            eapply nicely_ordered_mono>[|apply H3].
            ltac1:(set_solver).
        }
    Qed.

    Lemma order_enabled_first_2_empty_if_can_be_ordered
        initial l :
        (∃ l', l' ≡ₚ l /\ nicely_ordered initial l') ->
        (order_enabled_first initial l).2 = []
    .
    Proof.
        Search choose_first_enabled_match nicely_ordered.
        intros [l' [Hl'1 Hl'2]].
        ltac1:(funelim (order_enabled_first initial l)).
        {
            rewrite <- Heqcall.
            clear Heqcall.
            repeat ltac1:(case_match).
            simpl. simpl in *.
            clear H1.

            assert(Hperm := choose_first_enabled_match_perm vs ms i m' rest H).
            destruct Hperm as [Hperm Hperm'].
            subst rest.
            assert (Hno := delete_preserves_orderability vs ms l' i m').
            symmetry in Hl'1.
            specialize (Hno Hl'1 Hl'2).
            apply choose_first_enabled_match_elem_of in H as H'.
            apply choose_first_enabled_match_lookup in H as H''.
            specialize (Hno H' H'').
            destruct Hno as [l'' [Hl'' Hnol'']].
            symmetry in Hl''.
            specialize (H0 l'' Hl'').
            inversion Hnol''; subst; clear Hnol''.
            specialize (H0 H6).
            apply H0.
        }
        {
            rewrite <- Heqcall.
            clear Heqcall.
            simpl.
            clear H.
            ltac1:(rename e into Hnone).
            unfold choose_first_enabled_match in Hnone.
            rewrite bind_None in Hnone.
            destruct Hnone as [Hnone|Hnone].
            {
                rewrite list_find_None in Hnone.
                destruct l'.
                {
                    apply Permutation_nil in Hl'1.
                    exact Hl'1.
                }
                {
                    ltac1:(exfalso).
                    inversion Hl'2; subst; clear Hl'2.
                    rewrite Forall_forall in Hnone.
                    unfold enables_match in Hnone.
                    eapply Hnone>[|apply H2].
                    rewrite <- elem_of_list_In.
                    apply elem_of_Permutation.
                    exists l'.
                    symmetry. exact Hl'1.
                }
            }
            {
                destruct Hnone as [[n m] [HH1 HH2]].
                inversion HH2.
            }
        }
    Qed.

    Lemma order_enabled_first_nicely_ordered
        initial l
        :
        (∃ l', l' ≡ₚ l /\ nicely_ordered initial l' ) ->
        nicely_ordered initial ((order_enabled_first initial l).1 ++ (order_enabled_first initial l).2)
    .
    Proof.
        intros [l' Hl'].
        rewrite order_enabled_first_2_empty_if_can_be_ordered.
        {
            rewrite app_nil_r.
            apply order_enabled_first_1_nicely_ordered.
        }
        {
            exists l'.
            apply Hl'.
        }
    Qed.


    Theorem on_a_good_reordering:
        ∀(l0 : list Match) (initial_vars : gset variable),
        (∃ ρ0 : Valuation,
            valuation_satisfies_all_matches ρ0 l0
        ) ->
        ∃ (l : list Match),
            l ≡ₚ l0 /\
            ∀ (ρ : Valuation), initial_vars ⊆ dom ρ ->
            ∃ (ρ' : Valuation),
                reduce_matches (Some ρ) l = Some ρ' /\
                map_subseteq ρ ρ' /\
                valuation_satisfies_all_matches ρ' l0
    .
    Proof.
        intros l0 initial_vars [ρ0 Hρ0].
        exists ((order_enabled_first initial_vars l0).1 ++ (order_enabled_first initial_vars l0).2).
        split.
        {
            apply order_enabled_first_perm.
        }

        intros ρ Hρinit.
        ltac1:(cut(
            forall (ll : list Match),
                nicely_ordered initial_vars ll ->
                l0 ≡ₚ ll ->
                ∃ (ρρ' : Valuation),
                    reduce_matches (Some ρ) ll = Some ρρ' /\
                    map_subseteq ρ ρρ' /\
                    valuation_satisfies_all_matches ρρ' ll
        )).
        {
            intros H.
            specialize (H ((order_enabled_first initial_vars l0).1 ++ (order_enabled_first initial_vars l0).2)).
            ltac1:(ospecialize (H _ _)).
            {
                apply order_enabled_first_nicely_ordered.
                exists ((order_enabled_first initial_vars l0).1 ++ (order_enabled_first initial_vars l0).2).
                split.
                {
                    apply order_enabled_first_perm.
                }
            }
            {

            }
        }
        {
            intros H.
        }


        intros ρ Hinit.
        revert ρ0 Hρ0 ρ Hinit.
        induction l0.
        {
            intros ρ0 Hρ0 ρ Hinit.
            simpl.
            rewrite order_enabled_first_nil.
            simpl.
            exists ρ.
            split.
            {
                reflexivity.
            }
            split.
            {
                apply map_subseteq_po.
            }
            unfold valuation_satisfies_all_matches.
            intros x ot H.
            rewrite elem_of_nil in H.
            inversion H.
        }
        {
            intros ρ0 Hρ0.
            ltac1:(ospecialize (IHl0 ρ0 _)).
            {
                clear -Hρ0.
                unfold valuation_satisfies_all_matches in *.
                intros x ot Hxot.
                ltac1:(ospecialize (Hρ0 x ot _)).
                {
                    clear -Hxot.
                    ltac1:(set_solver).
                }
                apply Hρ0.
            }
        }
    Abort.


    Fixpoint rhs_evaluate_rule
        (ρ : Valuation)
        (r : RewritingRule)
        : option Element :=
    match r with
    | rr_local_rewrite lr =>
        evaluate_rhs_pattern ρ (lr_to lr)
    | rr_builtin b => Some (el_builtin b)
    | rr_sym s => Some (el_appsym (aps_operator s))
    | rr_app r1 r2 =>
        let oe1 := rhs_evaluate_rule ρ r1 in
        let oe2 := rhs_evaluate_rule ρ r2 in
        match oe1,oe2 with
        | Some (el_appsym aps1), Some (el_appsym aps2) =>
            Some (el_appsym (aps_app_aps aps1 aps2))
        | Some (el_appsym aps1), Some (el_builtin b) =>
            Some (el_appsym (aps_app_operand aps1 b))
        | _,_ => None
        end
    | rr_var x => ρ !! x
    | rr_requires r' _ => rhs_evaluate_rule ρ r'
    | rr_requires_match r' _ _ => rhs_evaluate_rule ρ r'
    end
    .


    Lemma rhs_evaluate_rule_correct_1
        (r : RewritingRule)
        (ρ : Valuation)
        (e : Element)
        : 
        rhs_evaluate_rule ρ r = Some e ->
        rr_satisfies LR_Right ρ r e
    .
    Proof.
        {
            revert e. revert ρ.
            induction r; intros ρ e Heval.
            {
                destruct e;
                ltac1:(simp rr_satisfies);
                cbn in Heval;
                destruct lr; cbn in *;
                apply evaluate_rhs_pattern_correct;
                exact Heval.
            }
            all: cbn in Heval; ltac1:(simplify_eq /=); auto with nocore.
            all: ltac1:(simp rr_satisfies); try reflexivity.
            all: (repeat (ltac1:(case_match))); ltac1:(simplify_eq /=).
            all: ltac1:(simp rr_satisfies); try ltac1:(naive_solver).
            {
                unfold rr_satisfies_unfold_clause_8.
                destruct (ρ !! v) eqn:Hv; ltac1:(naive_solver).
            }
        }
    Qed.

    Lemma rhs_evaluate_rule_correct_2
        (r : RewritingRule)
        (ρ : Valuation)
        (e : Element)
        : 
            rr_satisfies LR_Right ρ r e ->
            rhs_evaluate_rule ρ r = Some e
    .
    Proof.
        intros Hsatr.
        ltac1:(funelim (rr_satisfies LR_Right ρ r e));
            cbn.
        {
            apply evaluate_rhs_pattern_correct.
            assumption.
        }
        all: ltac1:(simp rr_satisfies in Hsatr).
        all: ltac1:(simplify_eq /=).
        all: try reflexivity.
        all: try ltac1:(contradiction).
        {
            erewrite H by ltac1:(naive_solver);
            erewrite H0 by ltac1:(naive_solver);
            reflexivity.
        }
        {
            erewrite H by ltac1:(naive_solver);
            erewrite H0 by ltac1:(naive_solver);
            reflexivity.
        }
        {
            ltac1:(simp rr_satisfies in Heqcall).
            apply H.
            apply Hsatr.
        }
        {
            apply H.
            rewrite Heq in Hsatr.
            unfold rr_satisfies_unfold_clause_8 in Hsatr.
            apply Hsatr.
        }{
            apply H.
            rewrite Heq in Hsatr.
            unfold rr_satisfies_unfold_clause_8 in Hsatr.
            apply Hsatr.
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

    Lemma weakly_well_defined_baked_in ρ r e:
        rr_satisfies LR_Left ρ r e ->
        exists e', rr_satisfies LR_Right ρ r e'
    .
    Proof.
        intros H.
        ltac1:(funelim (rr_satisfies LR_Left ρ r e));
            ltac1:(simp rr_satisfies in H).
        {
            
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
                        apply rhs_evaluate_rule_correct_1 in Heval.
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
            intros e Hnotstuck.
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
                    apply evaluate_rhs_rule_correct. in Heval.
                }
            }
        }
    Qed.




End with_decidable_signature.
