
From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    flattened
    (*flatten*)
    basic_matching
    try_match
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.




(*
Definition GroundTerm_try_match_OpenTerm
    {Σ : Signature}
    :
    GroundTerm -> OpenTerm -> option Valuation :=
    ApppliedOperatorOr'_try_match_AppliedOperatorOr'
        builtin_value
        BuiltinOrVar
.
*)
    
Definition evaluate_match
    {Σ : Signature}
    (ρ : Valuation)
    (m : Match)
    : bool :=
match m with
| mkMatch _ x φ =>
    match ρ !! x with
    | None => false
    | Some g => matchesb ρ g φ
    end
end.

Definition evaluate_sc
    `{CΣ : ComputableSignature}
    (ρ : Valuation)
    (sc : SideCondition)
    : bool :=
match sc with
| sc_constraint c =>
    matchesb ρ () c
| sc_match m =>
    evaluate_match ρ m
end.


Definition evaluate_rhs_pattern
    {Σ : Signature}
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
    {Σ : Signature}
    {CΣ : ComputableSignature}
    (r : FlattenedRewritingRule)
    (g : GroundTerm)
    : option GroundTerm
:=
    ρ ← try_match g (fr_from r);
    if (forallb (evaluate_sc ρ) (fr_scs r)) then
        evaluate_rhs_pattern ρ (fr_to r)
    else None
.

(* TODO: matches for expressions *)
Search Satisfies Expression.

Set Typeclasses Debug.
Lemma evaluate_rhs_pattern_correct
    {Σ : Signature}
    {CΣ : ComputableSignature}
    (φ : RhsPattern)
    (ρ : Valuation)
    (g : GroundTerm)
    :
    evaluate_rhs_pattern ρ φ = Some g <->
    matchesb ρ g φ = true
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


    #[export]
    Instance Valuation_lookup : Lookup variable GroundTerm Valuation.
    Proof.
        apply gmap_lookup.
    Defined.
    
    

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
