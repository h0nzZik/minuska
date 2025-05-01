From Minuska Require Import
    prelude
    spec
    basic_properties
.


From Coq Require Import Logic.PropExtensionality.

Lemma vars_of_to_l2r_of_tob
    {Σ : StaticModel}
    (r : TermOver builtin_value)
    :
    vars_of_to_l2r (TermOverBuiltin_to_TermOverBoV r) = []
.
Proof.
    unfold TermOverBuiltin_to_TermOverBoV.
    unfold TermOver_map.
    induction r; simpl.
    { reflexivity. }
    {
        revert H.
        induction l; intros H; simpl.
        { reflexivity. }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            rewrite IHl.
            unfold TermOverBuiltin_to_TermOverBoV  in *.
            rewrite H1.
            reflexivity.
        }
    }
Qed.


Lemma Expression2_evaluate_extensive_Some
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ1 ρ2 : Valuation2)
    (t : Expression2)
    (nv : NondetValue)
    (t' : TermOver builtin_value)
    :
    ρ1 ⊆ ρ2 ->
    Expression2_evaluate program ρ1 t nv = Some t' ->
    Expression2_evaluate program ρ2 t nv = Some t'.
Proof.
    intros Hρ1ρ2.
    revert t'.
    induction t; simpl; intros t'.
    { ltac1:(tauto). }
    {
        unfold vars_of in Hρ1ρ2.
        simpl in Hρ1ρ2.
        intros H.
        destruct (ρ1 !! x) eqn:Heq1, (ρ2 !! x) eqn:Heq2.
        {
            rewrite <- H.
            ltac1:(simplify_eq/=).
            f_equal.
            apply (lookup_weaken ρ1 ρ2 x) in Heq1.
            unfold Valuation2 in *.
            ltac1:(simplify_eq/=; congruence).
            { assumption. }
        }
        {
            ltac1:(exfalso).
            apply (lookup_weaken ρ1 ρ2 x) in Heq1.
            unfold Valuation2 in *.
            ltac1:(simplify_eq/=; congruence).
            { assumption. }
        }
        {
            inversion H.
        }
        {
            inversion H.
        }
    }
    {
        intros HH.
        rewrite bind_Some in HH.
        rewrite bind_Some.
        destruct HH as [x [H1x H2x]].
        (* injection H2x as H2x. *)
        apply list_collect_inv in H1x as H3x.
        assert (HSome : Forall isSome ((fun e => Expression2_evaluate program ρ2 e nv) <$> l)).
        {
            rewrite Forall_forall.
            rewrite Forall_forall in H3x.
            rewrite Forall_forall in H.
            intros ox Hox.
            apply H3x.
            rewrite elem_of_list_fmap.
            rewrite elem_of_list_fmap in Hox.
            destruct Hox as [e [H1e H2e]].
            subst.
            exists e.
            split; try assumption.
            destruct (Expression2_evaluate program ρ1 e) eqn:Heq.
            {
                ltac1:(naive_solver).
            }
            {
                clear H.
                specialize (H3x None).
                ltac1:(ospecialize (H3x _)).
                {
                    rewrite elem_of_list_fmap.
                    exists e. ltac1:(naive_solver).
                }
                inversion H3x.
            }
        }
        apply list_collect_Forall in HSome.
        destruct HSome as [l_out [H1l_out H2l_out]].
        exists l_out.
        split>[exact H1l_out|].
        (* apply f_equal. *)
        rewrite <- H2x. clear H2x.
        (* apply functional_extensionality. *)
        (* intros nv. *)
        assert (H0: Some l_out = Some x).
        {
            rewrite <- H1x.
            rewrite <- H1l_out.
            apply f_equal.
            clear - H H3x gt.
            revert H H3x.
            induction l; intros H H3x.
            {
                simpl. reflexivity.
            }
            {
                rewrite fmap_cons.
                rewrite fmap_cons.
                rewrite fmap_cons in H3x.
                rewrite Forall_cons in H3x.
                destruct H3x as [HH1 HH2].
                rewrite Forall_cons in H.
                destruct H as [H1 H2].
                specialize (IHl H2).
                f_equal.
                {
                    
                    unfold isSome in HH1.
                    ltac1:(case_match).
                    {
                        ltac1:(specialize (H1 t erefl)).
                        exact H1.
                    }
                    {
                        inversion HH1.
                    }
                }
                {
                    apply IHl.
                    apply HH2.
                }
            }
        }
        inversion H0; subst; clear H0.
        reflexivity.
    }
    {
        intros HH.
        rewrite bind_Some in HH.
        rewrite bind_Some.
        destruct HH as [x [H1x H2x]].
        injection H2x as H2x.
        apply list_collect_inv in H1x as H3x.
        assert (HSome : Forall isSome ((fun e => Expression2_evaluate program ρ2 e nv) <$> l)).
        {
            rewrite Forall_forall.
            rewrite Forall_forall in H3x.
            rewrite Forall_forall in H.
            intros ox Hox.
            apply H3x.
            rewrite elem_of_list_fmap.
            rewrite elem_of_list_fmap in Hox.
            destruct Hox as [e [H1e H2e]].
            subst.
            exists e.
            split; try assumption.
            destruct (Expression2_evaluate program ρ1 e) eqn:Heq.
            {
                ltac1:(naive_solver).
            }
            {
                clear H.
                specialize (H3x None).
                ltac1:(ospecialize (H3x _)).
                {
                    rewrite elem_of_list_fmap.
                    exists e. ltac1:(naive_solver).
                }
                inversion H3x.
            }
        }
        apply list_collect_Forall in HSome.
        destruct HSome as [l_out [H1l_out H2l_out]].
        exists l_out.
        split>[exact H1l_out|].
        apply f_equal.
        rewrite <- H2x. clear H2x.
        (* apply functional_extensionality. *)
        (* intros nv. *)
        assert (H0: Some l_out = Some x).
        {
            rewrite <- H1x.
            rewrite <- H1l_out.
            apply f_equal.
            clear - H H3x gt.
            revert H H3x.
            induction l; intros H H3x.
            {
                simpl. reflexivity.
            }
            {
                rewrite fmap_cons.
                rewrite fmap_cons.
                rewrite fmap_cons in H3x.
                rewrite Forall_cons in H3x.
                destruct H3x as [HH1 HH2].
                rewrite Forall_cons in H.
                destruct H as [H1 H2].
                specialize (IHl H2).
                f_equal.
                {
                    
                    unfold isSome in HH1.
                    ltac1:(case_match).
                    {
                        ltac1:(specialize (H1 t erefl)).
                        exact H1.
                    }
                    {
                        inversion HH1.
                    }
                }
                {
                    apply IHl.
                    apply HH2.
                }
            }
        }
        inversion H0; subst; clear H0.
        reflexivity.
    }
Qed.

Lemma Expression2_evaluate_total_1
    {Σ : StaticModel}
    (program : ProgramT)
    (e : Expression2)
    (ρ : Valuation2)
    (nv : NondetValue)
    (g : TermOver builtin_value)
:
    Expression2_evaluate program ρ e nv = Some g ->
    ( vars_of e ⊆ vars_of ρ )
.
Proof.
    revert g.
    induction e; intros b Hb; cbn.
    {
        apply empty_subseteq.
    }
    {
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        unfold vars_of in Hx0; simpl in Hx0.
        rewrite elem_of_singleton in Hx0.
        subst x0.
        ltac1:(rewrite elem_of_dom).
        unfold is_Some.
        simpl in Hb.
        ltac1:(case_match;simplify_eq/=).
        exists b. assumption.
    }
    {
        simpl in Hb.
        rewrite bind_Some in Hb.
        destruct Hb as [x [H1x H2x]].
        (* injection H2x as H2x. *)
        unfold vars_of; simpl.
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        rewrite elem_of_union_list in Hx0.
        destruct Hx0 as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [e [H1e H2e]].
        subst X.
        rewrite Forall_forall in H.
        apply list_collect_inv in H1x as H1x'.
        unfold isSome in H1x'.
        rewrite Forall_fmap in H1x'.
        rewrite Forall_forall in H1x'.
        specialize (H1x' e H2e).
        simpl in H1x'.
        ltac1:(case_match).
        {
            clear H1x'.
            eapply (H _ H2e); clear H.
            { apply H0. }
            {
                exact H2X.
            }
        }
        {
            inversion H1x'.
        }
    }
    {
        simpl in Hb.
        rewrite bind_Some in Hb.
        destruct Hb as [x [H1x H2x]].
        injection H2x as H2x.
        unfold vars_of; simpl.
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        rewrite elem_of_union_list in Hx0.
        destruct Hx0 as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [e [H1e H2e]].
        subst X.
        rewrite Forall_forall in H.
        apply list_collect_inv in H1x as H1x'.
        unfold isSome in H1x'.
        rewrite Forall_fmap in H1x'.
        rewrite Forall_forall in H1x'.
        specialize (H1x' e H2e).
        simpl in H1x'.
        ltac1:(case_match).
        {
            clear H1x'.
            eapply (H _ H2e); clear H.
            { apply H0. }
            {
                exact H2X.
            }
        }
        {
            inversion H1x'.
        }
    }
Qed.

Lemma Expression2Term_matches_enough
    {Σ : StaticModel}
    (program : ProgramT)
    (t : TermOver Expression2)
    (ρ : Valuation2)
    (g : TermOver builtin_value)
    (nv : NondetValue)
:
    satisfies ρ (program,(nv,g)) t ->
    vars_of t ⊆ vars_of ρ
.
Proof.
    unfold satisfies; simpl.

    revert ρ g.
    induction t; intros ρ g HH; destruct g; simpl in *;
        ltac1:(simp sat2E in HH).
    {
        ltac1:(case_match;[|contradiction]).
        apply Expression2_evaluate_total_1 in H.
        unfold vars_of; simpl.
        exact H.
    }
    {
        ltac1:(case_match;[|contradiction]).
        apply Expression2_evaluate_total_1 in H.
        unfold vars_of; simpl.
        exact H.
    }
    {
        inversion HH.
    }
    {
        destruct HH as [Hs0s [Hl0l HH]].
        subst s0.
        rewrite Forall_forall in H.
        unfold Valuation2 in *.
        unfold TermOver in *.
        rewrite vars_of_t_term_e.
        rewrite elem_of_subseteq.
        intros x Hx.
        rewrite elem_of_union_list in Hx.
        destruct Hx as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [t [HX Ht]].
        subst X.
        specialize (H _ Ht).
        rewrite elem_of_list_lookup in Ht.
        destruct Ht as [i Hi].
        specialize (HH i).
        remember (l0 !! i) as Hl0i.
        destruct Hl0i.
        {
            specialize (HH t0 t ltac:(assumption) ltac:(reflexivity)).
            specialize (H _ _ HH).
            clear -H2X H.
            ltac1:(set_solver).
        }
        {
            symmetry in HeqHl0i.
            rewrite lookup_ge_None in HeqHl0i.
            apply lookup_lt_Some in Hi.
            unfold TermOver in *.
            ltac1:(lia).
        }
    }
Qed.


Lemma list_collect_Expression2_evaluate_extensive_Some
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ1 ρ2 : Valuation2)
    (l : list Expression2)
    (nv : NondetValue)
    (l' : list (TermOver builtin_value))
    :
    ρ1 ⊆ ρ2 ->
    list_collect ((fun t => Expression2_evaluate program ρ1 t nv) <$> l) = Some l' ->
    list_collect ((fun t => Expression2_evaluate program ρ2 t nv) <$> l) = Some l'.
Proof.
    revert l'.
    induction l; intros l' Hrhos Hlc.
    {
        simpl in *. exact Hlc.
    }
    {
        simpl in *.
        rewrite bind_Some in Hlc.
        rewrite bind_Some.
        destruct Hlc as [t [H1t H2t]].
        exists t.
        split.
        {
            eapply Expression2_evaluate_extensive_Some>[|apply H1t].
            apply Hrhos.
        }
        {
            rewrite bind_Some in H2t.
            rewrite bind_Some.
            destruct H2t as [l'' [H1l'' H2l'']].
            exists l''.
            split>[|exact H2l''].
            apply IHl.
            apply Hrhos.
            apply H1l''.
        }
    }
Qed.

Lemma Expression2_evaluate_None_relative
    {Σ : StaticModel}
    (program : ProgramT)
    (e : Expression2)
    (ρ1 ρ2 : Valuation2)
    (nv : NondetValue)
    :
    vars_of e ⊆ vars_of ρ1 ->
    ρ1 ⊆ ρ2 ->
    Expression2_evaluate program ρ1 e nv = None ->
    Expression2_evaluate program ρ2 e nv = None
.
Proof.
    induction e; intros H1 H2 H3.
    {
        simpl in *.
        exact H3.
    }
    {
        simpl in *.
        destruct (ρ1 !! x) eqn:Heq1,
            (ρ2 !! x) eqn:Heq2.
        {
            inversion H3.
        }
        {
            reflexivity.
        }
        {
            ltac1:(exfalso).
            unfold vars_of in H1; simpl in H1.
            rewrite singleton_subseteq_l in H1.
            unfold Valuation2 in *.
            rewrite <- not_elem_of_dom in Heq1.
            apply Heq1. apply H1.
        }
        {
            reflexivity.
        }
    }
    {
        simpl in *.
        unfold vars_of in H1; simpl in H1.
        rewrite bind_None.
        rewrite bind_None in H3.
        destruct H3 as [H3|H3].
        {
            left.
            apply list_collect_Exists_1 in H3.
            apply list_collect_Exists.
            rewrite Exists_exists.
            rewrite Exists_exists in H3.
            destruct H3 as [x [H1x H2x]].
            rewrite Forall_forall in H.
            rewrite elem_of_list_fmap in H1x.
            destruct H1x as [y [H1y H2y]].
            subst x.
            setoid_rewrite elem_of_list_fmap.
            exists None.
            simpl. split.
            {
                exists y.
                split>[|exact H2y].
                symmetry.
                apply H.
                { apply H2y. }
                {
                    rewrite elem_of_list_lookup in H2y.
                    destruct H2y as [i Hi].
                    apply take_drop_middle in Hi.
                    rewrite <- Hi in H1.
                    rewrite fmap_app in H1.
                    rewrite fmap_cons in H1.
                    rewrite union_list_app in H1.
                    rewrite union_list_cons in H1.
                    ltac1:(set_solver).
                }
                {
                    apply H2.
                }
                {
                    simpl in H2x.
                    unfold isSome in H2x.
                    ltac1:(case_match).
                    ltac1:(exfalso).
                    apply H2x.
                    reflexivity.
                    reflexivity.
                }
            }
            {
                intros HContra. inversion HContra.
            }
        }
        {
            right.
            destruct H3 as [result [H1result H2result]].
            exists result.
            split>[|apply H2result].
            eapply list_collect_Expression2_evaluate_extensive_Some.
            { apply H2. }
            { apply H1result. }
        }
    }
    {
        simpl in *.
        unfold vars_of in H1; simpl in H1.
        rewrite bind_None.
        rewrite bind_None in H3.
        destruct H3 as [H3|H3].
        {
            left.
            apply list_collect_Exists_1 in H3.
            apply list_collect_Exists.
            rewrite Exists_exists.
            rewrite Exists_exists in H3.
            destruct H3 as [x [H1x H2x]].
            rewrite Forall_forall in H.
            rewrite elem_of_list_fmap in H1x.
            destruct H1x as [y [H1y H2y]].
            subst x.
            setoid_rewrite elem_of_list_fmap.
            exists None.
            simpl. split.
            {
                exists y.
                split>[|exact H2y].
                symmetry.
                apply H.
                { apply H2y. }
                {
                    rewrite elem_of_list_lookup in H2y.
                    destruct H2y as [i Hi].
                    apply take_drop_middle in Hi.
                    rewrite <- Hi in H1.
                    rewrite fmap_app in H1.
                    rewrite fmap_cons in H1.
                    rewrite union_list_app in H1.
                    rewrite union_list_cons in H1.
                    ltac1:(set_solver).
                }
                {
                    apply H2.
                }
                {
                    simpl in H2x.
                    unfold isSome in H2x.
                    ltac1:(case_match).
                    ltac1:(exfalso).
                    apply H2x.
                    reflexivity.
                    reflexivity.
                }
            }
            {
                intros HContra. inversion HContra.
            }
        }
        {
            right.
            destruct H3 as [result [H1result H2result]].
            exists result.
            inversion H2result.
        }
    }
Qed.


Lemma TermOverExpression2_satisfies_extensive
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ1 ρ2 : Valuation2)
    (t : TermOver Expression2)
    (gt : TermOver builtin_value)
    (nv : NondetValue)
    :
    ρ1 ⊆ ρ2 ->
    satisfies ρ1 (program, (nv,gt)) t ->
    satisfies ρ2 (program, (nv,gt)) t
.
Proof.
    revert gt ρ1 ρ2.
    unfold TermOver in *.
    unfold Valuation2 in *.
    ltac1:(induction t using TermOver_rect; intros gt ρ1 ρ2 Hρ1ρ2).
    {
        unfold satisfies; simpl.
        destruct gt; ltac1:(simp sat2E).
        {
            intros HH.
            ltac1:(case_match;[|contradiction]).
            eapply Expression2_evaluate_extensive_Some in H.
            rewrite H.
            exact HH.
            exact Hρ1ρ2.
        }
        {
            intros HH.
            ltac1:(case_match;[|contradiction]).
            eapply Expression2_evaluate_extensive_Some in H.
            rewrite H.
            exact HH.
            exact Hρ1ρ2.
        }
    }
    {
        unfold satisfies; simpl.
        destruct gt; ltac1:(simp sat2E).
        intros [HH1 [HH2 HH3]].
        (repeat split); try assumption.
        intros i t' φ' H1 H2.
        specialize (HH3 i t' φ' H1 H2).
        eapply X.
        {
            rewrite elem_of_list_lookup. exists i. apply H1.
        }
        { apply Hρ1ρ2. }
        apply HH3.
    }
Qed.

Lemma TermOverExpression2_satisfies_injective
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (t : TermOver Expression2)
    (nv : NondetValue)
    (g1 g2 : TermOver builtin_value)
:
    satisfies ρ (program, (nv,g1)) t ->
    satisfies ρ (program, (nv,g2)) t ->
    g1 = g2
.
Proof.
    revert g1 g2.
    induction t; intros g1 g2 Hg1 Hg2; simpl in *.
    {
        unfold satisfies in *; simpl in *.
        ltac1:(simp sat2E in Hg1).
        ltac1:(simp sat2E in Hg2).
        ltac1:(repeat case_match; try contradiction).
        ltac1:(simplify_eq/=).
        reflexivity.
    }
    {
        unfold satisfies in *; simpl in *.
        rewrite Forall_forall in H.
        destruct g1,g2;
            ltac1:(simp sat2E in Hg1);
            ltac1:(simp sat2E in Hg2).
        { inversion Hg1. }
        { inversion Hg1. }
        { inversion Hg2. }
        ltac1:(destruct_and!; simplify_eq/=; f_equal).
        apply list_eq.
        intros i.
        destruct (l0!!i) eqn:Heql0i,(l1!!i) eqn:Heql1i, (l!!i) eqn:Heqli.
        {
            specialize (H3 i t0 t1 Heqli Heql1i).
            specialize (H6 i t t1 Heqli Heql0i).
            apply f_equal.
            eapply H.
            {
                rewrite elem_of_list_lookup. exists i. exact Heqli.
            }
            { assumption. }
            { assumption. }
        }
        {
            apply lookup_lt_Some in Heql0i.
            apply lookup_lt_Some in Heql1i.
            apply lookup_ge_None in Heqli.
            ltac1:(lia).
        }
        {
            apply lookup_lt_Some in Heql0i.
            apply lookup_lt_Some in Heqli.
            apply lookup_ge_None in Heql1i.
            ltac1:(lia).
        }
        {
            apply lookup_lt_Some in Heql0i.
            apply lookup_ge_None in Heql1i.
            apply lookup_ge_None in Heqli.
            ltac1:(lia).
        }
        {
            apply lookup_lt_Some in Heql1i.
            apply lookup_ge_None in Heql0i.
            ltac1:(lia).
        }
        {
            apply lookup_ge_None in Heql0i.
            apply lookup_lt_Some in Heql1i.
            apply lookup_ge_None in Heqli.
            ltac1:(lia).
        }
        {
            reflexivity.
        }
        {
            reflexivity.
        }
    }
Qed.

Lemma Expression2_evalute_strip
    {Σ : StaticModel}
    (program : ProgramT)
    (e : Expression2)
    (nv : NondetValue)
    (g : TermOver builtin_value)
    (ρ : Valuation2)
:
    Expression2_evaluate program ρ e nv = Some g ->
    Expression2_evaluate program (filter (fun kv => kv.1 ∈ vars_of e) ρ) e nv = Some g
.
Proof.
    revert g.
    induction e; intros g H1; simpl in *.
    { assumption. }
    {
        unfold Valuation2 in *.
        ltac1:(repeat case_match).
        rewrite map_lookup_filter_Some in H0.
        {
            simpl in *.
            destruct H0 as [H2 H3].
            apply (inj Some) in H1.
            subst g.
            rewrite H2 in H.
            exact H.
        }
        {
            rewrite map_lookup_filter_None in H0.
            destruct H0 as [H0|H0].
            {
                ltac1:(simplify_eq/=).
            }
            {
                simpl in *.
                ltac1:(simplify_option_eq).
                specialize (H0 _ H).
                unfold vars_of in H0; simpl in H0.
                rewrite elem_of_singleton in H0.
                ltac1:(contradiction H0).
                reflexivity.
            }
        }
        {
            inversion H1.
        }
        {
            inversion H1.
        }
    }
    {
        rewrite bind_Some in H1.
        rewrite bind_Some.
        destruct H1 as [l' [H1l' H2l']].
        exists l'.
        split>[|apply H2l'].
        clear H2l' g.
        revert l' H1l'.
        induction l; intros l' HH.
        {
            simpl in *.
            apply HH.
        }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2).
            clear H2.
            simpl in *.
            rewrite bind_Some in HH.
            destruct HH as [t' [H1t' H2t']].
            rewrite bind_Some.
            specialize (H1 _ H1t').
            (* rewrite bind_Some. *)
            exists t'.
            split.
            {
                unfold vars_of; simpl.
                eapply Expression2_evaluate_extensive_Some>[|apply H1].
                unfold Valuation2 in *.
                apply map_filter_subseteq_ext.
                intros i x Hix.
                simpl.
                clear.
                ltac1:(set_solver).
            }
            {
                rewrite bind_Some in H2t'.
                rewrite bind_Some.
                destruct H2t' as [l'' [H1l'' H2l'']].
                exists l''.
                split>[|apply H2l''].
                unfold vars_of; simpl.
                specialize (IHl _ H1l'').
                eapply list_collect_Expression2_evaluate_extensive_Some>[|apply IHl].
                unfold Valuation2 in *.
                apply map_filter_subseteq_ext.
                intros i x Hix.
                simpl.
                clear.
                ltac1:(set_solver).
            }
        }
    }
    {
        rewrite bind_Some in H1.
        rewrite bind_Some.
        destruct H1 as [l' [H1l' H2l']].
        exists l'.
        split>[|apply H2l'].
        clear H2l' g.
        revert l' H1l'.
        induction l; intros l' HH.
        {
            simpl in *.
            apply HH.
        }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2).
            clear H2.
            simpl in *.
            rewrite bind_Some in HH.
            destruct HH as [t' [H1t' H2t']].
            rewrite bind_Some.
            specialize (H1 _ H1t').
            (* rewrite bind_Some. *)
            exists t'.
            split.
            {
                unfold vars_of; simpl.
                eapply Expression2_evaluate_extensive_Some>[|apply H1].
                unfold Valuation2 in *.
                apply map_filter_subseteq_ext.
                intros i x Hix.
                simpl.
                clear.
                ltac1:(set_solver).
            }
            {
                rewrite bind_Some in H2t'.
                rewrite bind_Some.
                destruct H2t' as [l'' [H1l'' H2l'']].
                exists l''.
                split>[|apply H2l''].
                unfold vars_of; simpl.
                specialize (IHl _ H1l'').
                eapply list_collect_Expression2_evaluate_extensive_Some>[|apply IHl].
                unfold Valuation2 in *.
                apply map_filter_subseteq_ext.
                intros i x Hix.
                simpl.
                clear.
                ltac1:(set_solver).
            }
        }
    }
Qed.


Lemma vars_of_t_over_expr
    {Σ : StaticModel}
    (e : Expression2)
    :
    (vars_of ((t_over e):(TermOver Expression2))) = vars_of e
.
Proof.
    reflexivity.
Qed.

Lemma TermOverExpression2_satisfies_strip
    {Σ : StaticModel}
    (program : ProgramT)
    (t : TermOver Expression2)
    (g : TermOver builtin_value)
    (ρ : Valuation2)
    (nv : NondetValue)
:
    satisfies ρ (program, (nv,g)) t ->
    satisfies (filter (fun kv => kv.1 ∈ vars_of t) ρ) (program, (nv,g)) t
.
Proof.
    revert ρ g.
    ltac1:(induction t using TermOver_rect; intros ρ g HH).
    {
        unfold satisfies in *; simpl in *.
        ltac1:(simp sat2E in HH).
        ltac1:(simp sat2E).
        ltac1:(repeat case_match; try contradiction).
        {
            apply Expression2_evalute_strip in H.
            rewrite vars_of_t_over_expr in H0.
            ltac1:(simplify_eq/=).
            reflexivity.
        }
        {
            apply Expression2_evalute_strip in H.
            rewrite vars_of_t_over_expr in H0.
            ltac1:(simplify_eq/=).
        }
    }
    {
        unfold satisfies in *; simpl in *.
        destruct g;
            ltac1:(simp sat2E in HH).
        { destruct HH. }
        ltac1:(simp sat2E).
        ltac1:(destruct_and!; (repeat split); simplify_eq/=; try congruence).
        intros.
        eapply TermOverExpression2_satisfies_extensive>[|eapply X].
        {
            unfold TermOver, Valuation2 in *.
            ltac1:(rewrite map_subseteq_spec).
            intros i0 x Hx.
            rewrite map_lookup_filter in Hx.
            rewrite map_lookup_filter.
            ltac1:(simplify_option_eq).
            reflexivity.
            ltac1:(exfalso).
            rewrite vars_of_t_term_e in H3.
            rewrite elem_of_union_list in H3.
            apply H3. clear H3.
            exists (vars_of φ').
            split>[|assumption].
            rewrite elem_of_list_fmap.
            exists φ'.
            split>[reflexivity|].
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        {
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        {
            eapply H2.
            apply pf1.
            apply pf2.
        }
    }
Qed.

Lemma TermOverBoV_satisfies_extensive
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (t : TermOver BuiltinOrVar)
    (gt : TermOver builtin_value)
    :
    ρ1 ⊆ ρ2 ->
    satisfies ρ1 gt t ->
    satisfies ρ2 gt t
.
Proof.
    revert gt ρ1 ρ2.
    unfold TermOver in *.
    unfold Valuation2 in *.
    ltac1:(induction t using TermOver_rect; intros gt ρ1 ρ2 Hρ1ρ2).
    {
        unfold satisfies; simpl.
        destruct gt,a ; ltac1:(simp sat2B); simpl.
        {
            intros HH.
            unfold TermOver in *.
            ltac1:(rewrite map_subseteq_spec in Hρ1ρ2).
            ltac1:(naive_solver).
        }
        {
            intros HH.
            ltac1:(rewrite map_subseteq_spec in Hρ1ρ2).
            ltac1:(naive_solver).
        }
    }
    {
        unfold satisfies; simpl.
        destruct gt; ltac1:(simp sat2B).
        intros [HH1 [HH2 HH3]].
        (repeat split); try assumption.
        intros i t' φ' H1 H2.
        specialize (HH3 i t' φ' H1 H2).
        eapply X.
        {
            rewrite elem_of_list_lookup. exists i. apply H1.
        }
        { apply Hρ1ρ2. }
        apply HH3.
    }
Qed.


Lemma TermOverBoV_satisfies_strip
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    (g : TermOver builtin_value)
    (ρ : Valuation2)
:
    satisfies ρ g t ->
    satisfies (filter (fun kv => kv.1 ∈ vars_of t) ρ) g t
.
Proof.
    revert ρ g.
    ltac1:(induction t using TermOver_rect; intros ρ g HH).
    {
        unfold satisfies in *; simpl in *.
        ltac1:(simp sat2B in HH).
        ltac1:(simp sat2B).
        unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar in *.
        ltac1:(repeat case_match; try congruence).
        unfold Valuation2 in *.
        rewrite map_lookup_filter.
        rewrite HH.
        simpl.
        ltac1:(simplify_option_eq).
        reflexivity.
        ltac1:(exfalso).
        apply H. clear H.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        rewrite elem_of_singleton.
        reflexivity.
    }
    {
        unfold satisfies in *; simpl in *.
        destruct g;
            ltac1:(simp sat2B in HH).
        { destruct HH. }
        ltac1:(simp sat2B).
        ltac1:(destruct_and!; (repeat split); simplify_eq/=; try congruence).
        intros.
        eapply TermOverBoV_satisfies_extensive>[|eapply X].
        {
            unfold TermOver, Valuation2 in *.
            ltac1:(rewrite map_subseteq_spec).
            intros i0 x Hx.
            rewrite map_lookup_filter in Hx.
            rewrite map_lookup_filter.
            ltac1:(simplify_option_eq).
            reflexivity.
            ltac1:(exfalso).
            rewrite vars_of_t_term in H3.
            rewrite elem_of_union_list in H3.
            apply H3. clear H3.
            exists (vars_of φ').
            split>[|assumption].
            rewrite elem_of_list_fmap.
            exists φ'.
            split>[reflexivity|].
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        {
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        {
            eapply H2.
            apply pf1.
            apply pf2.
        }
    }
Qed.

Lemma SideCondition_satisfies_extensive
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ1 ρ2 : Valuation2)
    (c : SideCondition)
    (nv : NondetValue)
    (b : bool)
    :
    ρ1 ⊆ ρ2 ->
    SideCondition_evaluate program ρ1 nv c = Some b ->
    SideCondition_evaluate program ρ2 nv c = Some b
.
Proof.
    revert b.
    induction c;
        intros b Hrhos;
        simpl;
        intros HH;
        unfold SideCondition_evaluate in *.
    {
        exact HH.
    }
    {
        exact HH.
    }
    {
        unfold satisfies in *; simpl in *.
        rewrite bind_Some in HH.
        rewrite bind_Some.
        destruct HH as [l [H1l H2l]].
        exists l.
        split>[|apply H2l].
        eapply list_collect_Expression2_evaluate_extensive_Some>[|apply H1l].
        apply Hrhos.
    }
    {
        rewrite bind_Some in HH.
        destruct HH as [b' [H1b' H2b']].
        rewrite bind_Some in H2b'.
        destruct H2b' as [b'' [H1b'' H2b'']].
        apply (inj Some) in H2b''.
        subst b.
        rewrite bind_Some.
        exists b'.
        split.
        {
            apply IHc1.
            apply Hrhos.
            apply H1b'.
        }
        {
            rewrite bind_Some.
            exists b''.
            split>[|reflexivity].
            apply IHc2.
            apply Hrhos.
            apply H1b''.
        }
    }
    {
        rewrite bind_Some in HH.
        destruct HH as [b' [H1b' H2b']].
        rewrite bind_Some in H2b'.
        destruct H2b' as [b'' [H1b'' H2b'']].
        apply (inj Some) in H2b''.
        subst b.
        rewrite bind_Some.
        exists b'.
        split.
        {
            apply IHc1.
            apply Hrhos.
            apply H1b'.
        }
        {
            rewrite bind_Some.
            exists b''.
            split>[|reflexivity].
            apply IHc2.
            apply Hrhos.
            apply H1b''.
        }
    }
Qed.

Lemma SideCondition_satisfies_strip
    {Σ : StaticModel}
    (program : ProgramT)
    (c : SideCondition)
    (ρ : Valuation2)
    (nv : NondetValue)
    (b : bool)
:
    SideCondition_evaluate program ρ nv c = Some b ->
    SideCondition_evaluate program (filter (fun kv => kv.1 ∈ vars_of c) ρ) nv c = Some b
.
Proof.
    revert b ρ.
    induction c;
        intros b ρ;
        unfold satisfies;
        simpl;
        intros HH.
    {
        exact HH.
    }
    {
        exact HH.
    }
    {    
        unfold SideCondition_evaluate in *.
        rewrite bind_Some in HH.
        destruct HH as [l [H1l H2l]].
        rewrite bind_Some.
        exists l.
        split>[|apply H2l].
        clear H2l.
        clear b.
        unfold vars_of; simpl.
        clear pred.

        revert l H1l.
        induction args; intros l H1l; simpl in *.
        { exact H1l. }
        {
            rewrite bind_Some in H1l.
            destruct H1l as [b [H1b H2b]].
            rewrite bind_Some in H2b.
            destruct H2b as [c [H1c H2c]].
            apply (inj Some) in H2c.
            subst l.
            rewrite bind_Some.
            exists b.
            split.
            {
                unfold vars_of; simpl.
                apply Expression2_evalute_strip in H1b.
                eapply Expression2_evaluate_extensive_Some in H1b.
                rewrite H1b.
                { reflexivity. }
                {
                    apply map_subseteq_spec.
                    intros i x Hix.
                    unfold Valuation2 in *.
                    rewrite map_lookup_filter_Some in Hix.
                    rewrite map_lookup_filter_Some.
                    destruct Hix as [H1ix H2ix].
                    simpl in *.
                    split>[apply H1ix|].
                    rewrite elem_of_union.
                    left.
                    exact H2ix.
                }
            }
            {
                rewrite bind_Some.
                exists c.
                split>[|reflexivity].
                specialize (IHargs _ H1c).
                clear H1c.
                eapply list_collect_Expression2_evaluate_extensive_Some>[
                    |apply IHargs
                ].
                apply map_subseteq_spec.
                intros i x Hix.
                unfold Valuation2 in *.
                rewrite map_lookup_filter_Some in Hix.
                rewrite map_lookup_filter_Some.
                destruct Hix as [H1ix H2ix].
                simpl in *.
                split>[apply H1ix|].
                unfold vars_of; simpl.
                rewrite elem_of_union.
                right.
                exact H2ix.
            }
        }
    }
    {
        rewrite bind_Some in HH.
        rewrite bind_Some.
        destruct HH as [b' [H1b' H2b']].
        rewrite bind_Some in H2b'.
        destruct H2b' as [b'' [H1b'' H2b'']].
        apply (inj Some) in H2b''.
        subst b.
        setoid_rewrite bind_Some.
        specialize (IHc1 _ _ H1b').
        exists b'.
        split.
        {
            eapply SideCondition_satisfies_extensive>[|apply IHc1].
            apply map_subseteq_spec.
            intros i x Hix.
            unfold Valuation2 in *.
            rewrite map_lookup_filter in Hix.
            rewrite map_lookup_filter.
            rewrite bind_Some in Hix.
            rewrite bind_Some.
            destruct Hix as [g' [H1g' H2g']].
            exists g'.
            split>[exact H1g'|].
            ltac1:(simplify_option_eq).
            { reflexivity. }
            {
                unfold vars_of in H1; simpl in H1.
                ltac1:(set_solver).
            }
        }
        {
            exists b''.
            split>[|reflexivity].
            eapply SideCondition_satisfies_extensive>[|apply IHc2].
            apply map_subseteq_spec.
            intros i x Hix.
            unfold Valuation2 in *.
            rewrite map_lookup_filter in Hix.
            rewrite map_lookup_filter.
            rewrite bind_Some in Hix.
            rewrite bind_Some.
            destruct Hix as [g' [H1g' H2g']].
            exists g'.
            split>[exact H1g'|].
            ltac1:(simplify_option_eq).
            { reflexivity. }
            {
                unfold vars_of in H1; simpl in H1.
                ltac1:(set_solver).
            }
            {
                assumption.
            }
        }
    }
    {
        rewrite bind_Some in HH.
        rewrite bind_Some.
        destruct HH as [b' [H1b' H2b']].
        rewrite bind_Some in H2b'.
        destruct H2b' as [b'' [H1b'' H2b'']].
        apply (inj Some) in H2b''.
        subst b.
        setoid_rewrite bind_Some.
        specialize (IHc1 _ _ H1b').
        exists b'.
        split.
        {
            eapply SideCondition_satisfies_extensive>[|apply IHc1].
            apply map_subseteq_spec.
            intros i x Hix.
            unfold Valuation2 in *.
            rewrite map_lookup_filter in Hix.
            rewrite map_lookup_filter.
            rewrite bind_Some in Hix.
            rewrite bind_Some.
            destruct Hix as [g' [H1g' H2g']].
            exists g'.
            split>[exact H1g'|].
            ltac1:(simplify_option_eq).
            { reflexivity. }
            {
                unfold vars_of in H1; simpl in H1.
                ltac1:(set_solver).
            }
        }
        {
            exists b''.
            split>[|reflexivity].
            eapply SideCondition_satisfies_extensive>[|apply IHc2].
            apply map_subseteq_spec.
            intros i x Hix.
            unfold Valuation2 in *.
            rewrite map_lookup_filter in Hix.
            rewrite map_lookup_filter.
            rewrite bind_Some in Hix.
            rewrite bind_Some.
            destruct Hix as [g' [H1g' H2g']].
            exists g'.
            split>[exact H1g'|].
            ltac1:(simplify_option_eq).
            { reflexivity. }
            {
                unfold vars_of in H1; simpl in H1.
                ltac1:(set_solver).
            }
            {
                assumption.
            }
        }
    }
Qed.

Lemma satisfies_term_bov_inv
    {Σ : StaticModel}
    (ρ : Valuation2)
    (γ : TermOver builtin_value)
    (s : symbol)
    (l : list (TermOver BuiltinOrVar))
    :
    satisfies ρ γ (t_term s l) ->
    { lγ : list (TermOver builtin_value) &
        ((γ = (t_term s lγ)) *
        (length l = length lγ) *
        ( forall (i : nat) γ e,
            lγ !! i = Some γ ->
            l !! i = Some e ->
            satisfies ρ γ e
        )
        )%type
    }
.
Proof.
    revert γ.
    induction l using rev_ind_T; intros γ.
    {
        intros H. exists [].
        unfold satisfies in H; simpl in H.
        destruct γ;
            ltac1:(simp sat2B in H).
        { destruct H. }
        {
            destruct H as [H1 [H2 H3]].
            destruct l.
            {
                subst s0.
                (repeat split).
                intros.
                rewrite lookup_nil in H.
                inversion H.
            }
            {
                simpl in H2. inversion H2.
            }
        }
    }
    {
        intros H.
        unfold satisfies in H; simpl in H.
        destruct γ; ltac1:(simp sat2B in H).
        { destruct H. }
        destruct H as [H1 [H2 H3]].
        destruct (analyze_list_from_end l0) as [He|He].
        {
            subst l0.
            rewrite length_app in H2.
            simpl in H2.
            ltac1:(lia).
        }
        destruct He as [l' [x' Hl0]].
        subst l0.
        do 2 (rewrite length_app in H2).
        simpl in H2.
        unfold TermOver in *.
        assert (length l' = length l) by ltac1:(lia).
        clear H2.
        specialize (H3 (length l) x' x) as H3'.
        unfold TermOver in *; simpl in *.
        rewrite lookup_app_r in H3'>[|ltac1:(lia)].
        rewrite lookup_app_r in H3'>[|ltac1:(lia)].
        rewrite Nat.sub_diag in H3'.
        rewrite H in H3'.
        rewrite Nat.sub_diag in H3'.
        specialize (H3' erefl erefl).
        unfold satisfies in IHl; simpl in IHl.
        specialize (IHl (t_term s l')).
        ltac1:(ospecialize (IHl _)).
        {
            ltac1:(simp sat2B).
            split>[reflexivity|].
            split>[ltac1:(lia)|].
            intros.
            apply H3 with (i := i).
            {
                rewrite lookup_app_l.
                assumption.
                apply lookup_lt_Some in pf1.
                assumption.
            }
            {
                rewrite lookup_app_l.
                assumption.
                apply lookup_lt_Some in pf2.
                assumption.
            }
        }
        destruct IHl as [lγ Hlγ].
        destruct Hlγ as [[HH1 HH2] HH3].
        inversion HH1; subst; clear HH1.
        exists (lγ ++ [x']).
        (repeat split).
        {
            do 2 (rewrite length_app).
            simpl.
            ltac1:(lia).
        }
        {
            intros.
            destruct (decide (i < length l)).
            {
                rewrite lookup_app_l in H0>[|ltac1:(lia)].
                rewrite lookup_app_l in H1>[|ltac1:(lia)].
                eapply HH3.
                apply H0.
                apply H1.
            }
            {
                unfold satisfies; simpl.
                eapply H3.
                apply H1.
                apply H0.   
            }
        }
    }
Qed.


Lemma satisfies_term_expr_inv
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (nv : NondetValue)
    (γ : TermOver builtin_value)
    (s : symbol)
    (l : list (TermOver Expression2))
    :
    satisfies ρ (program, (nv,γ)) (t_term s l) ->
    { lγ : list (TermOver builtin_value) &
        ((γ = (t_term s lγ)) *
        (length l = length lγ) *
        ( forall (i : nat) γ e,
            lγ !! i = Some γ ->
            l !! i = Some e ->
            satisfies ρ (program, (nv,γ)) e
        )
        )%type
    }
.
Proof.
    revert γ.
    induction l using rev_ind_T; intros γ.
    {
        intros H. exists [].
        unfold satisfies in H; simpl in H.
        destruct γ;
            ltac1:(simp sat2E in H).
        { destruct H. }
        {
            destruct H as [H1 [H2 H3]].
            destruct l.
            {
                subst s0.
                (repeat split).
                intros.
                rewrite lookup_nil in H.
                inversion H.
            }
            {
                simpl in H2. inversion H2.
            }
        }
    }
    {
        intros H.
        unfold satisfies in H; simpl in H.
        destruct γ; ltac1:(simp sat2E in H).
        { destruct H. }
        destruct H as [H1 [H2 H3]].
        destruct (analyze_list_from_end l0) as [He|He].
        {
            subst l0.
            rewrite length_app in H2.
            simpl in H2.
            ltac1:(lia).
        }
        destruct He as [l' [x' Hl0]].
        subst l0.
        do 2 (rewrite length_app in H2).
        simpl in H2.
        unfold TermOver in *.
        assert (length l' = length l) by ltac1:(lia).
        clear H2.
        specialize (H3 (length l) x' x) as H3'.
        unfold TermOver in *; simpl in *.
        rewrite lookup_app_r in H3'>[|ltac1:(lia)].
        rewrite lookup_app_r in H3'>[|ltac1:(lia)].
        rewrite Nat.sub_diag in H3'.
        rewrite H in H3'.
        rewrite Nat.sub_diag in H3'.
        specialize (H3' erefl erefl).
        unfold satisfies in IHl; simpl in IHl.
        specialize (IHl (t_term s l')).
        ltac1:(ospecialize (IHl _)).
        {
            ltac1:(simp sat2E).
            split>[reflexivity|].
            split>[ltac1:(lia)|].
            intros.
            apply H3 with (i := i).
            {
                rewrite lookup_app_l.
                assumption.
                apply lookup_lt_Some in pf1.
                assumption.
            }
            {
                rewrite lookup_app_l.
                assumption.
                apply lookup_lt_Some in pf2.
                assumption.
            }
        }
        destruct IHl as [lγ Hlγ].
        destruct Hlγ as [[HH1 HH2] HH3].
        inversion HH1; subst; clear HH1.
        exists (lγ ++ [x']).
        (repeat split).
        {
            do 2 (rewrite length_app).
            simpl.
            ltac1:(lia).
        }
        {
            intros.
            destruct (decide (i < length l)).
            {
                rewrite lookup_app_l in H0>[|ltac1:(lia)].
                rewrite lookup_app_l in H1>[|ltac1:(lia)].
                eapply HH3.
                apply H0.
                apply H1.
            }
            {
                unfold satisfies; simpl.
                eapply H3.
                apply H1.
                apply H0.   
            }
        }
    }
Qed.


Lemma satisfies_TermOverBuiltin_to_TermOverBoV
    {Σ : StaticModel}
    (ρ : Valuation2)
    (γ : TermOver builtin_value)
    :
    satisfies ρ γ (TermOverBuiltin_to_TermOverBoV γ)
.
Proof.
    unfold TermOverBuiltin_to_TermOverBoV, TermOver_map.
    unfold satisfies; simpl.
    ltac1:(induction γ using TermOver_rect).
    {
        unfold TermOverBuiltin_to_TermOverBoV.
        simpl.
        ltac1:(simp sat2B).
        simpl.
        reflexivity.
    }
    {
        unfold TermOverBuiltin_to_TermOverBoV.
        simpl.
        ltac1:(simp sat2B).
        simpl.
        split>[reflexivity|].
        rewrite map_length.
        split>[reflexivity|].
        intros i t' φ' HH1 HH2.
        ltac1:(replace (map) with (@fmap list list_fmap) in HH1 by reflexivity).
        rewrite list_lookup_fmap in HH1.
        ltac1:(rewrite HH2 in HH1).
        simpl in HH1.
        ltac1:(simplify_eq/=).
        apply H.
        rewrite elem_of_list_lookup.
        exists i.
        exact HH2.
    }
Qed.

Lemma satisfies_var
    {Σ : StaticModel}
    (ρ : Valuation2)
    x γ:
    ρ !! x = Some (γ) ->
    satisfies ρ γ (t_over (bov_variable x))
.
Proof.
    intros H.
    destruct γ; (repeat constructor); assumption.
Qed.

Lemma satisfies_var_expr
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (nv : NondetValue)
    x γ:
    ρ !! x = Some (γ) ->
    satisfies ρ (program, (nv,γ)) (t_over (e_variable x))
.
Proof.
    intros H.
    unfold satisfies; simpl.
    destruct γ; ltac1:(simp sat2E); simpl;
        rewrite H; reflexivity.
Qed.


Lemma satisfies_var_inv
    {Σ : StaticModel}
    (ρ : Valuation2)
    x γ:
    satisfies ρ γ (t_over (bov_variable x)) ->
    ρ !! x = Some (γ)
.
Proof.
    unfold satisfies; simpl.
    ltac1:(simp sat2B). simpl.
    intros H; exact H.
Qed.

Lemma satisfies_var_expr_inv
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (nv : NondetValue)
    x γ:
    satisfies ρ (program, (nv,γ)) (t_over (e_variable x)) ->
    ρ !! x = Some (γ)
.
Proof.
    unfold satisfies; simpl.
    ltac1:(simp sat2E).
    intros H.
        destruct (Expression2_evaluate program ρ (e_variable x)) eqn:Heq>[|ltac1:(contradiction)].
    simpl in Heq.
    destruct (ρ !! x) eqn:Heq2.
    {
        inversion Heq; subst; clear Heq.
        reflexivity.
    }
    { inversion Heq. }
Qed.




Lemma forall_satisfies_inv'
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation2)
    (γ1 γ2 : list (TermOver builtin_value))
    (l : list (TermOver BuiltinOrVar))
    :
    sum_list_with (S ∘ TermOver_size) l < sz ->
    length γ1 = length l ->
    length γ2 = length l ->
    (forall idx a b, γ1 !! idx = Some a -> l !! idx = Some b -> satisfies ρ a b) ->
    (forall idx a b, γ2 !! idx = Some a -> l !! idx = Some b -> satisfies ρ a b) ->
    γ1 = γ2
with satisfies_inv'
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation2)
    (x y : TermOver builtin_value)
    (z : TermOver BuiltinOrVar)
    :
    TermOver_size z < sz ->
    satisfies ρ x z ->
    satisfies ρ y z ->
    x = y
.
Proof.
    {
        intros Hsz H1 H2 H3.
        destruct sz.
        {
            ltac1:(lia).
        }

        intros H4.
        apply list_eq.
        intros i.
        destruct
            (γ1 !! i) eqn:Hγ1i,
            (γ2 !! i) eqn:Hγ2i.
        {
            destruct (l !! i) eqn:Hli.
            {
                specialize (H3 i t t1 Hγ1i Hli).
                specialize (H4 i t0 t1 Hγ2i Hli).
                clear -H3 H4 satisfies_inv' sz Hsz Hli.
                f_equal.
                specialize (satisfies_inv' Σ sz ρ t t0 t1).
                apply satisfies_inv'; try assumption.
                apply take_drop_middle in Hli.
                rewrite <- Hli in Hsz.

                rewrite sum_list_with_app in Hsz.
                simpl in Hsz.
                ltac1:(lia).
            }
            {
                apply lookup_lt_Some in Hγ1i.
                apply lookup_ge_None in Hli.
                ltac1:(lia).
            }
        }
        {
            apply lookup_lt_Some in Hγ1i.
            apply lookup_ge_None in Hγ2i.
            ltac1:(lia).
        }
        {
            apply lookup_lt_Some in Hγ2i.
            apply lookup_ge_None in Hγ1i.
            ltac1:(lia).
        }
        {
            reflexivity.
        }
    }
    {
        intros Hsz H1 H2.

        destruct sz.
        {
            ltac1:(lia).
        }

        destruct
            x as [ax|cx lx],
            y as [ay|cy ly],
            z as [az|cz lz]
            .
        {
            unfold satisfies in *; simpl in *.
            ltac1:(simp sat2B in H1).
            ltac1:(simp sat2B in H2).
            simpl in *.
            destruct az; simpl in *; ltac1:(simplify_eq/=); reflexivity.
        }
        {
            unfold satisfies in *; simpl in *.
            ltac1:(simp sat2B in H1).
            simpl in H1.
            destruct H1.
        }
        {
            unfold satisfies in *; simpl in *.
            ltac1:(simp sat2B in H1).
            ltac1:(simp sat2B in H2).
            simpl in *.
            destruct az; simpl in *; ltac1:(simplify_eq/=).
        }
        {
            unfold satisfies in *; simpl in *.
            ltac1:(simp sat2B in H1).
            ltac1:(simp sat2B in H2).
            simpl in *.
            destruct H1.
        }
        {
            unfold satisfies in *; simpl in *.
            ltac1:(simp sat2B in H1).
            ltac1:(simp sat2B in H2).
            simpl in *.
            destruct az; simpl in *; ltac1:(simplify_eq/=).
        }
        {
            unfold satisfies in *; simpl in *.
            ltac1:(simp sat2B in H1).
            ltac1:(simp sat2B in H2).
            simpl in *.
            destruct H2.
        }
        {
            unfold satisfies in *; simpl in *.
            ltac1:(simp sat2B in H1).
            ltac1:(simp sat2B in H2).
            simpl in *.
            destruct az; simpl in *; ltac1:(simplify_eq/=).
            reflexivity.
        }
        {
            unfold satisfies in *; simpl in *.
            ltac1:(simp sat2B in H1).
            ltac1:(simp sat2B in H2).
            simpl in *.
            ltac1:(destruct_and!).
            ltac1:(simplify_eq/=).
            f_equal.
            eapply forall_satisfies_inv' with (l := lz)(sz := sz).
            ltac1:(lia).
            unfold TermOver in *;
                ltac1:(lia).
            unfold TermOver in *;
                ltac1:(lia).
            intros.
            eapply H5.
            apply H0.
            apply H.
            intros.
            eapply H3.
            apply H0.
            apply H.
        }
    }
Qed.

Lemma forall_satisfies_inv
    {Σ : StaticModel}
    (ρ : Valuation2)
    (γ1 γ2 : list (TermOver builtin_value))
    (l : list (TermOver BuiltinOrVar))
    :
    length γ1 = length l ->
    length γ2 = length l ->
    (forall idx a b, γ1 !! idx = Some a -> l !! idx = Some b -> satisfies ρ a b) ->
    (forall idx a b, γ2 !! idx = Some a -> l !! idx = Some b -> satisfies ρ a b) ->
    γ1 = γ2
.
Proof.
    intros.
    eapply forall_satisfies_inv' with (l := l)(ρ := ρ) (sz := S (sum_list_with (S ∘ TermOver_size) l));
        try assumption.
    ltac1:(lia).
Qed.

Lemma satisfies_inv
    {Σ : StaticModel}
    (ρ : Valuation2)
    (x y : TermOver builtin_value)
    (z : TermOver BuiltinOrVar)
    :
    satisfies ρ x z ->
    satisfies ρ y z ->
    x = y
.
Proof.
    intros.
    apply satisfies_inv' with (ρ := ρ) (z := z) (sz := S (TermOver_size z));
        try assumption.
    ltac1:(lia).
Qed.



Lemma satisfies_in_size
    {Σ : StaticModel}
    (ρ : Valuation2)
    (x : variable)
    (t t' : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    x ∈ vars_of (φ) ->
    ρ !! x = Some (t') ->
    satisfies ρ t φ ->
    TermOver_size t' <= TermOver_size t
.
Proof.
    revert t.
    induction φ; intros t Hin Hsome Hsat.
    {
        destruct a.
        {
            unfold satisfies in *; simpl in *.
            destruct t; ltac1:(simp sat2B in Hsat);
                simpl in *; ltac1:(simplify_eq/=).
            ltac1:(exfalso).
            unfold vars_of in Hin; simpl in Hin.
            unfold vars_of in Hin; simpl in Hin.
            ltac1:(set_solver).
        }
        {
            unfold satisfies in *; simpl in *.
            destruct t; ltac1:(simp sat2B in Hsat);
                simpl in *; ltac1:(simplify_eq/=).
            {
                unfold vars_of in Hin; simpl in Hin.
                unfold vars_of in Hin; simpl in Hin.
                rewrite elem_of_singleton in Hin. subst x0.
                ltac1:(simplify_eq/=).
                ltac1:(lia).
            }
            {
                unfold vars_of in Hin; simpl in Hin.
                unfold vars_of in Hin; simpl in Hin.
                rewrite elem_of_singleton in Hin. subst x0.
                ltac1:(simplify_eq/=).
                ltac1:(lia).
            }
        }
    }
    {
        apply satisfies_term_bov_inv in Hsat.
        destruct Hsat as [lγ [[H1 H2] H3]].
        subst.
        simpl.
        simpl in Hin.
        rewrite vars_of_t_term in Hin.
        clear s.
        revert l H Hin H2 H3; induction lγ; intros l H Hin H2 H3.
        {
            simpl in *.
            destruct l; simpl in *; try ltac1:(lia).
            ltac1:(exfalso; clear -Hin; set_solver).
        }
        {
            simpl in *.
            destruct l; simpl in *; try ltac1:(lia).
            rewrite Forall_cons in H.
            destruct H as [IH1 IH2].
            
            rewrite elem_of_union in Hin.
            destruct Hin as [Hin|Hin].
            {
                specialize (H3 0 a t erefl erefl) as H3'.
                specialize (IH1 _ Hin Hsome H3').
                ltac1:(lia).
            }
            {
                specialize (IHlγ _ IH2 Hin ltac:(lia)).
                ltac1:(ospecialize (IHlγ _)).
                {
                    intros. apply H3 with (i := S i); simpl; assumption.
                }
                ltac1:(lia).
            }
        }
    }
Qed.


Lemma double_satisfies_contradiction
    {Σ : StaticModel}
    (ρ : Valuation2)
    (ay : BuiltinOrVar)
    (cz cx : symbol)
    (lx : list (TermOver builtin_value))
    (lz : list (TermOver BuiltinOrVar))
    :
    vars_of ((t_over ay)) = vars_of ((t_term cz lz)) ->
    satisfies ρ (t_term cx lx) (t_over ay) ->
    satisfies ρ (t_term cx lx) (t_term cz lz) ->
    False
.
Proof.
    intros Hvars H1 H2.
    unfold satisfies in *; simpl in *.
    ltac1:(simp sat2B in H1).
    ltac1:(simp sat2B in H2).
    destruct ay; simpl in *;
        ltac1:(destruct_and?; simplify_eq/=).
    rewrite vars_of_t_term in Hvars.
    assert (H: x ∈ vars_of lz).
    {
        unfold vars_of; simpl.
        rewrite <- Hvars.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        ltac1:(set_solver).
    }
    unfold vars_of in H; simpl in H.
    rewrite elem_of_union_list in H.
    destruct H as [X [H1X H2X]].
    rewrite elem_of_list_fmap in H1X.
    destruct H1X as [y [H1y H2y]].
    subst.
    rewrite elem_of_list_lookup in H2y.
    destruct H2y as [i Hi].
    destruct (lx !! i) eqn:Hlxi.
    {
        specialize (H3 i _ _ Hi Hlxi).
        assert (Htmp1 := satisfies_in_size ρ x t (t_term cz lx) y H2X H1 H3).
        simpl in Htmp1.
        apply take_drop_middle in Hlxi.
        rewrite <- Hlxi in Htmp1.
        rewrite sum_list_with_app in Htmp1.
        simpl in Htmp1.
        ltac1:(lia).
    }
    {
        apply lookup_ge_None in Hlxi.
        apply lookup_lt_Some in Hi.
        unfold Valuation2,TermOver in *.
        ltac1:(lia).
    }
Qed.


Definition size_of_var_in_val
    {Σ : StaticModel}
    (ρ : Valuation2)
    (x : variable)
    : nat
:=
    match ρ!!x with
    | None => 0
    | Some g => pred (TermOver_size (g))
    end
.

Definition delta_in_val
    {Σ : StaticModel}
    (ρ : Valuation2)
    (ψ : TermOver BuiltinOrVar)
    : nat
:=
    sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ)
.



Lemma concrete_is_larger_than_symbolic
    {Σ : StaticModel}
    (ρ : Valuation2)
    (γ : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    satisfies ρ γ φ ->
    TermOver_size γ = TermOver_size φ + delta_in_val ρ φ
.
Proof.
    revert φ.
    induction γ; intros φ H1.
    {
        unfold satisfies in H1; simpl in H1.
        destruct φ; ltac1:(simp sat2B in H1);
            simpl in H1.
        {
            destruct a0; simpl in *;
                ltac1:(simplify_eq/=);
                unfold delta_in_val,vars_of_to_l2r;
                simpl.
            {
                reflexivity.
            }
            {
                unfold size_of_var_in_val; simpl.
                unfold Valuation2,TermOver in *.
                rewrite H1.
                simpl. reflexivity.
            }
        }
        { destruct H1. }
    }
    {
        simpl.
        destruct φ.
        {
            destruct a.
            {
                unfold satisfies in H1; simpl in H1.
                ltac1:(simp sat2B in H1).
                simpl in H1.
                inversion H1.
            }
            {
                unfold satisfies in H1; simpl in H1.
                ltac1:(simp sat2B in H1).
                simpl in H1.
                simpl.
                unfold delta_in_val. simpl.
                unfold size_of_var_in_val.
                unfold Valuation2,TermOver in *.
                rewrite H1. simpl.
                unfold TermOver in *.
                apply f_equal.            
                simpl. ltac1:(lia).
            }
        }
        {
            apply satisfies_term_bov_inv in H1.
            destruct H1 as [lγ [[H2 H3] H4]].
            inversion H2; subst; clear H2.
            simpl.
            revert l0 H3 H4.
            induction lγ; intros l0 H3 H4.
            {
                destruct l0.
                {
                    simpl. unfold delta_in_val. simpl. ltac1:(lia).
                }
                {
                    simpl in H3. ltac1:(lia).
                }
            }
            {
                destruct l0.
                {
                    simpl in *. ltac1:(lia).
                }
                {
                    simpl in *.
                    rewrite Forall_cons in H.
                    destruct H as [H H'].
                    specialize (IHlγ H').
                    specialize (IHlγ l0 ltac:(lia)).
                    ltac1:(ospecialize (IHlγ _)).
                    {
                        intros. eapply H4 with (i := S i); simpl; assumption.
                    }
                    simpl in *.
                    specialize (H _ (H4 0 a t eq_refl eq_refl)).
                    unfold delta_in_val. simpl.
                    rewrite sum_list_with_app.
                    rewrite H.
                    unfold delta_in_val in IHlγ.
                    simpl in IHlγ.
                    injection H3 as H3.
                    injection IHlγ as IHlγ.
                    rewrite IHlγ.
                    unfold delta_in_val.
                    ltac1:(lia).
                }
            }
        }
    }
Qed.

Lemma enveloping_preserves_or_increases_delta
    {Σ : StaticModel}
    (ρ : Valuation2)
    (γ1 γ2 : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    (s : symbol)
    (l1 l2 : list (TermOver BuiltinOrVar))
    (d : nat)
    :
    satisfies ρ γ1 φ ->
    satisfies ρ γ2 (t_term s (l1 ++ φ::l2)) ->
    TermOver_size γ1 = TermOver_size φ + d ->
    TermOver_size γ2 >= TermOver_size (t_term s (l1 ++ φ::l2)) + d
.
Proof.
    intros H1 H2 H3.
    simpl.
    apply satisfies_term_bov_inv in H2.
    destruct H2 as [lγ [[h4 H5] H6]].
    subst γ2. simpl in *.
    rewrite sum_list_with_app. simpl.
    rewrite length_app in H5. simpl in H5.

    destruct (lγ !! (length l1)) eqn:Hγ.
    {
        apply take_drop_middle in Hγ.
        rewrite <- Hγ in H6.
        {
            assert (t = γ1).
            {
                eapply satisfies_inv.
                {
                    apply H6 with (i := length l1).
                    {
                        rewrite lookup_app_r.
                        {
                            rewrite length_take.
                            ltac1:(replace ((length l1 - length l1 `min` length lγ)) with 0 by lia).
                            simpl. reflexivity.
                        }
                        {
                            rewrite length_take.
                            ltac1:(lia).
                        }
                    }
                    {
                        rewrite lookup_app_r.
                        {
                            rewrite Nat.sub_diag. simpl.
                            reflexivity.
                        }
                        {
                            ltac1:(lia).
                        }
                    }
                }
                {
                    apply H1.
                }
            }
            subst t.
            simpl in *.
            rewrite <- Hγ.
            rewrite sum_list_with_app.
            simpl.
            rewrite H3.
            clear H3.
            clear Hγ.
            assert (sum_list_with (S ∘ TermOver_size) (take (length l1) lγ) >= sum_list_with (S ∘ TermOver_size) l1).
            {
                assert (Hineq: length lγ >= length l1) by ltac1:(lia).
                clear -H6 Hineq.
                revert lγ H6 Hineq.
                induction l1; intros lγ H6 Hineq.
                {
                    simpl. ltac1:(lia).
                }
                {
                    destruct lγ.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        assert (Hsat := H6 0 t a eq_refl eq_refl).
                        apply concrete_is_larger_than_symbolic in Hsat.
                        specialize (IHl1 lγ).
                        ltac1:(ospecialize (IHl1 _)).
                        {
                            intros. eapply H6 with (i := S i); simpl. apply H. assumption.
                        }
                        simpl in *.
                        specialize (IHl1 ltac:(lia)).
                        ltac1:(lia).
                    }
                }
            }
            assert (((sum_list_with (S ∘ TermOver_size) (drop (S (length l1)) lγ))) >= (sum_list_with (S ∘ TermOver_size) l2)).
            {
                remember ((drop (S (length l1)) lγ)) as lγ'.
                assert (Hlen: length lγ' = length l2).
                {
                    subst.
                    rewrite length_drop.
                    ltac1:(lia).
                }
                clear -Hlen H6 H5.
                assert (H7: ∀ i γ e, lγ' !! i = Some γ -> l2 !! i = Some e -> satisfies ρ γ e).
                {
                    intros.
                    specialize (H6 (i + (length (l1 ++ [φ]))) γ e).
                    ltac1:(
                        replace (take (length l1) lγ ++ γ1 :: lγ')
                        with ((take (length l1) lγ ++ [γ1]) ++ lγ')
                        in H6
                        by (rewrite <- app_assoc; reflexivity)
                    ).
                    rewrite lookup_app_r in H6.
                    {
                        rewrite length_app in H6.
                        rewrite length_app in H6.
                        rewrite length_take in H6.
                        simpl in H6.
                        ltac1:(
                            replace (i + (length l1 + 1) - (length l1 `min` length lγ + 1))
                            with (i)
                            in H6
                            by lia
                        ).
                        specialize (H6 ltac:(assumption)).
                        ltac1:(
                            replace (l1 ++ (φ :: l2))
                            with ((l1 ++ [φ]) ++ l2)
                            in H6
                            by (rewrite <- app_assoc; reflexivity)
                        ).
                        rewrite lookup_app_r in H6.
                        {
                            rewrite length_app in H6.
                            simpl in H6.
                            ltac1:(
                                replace ((i + (length l1 + 1) - (length l1 + 1)))
                                with (i)
                                in H6
                                by lia
                            ).
                            specialize (H6 ltac:(assumption)).
                            apply H6.
                        }
                        {
                            rewrite length_app. simpl.
                            ltac1:(lia).
                        }
                    }
                    {
                        rewrite length_app.
                        rewrite length_app.
                        rewrite length_take.
                        simpl.
                        ltac1:(lia).
                    }
                }
                clear H6.
                clear H5 lγ.
                revert l2 Hlen H7.
                induction lγ'; intros l2 Hlen H8.
                {
                    destruct l2.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        simpl in *. ltac1:(lia).
                    }
                }
                {
                    destruct l2.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        simpl in *.
                        assert (H1 := H8 (0) a t eq_refl eq_refl). simpl in H1.
                        apply concrete_is_larger_than_symbolic in H1.
                        specialize (IHlγ' l2 ltac:(lia)).
                        ltac1:(ospecialize (IHlγ' _)).
                        {
                            intros.
                            exact (H8 (S i) γ e ltac:(assumption) ltac:(assumption)).
                        }
                        ltac1:(lia).
                    }
                }
            }
            
            ltac1:(lia).
        }
    }
    {
        apply lookup_ge_None_1 in Hγ.
        ltac1:(lia).
    }
Qed.



Lemma TermOverBoV_subst_once_size
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of ψ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    TermOver_size (TermOverBoV_subst φ h ψ) = Nat.pred (TermOver_size φ + TermOver_size ψ)
.
Proof.
    induction φ; simpl; intros Hnotinψ Hexactlyonce.
    {
        destruct a.
        {
            simpl in *. ltac1:(lia).
        }
        {
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h = x)).
            {
                simpl in *. reflexivity.
            }
            {
                simpl in *. ltac1:(lia).
            }
        }
    }
    {
        simpl in *.
        rewrite sum_list_with_compose.
        unfold compose.
        do 2 (rewrite sum_list_with_S).
        do 2 (rewrite map_length).
        do 2 (rewrite sum_list_fmap).
        rewrite length_fmap.

        assert (Hconcat: h ∈ concat (map vars_of_to_l2r l)).
        {
            clear -Hexactlyonce.
            induction l; simpl in *.
            { ltac1:(lia). }
            {
                rewrite filter_app in Hexactlyonce.
                rewrite length_app in Hexactlyonce.
                destruct (decide (h ∈ vars_of_to_l2r a)).
                {
                    rewrite elem_of_app. left. assumption.
                }
                {
                    ltac1:(ospecialize (IHl _)).
                    {
                        ltac1:(cut(length (filter (eq h) (vars_of_to_l2r a)) = 0)).
                        {
                            intros HH. ltac1:(lia).
                        }
                        rewrite length_zero_iff_nil.
                        remember (vars_of_to_l2r a) as l'.
                        clear Heql'.
                        clear -n.
                        induction l'.
                        {
                            reflexivity.
                        }
                        {
                            rewrite elem_of_cons in n.
                            apply Decidable.not_or in n.
                            destruct n as [H1 H2].
                            specialize (IHl' H2).
                            rewrite filter_cons.
                            destruct (decide (h = a)).
                            {
                                subst. ltac1:(contradiction).
                            }
                            {
                                apply IHl'.
                            }
                        }
                    }
                    {
                        rewrite elem_of_app. right. apply IHl.
                    }
                }
            }
        }
        rewrite elem_of_list_In in Hconcat.
        rewrite in_concat in Hconcat.
        destruct Hconcat as [x [H1x H2x]].
        rewrite in_map_iff in H1x.
        destruct H1x as [x0 [H1x0 H2x0]].
        subst.

        rewrite <- elem_of_list_In in H2x.
        rewrite elem_of_list_lookup in H2x.
        destruct H2x as [i Hi].

        rewrite <- elem_of_list_In in H2x0.
        assert (H2x0' := H2x0).
        rewrite elem_of_list_lookup in H2x0.
        destruct H2x0 as [j Hj].
        apply take_drop_middle in Hj.
        rewrite <- Hj.
        rewrite length_app.
        rewrite sum_list_with_app.
        rewrite map_app.
        rewrite sum_list_with_app.
        simpl.

        rewrite <- Hj in Hexactlyonce.
        rewrite map_app in Hexactlyonce. simpl in Hexactlyonce.
        rewrite concat_app in Hexactlyonce. simpl in Hexactlyonce.
        do 2 (rewrite filter_app in Hexactlyonce).
        do 2 (rewrite length_app in Hexactlyonce).
        simpl in Hexactlyonce.
        
        assert(Hnotintake: forall x2, x2 ∈ take j l -> h ∉ vars_of_to_l2r x2).
        {
            intros x2 Hx2.
            intros HContra.
            
            assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (take j l))))).
            {
                rewrite elem_of_list_lookup in Hx2.
                destruct Hx2 as [i0 Hx2].
                
                assert (Heq' := Hx2).
                apply take_drop_middle in Heq'.
                rewrite <- Heq'.
                rewrite map_app.
                rewrite concat_app.
                rewrite filter_app.
                simpl.
                rewrite filter_app.
                rewrite length_app.
                rewrite length_app.
                rewrite elem_of_list_lookup in HContra.
                destruct HContra as [k Hk].
                apply take_drop_middle in Hk.
                rewrite <- Hk.
                rewrite filter_app.
                rewrite length_app.
                rewrite filter_cons.
                destruct (decide (h = h))>[|ltac1:(contradiction)].
                simpl.
                ltac1:(lia).
            }
            apply take_drop_middle in Hi.
            rewrite <- Hi in Hexactlyonce.
            rewrite filter_app in Hexactlyonce.
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h=h))>[|ltac1:(contradiction)].
            rewrite length_app in Hexactlyonce.
            simpl in Hexactlyonce.
            unfold TermOver in *.
            ltac1:(lia).
        }

        assert(Hnotindrop: forall x2, x2 ∈ drop (S j) l -> h ∉ vars_of_to_l2r x2).
        {
            intros x2 Hx2.
            intros HContra.
            simpl in Hexactlyonce.
            assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (drop (S j) l))))).
            {
                rewrite elem_of_list_lookup in Hx2.
                destruct Hx2 as [i0 Hx2].
                
                assert (Heq' := Hx2).
                apply take_drop_middle in Heq'.
                rewrite <- Heq'.
                rewrite map_app.
                rewrite concat_app.
                rewrite filter_app.
                simpl.
                rewrite filter_app.
                rewrite length_app.
                rewrite length_app.
                rewrite elem_of_list_lookup in HContra.
                destruct HContra as [k Hk].
                apply take_drop_middle in Hk.
                rewrite <- Hk.
                rewrite filter_app.
                rewrite length_app.
                rewrite filter_cons.
                destruct (decide (h = h))>[|ltac1:(contradiction)].
                simpl.
                ltac1:(lia).
            }
            apply take_drop_middle in Hi.
            rewrite <- Hi in Hexactlyonce.
            rewrite filter_app in Hexactlyonce.
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h=h))>[|ltac1:(contradiction)].
            rewrite length_app in Hexactlyonce.
            simpl in Hexactlyonce.
            unfold TermOver in *.
            ltac1:(lia).
        }

        assert (HH1: (sum_list_with TermOver_size
                (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ)
                (take j l))  )
                = sum_list_with TermOver_size (take j l) ).
        {
            apply sum_list_with_eq_pairwise.
            {
                rewrite map_length.
                reflexivity.
            }
            {
                intros i0 x1 x2 Hx1 Hx2.
                ltac1:(replace map with (@fmap _ list_fmap) in Hx1 by reflexivity).
                rewrite list_lookup_fmap in Hx1.
                unfold TermOver in *.
                rewrite Hx2 in Hx1. simpl in Hx1. inversion Hx1; subst; clear Hx1.
                rewrite subst_notin.
                {
                    reflexivity.
                }
                {
                    intros HContra.
                    specialize (Hnotintake x2).
                    ltac1:(ospecialize (Hnotintake _)).
                    {
                        rewrite elem_of_list_lookup.
                        exists i0. exact Hx2.
                    }
                    apply Hnotintake. apply HContra.
                }
            }
        }

        assert (HH2: (sum_list_with TermOver_size
                (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ)
                (drop (S j) l))  )
                = sum_list_with TermOver_size (drop (S j) l) ).
        {
            apply sum_list_with_eq_pairwise.
            {
                rewrite map_length.
                reflexivity.
            }
            {
                intros i0 x1 x2 Hx1 Hx2.
                unfold TermOver in *.
                ltac1:(replace map with (@fmap _ list_fmap) in Hx1 by reflexivity).
                rewrite list_lookup_fmap in Hx1.
                rewrite Hx2 in Hx1. simpl in Hx1. inversion Hx1; subst; clear Hx1.
                rewrite subst_notin.
                {
                    reflexivity.
                }
                {

                    intros HContra.
                    specialize (Hnotindrop x2).
                    ltac1:(ospecialize (Hnotindrop _)).
                    {
                        rewrite elem_of_list_lookup.
                        exists i0. exact Hx2.
                    }
                    apply Hnotindrop. apply HContra.
                }
            }
        }
        unfold TermOver in *.
        rewrite HH1. clear HH1.
        rewrite HH2. clear HH2.
        remember (sum_list_with TermOver_size (take j l) ) as N1.
        remember (sum_list_with TermOver_size (drop (S j) l) ) as N2.
        rewrite length_take.
        rewrite length_drop.

        rewrite Forall_forall in H.
        specialize (H x0 H2x0' Hnotinψ).

        assert (Hnotintake': length (filter (eq h) (concat (map vars_of_to_l2r (take j l)))) = 0).
        {
            rewrite length_zero_iff_nil.
            apply list_filter_Forall_not.
            rewrite Forall_forall.
            intros x Hx HContra.
            subst x.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [x [H1x H2x]].
            rewrite in_map_iff in H1x.
            destruct H1x as [x1 [H1x1 H2x1]].
            rewrite <- elem_of_list_In in H2x.
            subst x.
            rewrite <- elem_of_list_In in H2x1.
            specialize (Hnotintake _ H2x1).
            apply Hnotintake. apply H2x.
        }

        assert (Hnotindrop': length (filter (eq h) (concat (map vars_of_to_l2r (drop (S j) l)))) = 0).
        {
            rewrite length_zero_iff_nil.
            apply list_filter_Forall_not.
            rewrite Forall_forall.
            intros x Hx HContra.
            subst x.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [x [H1x H2x]].
            rewrite in_map_iff in H1x.
            destruct H1x as [x1 [H1x1 H2x1]].
            rewrite <- elem_of_list_In in H2x.
            subst x.
            rewrite <- elem_of_list_In in H2x1.
            specialize (Hnotindrop _ H2x1).
            apply Hnotindrop. apply H2x.
        }
        unfold TermOver in *.
        specialize (H ltac:(lia)).
        rewrite H.
        assert (Htmp1 := TermOver_size_not_zero x0).
        unfold TermOver in *.
        rewrite length_app.
        simpl.
        rewrite length_drop.
        rewrite length_take.
        ltac1:(lia).
    }
Qed.


Lemma satisfies_TermOverBoV_to_TermOverExpr
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (γ : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    (nv : NondetValue)
    :
    satisfies ρ (program, (nv,γ)) (TermOverBoV_to_TermOverExpr2 φ)
    ->
    satisfies ρ γ φ
.
Proof.
    unfold TermOverBoV_to_TermOverExpr2, TermOver_map.
    revert γ.
    ltac1:(induction φ using TermOver_rect); intros γ.
    {
        simpl.
        intros H.
        {
            destruct a; simpl in *.
            {
                unfold satisfies in *; simpl in *.
                unfold TermOverBoV_to_TermOverExpr2 in H.
                simpl in *.
                ltac1:(simp sat2E in H).
                ltac1:(simp sat2B).
                simpl.
                ltac1:(case_match; try contradiction);
                    subst; simpl in *;
                    ltac1:(simplify_eq/=).
                reflexivity.  
            }
            {
                unfold satisfies in *; simpl in *.
                unfold TermOverBoV_to_TermOverExpr2 in H.
                simpl in *.
                ltac1:(simp sat2E in H).
                ltac1:(simp sat2B).
                simpl.
                ltac1:(case_match; try contradiction);
                    subst; simpl in *;
                    ltac1:(simplify_eq/=).
                ltac1:(case_match; try contradiction);
                    subst; simpl in *;
                    ltac1:(simplify_eq/=).
                inversion H; subst; clear H.
                reflexivity.
            }
        }
    }
    {
        intros HH.
        {
            simpl in HH.
            apply satisfies_term_expr_inv in HH.
            destruct HH as [lγ [[H1 H2] H3]].
            subst γ.
            unfold satisfies; simpl.
            ltac1:(simp sat2B).
            split>[reflexivity|].
            rewrite map_length in H2.
            unfold TermOver in *.
            split>[ltac1:(lia)|].
            intros.
            apply X.
            {
                rewrite elem_of_list_lookup.
                exists i. assumption.
            }
            eapply H3.
            { apply pf2. }
            {
                ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                rewrite list_lookup_fmap.
                rewrite pf1.
                simpl.      
                reflexivity.              
            }
        }
    }
Qed.



Equations? TermOverBoV_eval
    {Σ : StaticModel}
    (ρ : Valuation2)
    (φ : TermOver BuiltinOrVar)
    (pf : vars_of φ ⊆ vars_of ρ)
    : TermOver builtin_value
    by wf (TermOver_size φ) lt
:=

    TermOverBoV_eval ρ (t_over (bov_builtin b)) pf := t_over b
    ;

    TermOverBoV_eval ρ (t_over (bov_variable x)) pf with (inspect (ρ !! x)) => {
        | (@exist _ _ (Some t) pf') := t;
        | (@exist _ _ None pf') := _ ;
    }
    ;

    
    TermOverBoV_eval ρ (t_term s l) pf :=
        t_term s (pfmap l (fun φ' pf' => TermOverBoV_eval ρ φ' _))
    ;
.
Proof.
    {
        ltac1:(exfalso).        
        abstract(
            rewrite elem_of_subseteq in pf;
            specialize (pf x);
            unfold vars_of in pf; simpl in pf;
            unfold vars_of in pf; simpl in pf;
            unfold vars_of in pf; simpl in pf;
            rewrite elem_of_singleton in pf;
            specialize (pf eq_refl);
            unfold Valuation2 in *;
            rewrite elem_of_dom in pf;
            ltac1:(rewrite pf' in pf);
            eapply is_Some_None;
            apply pf
        ).
    }
    {
        unfold TermOver in *.
        intros. subst.
        apply elem_of_list_split in pf'.
        destruct pf' as [l1 [l2 Hl1l2]].
        subst l.
        rewrite vars_of_t_term in pf.
        rewrite fmap_app in pf. rewrite fmap_cons in pf.
        rewrite union_list_app_L in pf.
        rewrite union_list_cons in pf.
        ltac1:(set_solver).        
    }
    {
        intros. subst. simpl.
        apply elem_of_list_split in pf'.
        destruct pf' as [l1 [l2 Hl1l2]].
        subst l.
        rewrite sum_list_with_app.
        simpl.
        ltac1:(lia).
    }
Defined.


Lemma satisfies_TermOverBoV__impl__vars_subseteq
    {Σ : StaticModel}
    (ρ : Valuation2)
    (c : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    satisfies ρ c φ ->
    vars_of φ ⊆ vars_of ρ
.
Proof.
    revert ρ c.
    induction φ; intros ρ c HH.
    {
        unfold satisfies in HH; simpl in HH.
        ltac1:(simp sat2B in HH).
        destruct a; simpl in HH; subst.
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        rewrite elem_of_subseteq.
        intros x' Hx'.
        rewrite elem_of_singleton in Hx'.
        subst x'.
        unfold Valuation2 in *.
        rewrite elem_of_dom.
        exists (c).
        exact HH.
    }
    {
        unfold satisfies in HH; simpl in HH.
        destruct c; ltac1:(simp sat2B in HH).
        { destruct HH. }
        destruct HH as [HH1 [HH2 HH3]].
        unfold TermOver in *.
        rewrite vars_of_t_term.
        rewrite elem_of_subseteq.
        intros x Hx.
        rewrite elem_of_union_list in Hx.
        destruct Hx as [X [HX Hx]].
        rewrite elem_of_list_fmap in HX.
        destruct HX as [y [HX Hy]].
        subst X.
        apply elem_of_list_split in Hy.
        destruct Hy as [l1 [l2 Hy]].
        subst l.
        rewrite Forall_app in H.
        rewrite Forall_cons in H.
        destruct H as [H1 [H2 H3]].
        
        subst s0.
        destruct (l0 !! length l1) eqn:Heq.
        {
            specialize (HH3 (length l1) t y).
            rewrite lookup_app_r in HH3>[|unfold TermOver in *; ltac1:(lia)].
            rewrite Nat.sub_diag in HH3. simpl in HH3.
            specialize (HH3 erefl Heq).
            specialize (H2 _ _ HH3).
            clear -H2 Hx.
            ltac1:(set_solver).
        }
        {
            apply lookup_ge_None in Heq.
            rewrite length_app in HH2. simpl in HH2.
            unfold TermOver in *.
            ltac1:(lia).
        }
    }
Qed.


Lemma vars_of__TermOverBoV_subst__varless
    {Σ : StaticModel} c x v
    :
    vars_of v = ∅ ->
    vars_of (TermOverBoV_subst c x v) = vars_of c ∖ {[x]}
.
Proof.
    induction c; simpl in *; intros HH.
    {
        destruct a.
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            destruct (decide (x = x0)).
            {
                subst.
                ltac1:(set_solver).
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                ltac1:(set_solver).
            }
        }
    }
    {
        unfold TermOver in *.
        rewrite vars_of_t_term.
        rewrite vars_of_t_term.
        apply set_eq.
        revert HH H.
        induction l; intros HH H.
        {
            intros x0. simpl. ltac1:(set_solver).
        }
        {
            intros x0.
            specialize (IHl HH).
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            specialize (H1 HH).
            ltac1:(set_solver).
        }
    }
Qed.

Fixpoint TermOver'_option_map
    {T : Type} {A B : Type}
    (f : A -> option B)
    (t : @TermOver' T A)
    : option (@TermOver' T B)
:=
    match t with
    | t_over b => t_over <$> (f b)
    | t_term s l => t_term s <$> (list_collect ((TermOver'_option_map f) <$> l))
    end
.

Fixpoint TermOver'_leaves
    {T A : Type}
    {_EA : EqDecision A}
    {_CA : Countable A}
    (t : @TermOver' T A)
    :
    gset A
:=
    match t with
    | t_over a => singleton a
    | t_term _ l => union_list (TermOver'_leaves <$> l) 
    end
.

Lemma TermOver'_option_map__Some_1
    {T : Type}
    {A B : Type}
    {_EA : EqDecision A}
    {_CA : Countable A}
    (f : A -> option B)
    (t : @TermOver' T A)
    (t' : @TermOver' T B)
:
    TermOver'_option_map f t = Some t' ->
    forall (a : A),
        a ∈ TermOver'_leaves t ->
        exists (b : B),
            f a = Some b
.
Proof.
    revert t'.
    induction t; intros t' Ht'; simpl in *.
    {
        rewrite fmap_Some in Ht'.
        destruct Ht' as [x [H1x H2x]].
        subst t'.
        intros a' Ha'.
        rewrite elem_of_singleton in Ha'.
        subst a'.
        exists x.
        exact H1x.
    }
    {
        rewrite fmap_Some in Ht'.
        destruct Ht' as [l' [H1l' H2l']].
        subst t'.
        apply list_collect_inv in H1l'.
        clear l'.
        intros a Ha.
        rewrite elem_of_union_list in Ha.
        destruct Ha as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst X.
        rewrite Forall_forall in H.
        specialize (H _ H2y).
        rewrite Forall_forall in H1l'.
        unfold isSome in *.
        specialize (H1l' (TermOver'_option_map f y)).
        rewrite elem_of_list_fmap in H1l'.
        ltac1:(ospecialize (H1l' _)).
        {
            exists y.
            split>[|apply H2y].
            simpl.
            reflexivity.
        }
        destruct (TermOver'_option_map f y) eqn:Heq.
        {
            clear H1l'.
            specialize (H t erefl).
            specialize (H a H2X).
            exact H.
        }
        {
            inversion H1l'.
        }
    }
Qed.

Lemma TermOver'_option_map__extension
    {T : Type} {A B : Type}
    {_EA : EqDecision A}
    {_CA : Countable A}
    (f1 f2 : A -> option B)
    (ta : @TermOver' T A)
    (tb : @TermOver' T B)
:
    (forall a, a ∈ TermOver'_leaves ta -> isSome (f1 a) -> f2 a = f1 a) ->
    TermOver'_option_map f1 ta = Some tb ->
    TermOver'_option_map f2 ta = Some tb
.
Proof.
    revert tb.
    induction ta; intros tb HH1 HH2; simpl in *.
    {
        rewrite fmap_Some in HH2.
        rewrite fmap_Some.
        destruct HH2 as [x [H1x H2x]].
        subst tb.
        exists x.
        split>[|reflexivity].
        specialize (HH1 a).
        rewrite elem_of_singleton in HH1.
        specialize (HH1 eq_refl).
        unfold isSome in *.
        ltac1:(case_match; simplify_eq/=).
        specialize (HH1 eq_refl).
        exact HH1.
    }
    {
        rewrite fmap_Some.
        rewrite fmap_Some in HH2.
        destruct HH2 as [x [H1x H2x]].
        subst tb.
        exists x.
        split>[|reflexivity].
        clear s.
        revert x H1x H HH1.
        induction l;
            intros x H1x H HH1;
            simpl in *.
        {
            exact H1x.
        }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            rewrite bind_Some.
            rewrite bind_Some in H1x.
            destruct H1x as [y [H1y H2y]].
            rewrite bind_Some in H2y.
            destruct H2y as [z [H1z H2z]].
            apply (inj Some) in H2z.
            subst x.
            specialize (IHl _ H1z H2).
            clear H1z H2.
            simpl in *.
            exists y.
            rewrite bind_Some.
            split.
            {
                apply H1.
                intros a0 H1a0 H2a0.
                apply HH1.
                {
                    clear - H1a0.
                    ltac1:(set_solver).
                }
                {
                    apply H2a0.
                }
                {
                    apply H1y.
                }
            }
            {
                exists z.
                split>[|reflexivity].
                apply IHl.
                intros a0 H1a0 H2a0.
                apply HH1.
                {
                    clear - H1a0.
                    ltac1:(set_solver).
                }
                {
                    apply H2a0.
                }
            }
        }
    }
Qed.

Lemma TermOver'_option_map__extensional
    {T : Type} {A B : Type}
    {_EA : EqDecision A}
    {_CA : Countable A}
    (f1 f2 : A -> option B)
    (ta : @TermOver' T A)
:
    (forall a, a ∈ TermOver'_leaves ta -> (isSome (f1 a) -> f2 a = f1 a) /\ (isSome (f2 a) -> f1 a = f2 a)) ->
    TermOver'_option_map f1 ta = TermOver'_option_map f2 ta
.
Proof.
    intros H1.
    destruct (TermOver'_option_map f1 ta) eqn:Heq.
    {
        eapply TermOver'_option_map__extension in Heq.
        symmetry.
        apply Heq.
        apply H1.
    }
    {
        destruct (TermOver'_option_map f2 ta) eqn:Heq2.
        {
            ltac1:(exfalso).
            eapply TermOver'_option_map__extension in Heq2.
            {
                rewrite Heq in Heq2.
                inversion Heq2.
            }
            {
                apply H1.
            }
        }
        {
            reflexivity.
        }
    }
Qed.

Fixpoint try_neg
    {Σ : StaticModel}
    (sc : SideCondition)
    : option SideCondition
:= 
    match sc with
    | sc_true => Some sc_false
    | sc_false => Some sc_true
    | sc_and sc1 sc2 =>
        sc1' ← try_neg sc1;
        sc2' ← try_neg sc2;
        Some (sc_or sc1' sc2')
    | sc_or sc1 sc2 =>
        sc1' ← try_neg sc1;
        sc2' ← try_neg sc2;
        Some (sc_and sc1' sc2')
    | sc_atom p l =>
        if decide (length l = bps_ar p) then 
            p' ← bps_neg p;
            Some (sc_atom p' l)
        else None
    end
.

Lemma try_neg_sym
    {Σ : StaticModel}
    (sc sc' : SideCondition)
:
    try_neg sc = Some sc' ->
    try_neg sc' = Some sc
.
Proof.
    revert sc'.
    induction sc;
        intros sc' HH;
        simpl in *.
    {
        ltac1:(simplify_eq/=).
        reflexivity.
    }
    {
        ltac1:(simplify_eq/=).
        reflexivity.
    }
    {
        ltac1:(repeat case_match; simplify_option_eq).
        {
            rewrite bind_Some.
            ltac1:(exists pred).
            split>[|reflexivity].
            assert (Htmp := bps_neg__sym _ _ Heqo).
            ltac1:(congruence).
        }
        {
            assert (Htmp := bps_neg__sym _ _ Heqo).
            assert (Htmp2 := bps_neg_ar _ _ Heqo).
            ltac1:(lia).
        }
    }
    {
        ltac1:(repeat case_match; simplify_option_eq).
        {
            reflexivity.
        }
    }
    {
        ltac1:(repeat case_match; simplify_option_eq).
        {
            reflexivity.
        }
    }
Qed.
