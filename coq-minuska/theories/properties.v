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
    (gt : NondetValue -> TermOver builtin_value)
    :
    ρ1 ⊆ ρ2 ->
    Expression2_evaluate program ρ1 t = Some gt ->
    Expression2_evaluate program ρ2 t = Some gt.
Proof.
    intros Hρ1ρ2.
    revert gt.
    induction t; simpl; intros gt.
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
            apply functional_extensionality.
            intros _.
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
        injection H2x as H2x.
        apply list_collect_inv in H1x as H3x.
        assert (HSome : Forall isSome (Expression2_evaluate program ρ2 <$> l)).
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
        apply functional_extensionality.
        intros nv.
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
        assert (HSome : Forall isSome (Expression2_evaluate program ρ2 <$> l)).
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
        apply functional_extensionality.
        intros nv.
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
    (ng : NondetValue -> TermOver builtin_value)
:
    Expression2_evaluate program ρ e = Some ng ->
    ( vars_of e ⊆ vars_of ρ )
.
Proof.
    revert ng.
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
        exists t. assumption.
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

Lemma Expression2_evaluate_Some_enough_inv
    {Σ : StaticModel}
    (program : ProgramT)
    (e : Expression2)
    (ρ : Valuation2)
    :
    vars_of e ⊆ vars_of ρ ->
    { g : _ & Expression2_evaluate program ρ e = Some g }
.
Proof.
    induction e; intros Hsub.
    {
        simpl. exists (fun _ => e).
        reflexivity.
    }
    {
        simpl.
        ltac1:(case_match).
        {
            exists (fun _ => t).
            reflexivity.
        }
        {
            ltac1:(exfalso).
            unfold vars_of in Hsub; simpl in Hsub.
            rewrite elem_of_subseteq in Hsub.
            specialize (Hsub x ltac:(set_solver)).
            unfold Valuation2 in *.
            rewrite elem_of_dom in Hsub.
            rewrite H in Hsub.
            unfold is_Some in Hsub.
            destruct Hsub as [y Hy].
            inversion Hy.
        }
    }
    {
        simpl.
        assert (H1 : Forall isSome (Expression2_evaluate program ρ <$> l)).
        {
            rewrite Forall_fmap.
            rewrite Forall_forall.
            intros e He.
            specialize (X e He).
            simpl.
            unfold isSome.
            ltac1:(case_match).
            { reflexivity. }
            ltac1:(exfalso).
            unfold vars_of in Hsub; simpl in Hsub.
            ltac1:(ospecialize (X _)).
            {
                clear X.
                rewrite elem_of_subseteq in Hsub.
                rewrite elem_of_subseteq.
                intros x Hx.
                specialize (Hsub x).
                rewrite elem_of_union_list in Hsub.
                ltac1:(ospecialize (Hsub _)).
                {
                    clear Hsub.
                    exists (vars_of e).
                    rewrite elem_of_list_fmap.
                    split>[|assumption].
                    exists e.
                    split>[|assumption].
                    reflexivity.
                }
                exact Hsub.
            }
            destruct X as [g Hcontra].
            inversion Hcontra.
        }
        apply list_collect_Forall_T in H1.
        destruct H1 as [l_out [H1l_out H2l_out]].
        rewrite H1l_out. simpl.
        eexists. reflexivity.
    }
    {
        simpl.
        assert (H1 : Forall isSome (Expression2_evaluate program ρ <$> l)).
        {
            rewrite Forall_fmap.
            rewrite Forall_forall.
            intros e He.
            specialize (X e He).
            simpl.
            unfold isSome.
            ltac1:(case_match).
            { reflexivity. }
            ltac1:(exfalso).
            unfold vars_of in Hsub; simpl in Hsub.
            ltac1:(ospecialize (X _)).
            {
                clear X.
                rewrite elem_of_subseteq in Hsub.
                rewrite elem_of_subseteq.
                intros x Hx.
                specialize (Hsub x).
                rewrite elem_of_union_list in Hsub.
                ltac1:(ospecialize (Hsub _)).
                {
                    clear Hsub.
                    exists (vars_of e).
                    rewrite elem_of_list_fmap.
                    split>[|assumption].
                    exists e.
                    split>[|assumption].
                    reflexivity.
                }
                exact Hsub.
            }
            destruct X as [g Hcontra].
            inversion Hcontra.
        }
        apply list_collect_Forall_T in H1.
        destruct H1 as [l_out [H1l_out H2l_out]].
        rewrite H1l_out. simpl.
        eexists. reflexivity.
    }
Qed.

Lemma TermOverExpression2_evalute_total_2
    {Σ : StaticModel}
    (program : ProgramT)
    (t : TermOver Expression2)
    (ρ : Valuation2)
    (nv : NondetValue)
    :
    ( vars_of t ⊆ vars_of ρ ) ->
    {e : TermOver builtin_value & sat2E program ρ e t nv}
.
Proof.
    revert ρ.
    ltac1:(induction t using TermOver_rect; intros ρ Hρ).
    {
        unfold vars_of in Hρ; simpl in Hρ.
        apply Expression2_evaluate_Some_enough_inv with (program := program) in Hρ.
        destruct Hρ as [g Hg].
        exists (g nv).
        ltac1:(simp sat2E).
        rewrite Hg.
        reflexivity.
    }
    {
        unfold Valuation2,TermOver in *.
        rewrite vars_of_t_term_e in Hρ.
        assert(X' : forall ρ0 x, x ∈ l -> vars_of x ⊆ vars_of ρ0 -> {e : TermOver' builtin_value & sat2E program ρ0 e x nv}).
        {
            ltac1:(naive_solver).
        }
        clear X.
        specialize (X' ρ).
        assert(X'' : forall x, x ∈ l -> {e : TermOver' builtin_value & sat2E program ρ e x nv}).
        {
            intros. apply X'. assumption.
            rewrite elem_of_subseteq in Hρ.
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            specialize (Hρ x0).
            apply Hρ.
            rewrite elem_of_union_list.
            exists (vars_of x).
            rewrite elem_of_list_fmap.
            split>[|assumption].
            exists x.
            split>[reflexivity|].
            exact H.
        }
        clear X'.
        remember (pfmap l (fun x pf => projT1 (X'' x pf))) as l'.
        exists (t_term b l').
        ltac1:(simp sat2E).
        split>[reflexivity|].
        subst l'.
        split.
        {
            rewrite length_pfmap. reflexivity.
        }
        {
            intros i t' φ' Hli Hpf.
            apply lookup_lt_Some in Hli as Hli'.
            unfold TermOver in *.
            rewrite <- (pflookup_spec l i Hli') in Hli.
            injection Hli as Hli.
            rewrite <- Hli.
            lazy_match! goal with
            | [|- sat2E _ _ _ (` ?p) _] => pose(p := $p)
            end.
            assert (HH2 := pfmap_lookup_Some_1 l (λ (x : TermOver' Expression2) (pf : x ∈ l), projT1 (X'' x pf)) i  t' Hpf).
            simpl in HH2.
            pose (Hp := proj2_sig p).
            pose (Xp := X'' (proj1_sig p) Hp).
            ltac1:(unfold Hp in Xp). clear Hp.
            ltac1:(fold p).
            assert (HH := projT2 Xp). simpl in HH.
            rewrite HH2.
            ltac1:(unfold Xp in HH).
            ltac1:(unfold p in HH).
            ltac1:(unfold p).
            ltac1:(replace (pfmap_lookup_Some_lt Hpf) with (Hli')).
            {
                exact HH.
            }
            {
                apply proof_irrelevance.
            }
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
    (g : NondetValue -> TermOver builtin_value)
    (ρ : Valuation2)
:
    Expression2_evaluate program ρ e = Some g ->
    Expression2_evaluate program (filter (fun kv => kv.1 ∈ vars_of e) ρ) e = Some g
.
Proof.
    intros HH.
    apply Expression2_evaluate_total_1 in HH as HH1.
    assert (HH2 : vars_of e ⊆ vars_of (filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ vars_of e) ρ)).
    {
        unfold Valuation2 in *.
        unfold vars_of; simpl.
        rewrite elem_of_subseteq.
        intros x Hx.
        ltac1:(rewrite elem_of_dom).
        unfold vars_of in HH1, Hx; simpl in HH1,Hx.
        rewrite elem_of_subseteq in HH1.
        specialize (HH1 _ Hx).
        ltac1:(rewrite elem_of_dom in HH1).
        destruct HH1 as [y Hy].
        exists y.
        unfold Valuation2 in *.
        apply map_lookup_filter_Some_2.
        exact Hy.
        simpl.
        apply Hx.
    }
    apply Expression2_evaluate_Some_enough_inv with (program := program) in HH2 as HH3.
    destruct HH3 as [g0 Hg0].
    eapply Expression2_evaluate_extensive_Some with (ρ2 := ρ) in Hg0 as H1g0.
    {
        assert (g = g0) by ltac1:(congruence).
        subst g0.
        apply Hg0.
    }
    {
        unfold Valuation2 in *.
        apply map_filter_subseteq.
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
    :
    ρ1 ⊆ ρ2 ->
    satisfies ρ1 (program, nv) c ->
    satisfies ρ2 (program, nv) c
.
Proof.
    induction c.
    {
        intros Hrhos.
        unfold satisfies; simpl.
        intros HH.
        unfold SideCondition_evaluate in *.
        ltac1:(repeat case_match); try (solve [ltac1:(contradiction)]).
        {
            assert (l0 = l).
            {
                clear HH.
                ltac1:(rename pred into p).
                revert l l0 H H0.
                simpl.
                clear p.
                induction args; intros l1 l2 H1 H2.
                {
                    simpl in *. ltac1:(simplify_eq/=). reflexivity.
                }
                {
                    simpl in *.
                    rewrite bind_Some in H1.
                    rewrite bind_Some in H2.
                    destruct H1 as [x1 [H1x1 H2x1]].
                    destruct H2 as [x2 [H1x2 H2x2]].
                    rewrite bind_Some in H2x1.
                    rewrite bind_Some in H2x2.
                    destruct H2x1 as [ll1 [H1ll1 H2ll1]].
                    destruct H2x2 as [ll2 [H1ll2 H2ll2]].
                    simpl in *.
                    ltac1:(simplify_eq/=).
                    eapply Expression2_evaluate_extensive_Some in H1x1.
                    {
                        rewrite H1x1 in H1x2.
                        ltac1:(simplify_eq/=).
                        f_equal.
                        apply IHargs; assumption.
                    }
                    {
                        assumption.
                    }
                }
            }
            rewrite H1.
            exact HH.
        }
        {
            clear HH.
            revert l H H0.
            ltac1:(rename pred into p).
            induction args; intros l HH1 HH2; simpl in *.
            {
                ltac1:(simplify_eq/=).
            }
            {
                simpl in *.
                rewrite bind_Some in HH1.
                rewrite bind_None in HH2.
                destruct HH1 as [x1 [H1x1 H2x1]].
                rewrite bind_Some in H2x1.
                destruct H2x1 as [ll1 [H1ll1 H2ll1]].
                simpl in *.
                ltac1:(simplify_eq/=).
                destruct HH2 as [HH2|HH2].
                {
                    eapply Expression2_evaluate_extensive_Some in H1x1.
                    {
                        rewrite H1x1 in HH2.
                        inversion HH2.
                    }
                    { assumption. }
                }
                {
                    destruct HH2 as [x2 [H1x2 H2x2]].
                    rewrite bind_None in H2x2.
                    specialize (IHargs _ H1ll1).
                    destruct H2x2 as [H2x2 | H2x2].
                    {
                        exact (IHargs H2x2).
                    }
                    {
                        destruct H2x2 as [x [H1x H2x]].
                        inversion H2x.
                    }
                }
            }
        }
        {
            inversion HH.
        }
        {
            inversion HH.
        }
    }
    {
        intros Hrhos.
        unfold satisfies; simpl.
        intros HH.
        apply andb_prop in HH.
        destruct HH as [HH1 HH2].
        specialize (IHc1 Hrhos).
        specialize (IHc2 Hrhos).
        specialize (IHc1 HH1).
        specialize (IHc2 HH2).
        unfold satisfies in IHc1; simpl in IHc1.
        unfold satisfies in IHc2; simpl in IHc2.
        rewrite IHc1.
        rewrite IHc2.
        reflexivity.
    }
    {
        intros Hrhos.
        unfold satisfies; simpl.
        intros HH.
        apply orb_prop in HH.
        destruct HH as [HH1|HH2].
        {
            specialize (IHc1 Hrhos).
            specialize (IHc1 HH1).
            unfold satisfies in IHc1; simpl in IHc1.
            rewrite IHc1.
            reflexivity.
        }
        {
            specialize (IHc2 Hrhos).    
            specialize (IHc2 HH2).
            unfold satisfies in IHc2; simpl in IHc2.
            rewrite IHc2.
            rewrite orb_true_r.
            reflexivity.
        }
    }
Qed.

Lemma SideCondition_satisfies_strip
    {Σ : StaticModel}
    (program : ProgramT)
    (c : SideCondition)
    (ρ : Valuation2)
    (nv : NondetValue)
:
    satisfies ρ (program, nv) c ->
    satisfies (filter (fun kv => kv.1 ∈ vars_of c) ρ) (program, nv) c
.
Proof.
    revert ρ.
    induction c; intros ρ.
    {
        unfold satisfies; simpl.
        intros HH.

        unfold SideCondition_evaluate in *.

        ltac1:(repeat case_match).
        {
            assert (Htmp: l0 = l).
            {
                ltac1:(rename pred into p).
                clear HH.
                revert l l0 H H0.
                induction args; intros l1 l2 H1 H2; simpl in *.
                {
                    ltac1:(simplify_eq/=).
                    reflexivity.
                }
                {
                    rewrite bind_Some in H1.
                    rewrite bind_Some in H2.
                    destruct H1 as [x1 [H1x1 H2x1]].
                    destruct H2 as [x2 [H1x2 H2x2]].
                    rewrite bind_Some in H2x1.
                    rewrite bind_Some in H2x2.
                    destruct H2x1 as [y1 [H1y1 H2y1]].
                    destruct H2x2 as [y2 [H1y2 H2y2]].
                    ltac1:(simplify_eq/=).
                    simpl in *.
                    f_equal.
                    {
                        apply Expression2_evalute_strip in H1x1.
                        eapply Expression2_evaluate_extensive_Some in H1x1.
                        rewrite H1x1 in H1x2.
                        {
                            ltac1:(simplify_eq/=). reflexivity.
                        }
                        ltac1:(simplify_eq/=).
                        ltac1:(rewrite map_subseteq_spec).
                        intros v t Hvt.
                        ltac1:(rewrite map_lookup_filter).
                        ltac1:(rewrite map_lookup_filter in Hvt).
                        rewrite bind_Some in Hvt.
                        rewrite bind_Some.
                        destruct Hvt as [g [H1g H2g]].
                        ltac1:(simplify_option_eq).
                        {
                            exists t.
                            split>[assumption|reflexivity].
                        }
                        {
                            unfold vars_of in H1; simpl in H1.
                            unfold vars_of in H1; simpl in H1.
                            clear - H0 H1.
                            ltac1:(set_solver).
                        }
                    }
                    {
                        symmetry.
                        assert(HH2: Forall (λ u : option (NondetValue → TermOver builtin_value), u)
                                (list_fmap Expression2 (option (NondetValue → TermOver builtin_value))
                                (Expression2_evaluate program
                                (filter
                                (λ kv : variable * TermOver builtin_value,
                                kv.1 ∈ vars_of args)
                                ρ))
                                args) 
                            ).
                        {
                            apply list_collect_inv in H1y2.
                            rewrite Forall_forall.
                            rewrite Forall_forall in H1y2.
                            intros o Ho.
                            specialize (H1y2 o).
                            apply H1y2.
                            clear H1y2.
                            rewrite elem_of_list_fmap.
                            rewrite elem_of_list_fmap in Ho.
                            destruct Ho as [e [He1 He2]].
                            exists e.
                            split>[|exact He2].
                            
                            destruct o.
                            {
                                symmetry in He1.
                                symmetry.
                                eapply Expression2_evaluate_extensive_Some in He1.
                                apply He1.
                                ltac1:(rewrite map_subseteq_spec).
                                intros v' t' Hv't'.
                                ltac1:(rewrite map_lookup_filter).
                                ltac1:(rewrite map_lookup_filter in Hv't').
                                rewrite bind_Some in Hv't'.
                                rewrite bind_Some.
                                destruct Hv't' as [g [H1g H2g]].
                                ltac1:(simplify_option_eq).
                                {
                                    exists t'.
                                    split>[assumption|reflexivity].
                                }
                                {
                                    ltac1:(exfalso).
                                    apply H1. clear H1.
                                    unfold vars_of; simpl.
                                    unfold vars_of; simpl.
                                    unfold vars_of in H; simpl in H.
                                    unfold vars_of in H; simpl in H.
                                    clear -H.
                                    ltac1:(set_solver).
                                }
                            }
                            {
                                ltac1:(exfalso).
                                clear - He1 He2 H1y1.
                                apply list_collect_inv in H1y1.
                                rewrite Forall_fmap in H1y1.
                                rewrite Forall_forall in H1y1.
                                specialize (H1y1 e He2).
                                simpl in H1y1.
                                unfold isSome in H1y1.
                                destruct (Expression2_evaluate program ρ e) eqn:Heq.
                                {
                                    symmetry in He1.
                                    eapply eq_None_ne_Some_1 with (x := t) in He1.
                                    apply He1. clear He1.
                                    eapply Expression2_evalute_strip in Heq.
                                    eapply Expression2_evaluate_extensive_Some in Heq.
                                    apply Heq.
                                    ltac1:(rewrite map_subseteq_spec).
                                    intros x g Hxg.
                                    ltac1:(rewrite map_lookup_filter in Hxg).
                                    ltac1:(rewrite map_lookup_filter).
                                    rewrite bind_Some in Hxg.
                                    rewrite bind_Some.
                                    destruct Hxg as [g' [Hg' H'g']].
                                    ltac1:(simplify_option_eq).
                                    {
                                        exists g.
                                        split>[assumption|reflexivity].
                                    }
                                    {
                                        ltac1:(exfalso).
                                        apply H1. clear H1.
                                        unfold vars_of; simpl.
                                        unfold vars_of; simpl.
                                        rewrite elem_of_union_list.
                                        exists (vars_of e).
                                        rewrite elem_of_list_fmap.
                                        split>[|assumption].
                                        exists e.
                                        split>[reflexivity|exact He2].
                                    }
                                }
                                {
                                    inversion H1y1.
                                }
                            }
                        }
                        
                        apply IHargs.
                        {
                            apply list_collect_Forall in HH2 as HH2'.
                            destruct HH2' as [l_out [H1l_out H2l_out]].    
                            simpl in *.
                            clear IHargs.
                            clear H1x2.
                            rewrite <- H1y2.
                            apply f_equal.
                            apply list_eq.
                            intros i.
                            rewrite list_lookup_fmap.
                            rewrite list_lookup_fmap.
                            destruct (args !! i) eqn:Hi; simpl in *.
                            {
                                apply f_equal.
                                destruct (Expression2_evaluate program ρ e) eqn:Heq; simpl in *.
                                {
                                    apply Expression2_evalute_strip in Heq.
                                    eapply Expression2_evaluate_extensive_Some in Heq.
                                    symmetry.
                                    apply Heq.
                                    ltac1:(rewrite map_subseteq_spec).
                                    intros i0 g Hg.
                                    ltac1:(rewrite map_lookup_filter in Hg).
                                    ltac1:(rewrite map_lookup_filter).
                                    rewrite bind_Some in Hg.
                                    rewrite bind_Some.
                                    destruct Hg as [x [H1x H2x]].
                                    ltac1:(simplify_option_eq).
                                    {
                                        exists g.
                                        split>[assumption|reflexivity].
                                    }
                                    {
                                        ltac1:(exfalso).
                                        apply H1. clear H1.
                                        unfold vars_of; simpl.
                                        unfold vars_of; simpl.
                                        rewrite elem_of_union.
                                        right.
                                        apply take_drop_middle in Hi.
                                        rewrite <- Hi.
                                        rewrite fmap_app.
                                        rewrite union_list_app.
                                        rewrite elem_of_union.
                                        right.
                                        rewrite fmap_cons.
                                        rewrite union_list_cons.
                                        rewrite elem_of_union.
                                        left.
                                        assumption.
                                    }
                                }
                                {
                                    ltac1:(exfalso).
                                    apply list_collect_inv in H1y2.
                                    apply list_collect_inv in H1l_out.
                                    rewrite Forall_fmap in H1y2.
                                    rewrite Forall_fmap in H1l_out.
                                    apply take_drop_middle in Hi.
                                    rewrite <- Hi in H1y2.
                                    rewrite Forall_app in H1y2.
                                    rewrite Forall_cons in H1y2.
                                    destruct H1y2 as [_ [HContra _]].
                                    simpl in HContra.
                                    unfold isSome in HContra.
                                    ltac1:(case_match).
                                    {
                                        clear HContra.
                                        eapply Expression2_evaluate_extensive_Some in H.
                                        rewrite H in Heq.
                                        inversion Heq.
                                        unfold Valuation2 in *.
                                        apply map_filter_subseteq.
                                    }
                                    {
                                        inversion HContra.
                                    }
                                }
                            }
                            {
                                reflexivity.
                            }
                        }
                        {
                            unfold fmap.
                            rewrite <- H1y1.


                            apply list_collect_Forall in HH2 as HH2'.
                            destruct HH2' as [l_out [H1l_out H2l_out]].
                            apply f_equal.
                            apply list_eq.
                            intros i.
                            rewrite list_lookup_fmap.
                            rewrite list_lookup_fmap.
                            destruct (args !! i) eqn:Hai; simpl in *.
                            {
                                apply f_equal.
                                apply take_drop_middle in Hai.
                                rewrite Forall_fmap in HH2.
                                rewrite <- Hai in HH2.
                                rewrite Forall_app in HH2.
                                rewrite Forall_cons in HH2.
                                destruct HH2 as [_ [Hmy _]].
                                unfold isSome in Hmy. simpl in Hmy.
                                ltac1:(case_match)>[|inversion Hmy].
                                clear Hmy.
                                rewrite <- Hai.
                                (* rewrite H. *)
                                symmetry.
                                eapply Expression2_evaluate_extensive_Some in H as H'1.
                                {
                                    rewrite H'1.
                                    eapply Expression2_evaluate_extensive_Some in H as H'2.
                                    {
                                        rewrite H'2.
                                        reflexivity.
                                    }
                                    {
                                        ltac1:(rewrite /(@vars_of SideCondition variable _ _ _)/=).
                                        unfold Valuation2 in *.
                                        apply reflexivity.
                                    }
                                }
                                {
                                    unfold Valuation2 in *.
                                    apply map_filter_subseteq.
                                }
                            }
                            {
                                reflexivity.
                            }
                        }
                    }
                }
            }
            rewrite Htmp. clear Htmp.
            apply HH.
        }

        {
            clear HH.
            (* apply list_collect_inv in H as H'.
            rewrite Forall_fmap in H'. *)
            apply eq_None_ne_Some_1 with (x := l) in H0.
            ltac1:(exfalso).
            apply H0. clear H0.
            
            revert l H.
            induction args; simpl; intros l HH.
            {
                assumption.
            }
            {
                rewrite bind_Some in HH.
                rewrite bind_Some.
                destruct HH as [x [H1x H2x]].
                rewrite bind_Some in H2x.
                destruct H2x as [x0 [H1x0 H2x0]].
                ltac1:(simplify_eq/=).
                specialize (IHargs _ H1x0).
                exists x.
                split.
                {
                    apply Expression2_evalute_strip in H1x.
                    eapply Expression2_evaluate_extensive_Some in H1x.
                    rewrite H1x.
                    reflexivity.
                    unfold Valuation2 in *.
                    ltac1:(rewrite map_subseteq_spec).
                    intros i x1 Hix1.
                    rewrite map_lookup_filter in Hix1.
                    rewrite map_lookup_filter.
                    rewrite bind_Some in Hix1.
                    destruct Hix1 as [x2 [H1x2 H2x2]].
                    rewrite bind_Some.
                    ltac1:(simplify_option_eq).
                    {
                        exists x1.
                        split>[assumption|reflexivity].
                    }
                    {
                        ltac1:(exfalso).
                        apply H1. clear H1.
                        unfold vars_of; simpl.
                        unfold vars_of; simpl.
                        rewrite elem_of_union.
                        left. assumption.
                    }
                }
                {
                    rewrite bind_Some.
                    exists x0.
                    split>[|reflexivity].
                    apply list_collect_inv in IHargs as IHargs'.
                    rewrite Forall_fmap in IHargs'.
                    rewrite <- IHargs.
                    apply f_equal.
                    apply list_eq.
                    intros i.
                    do 2 (rewrite list_lookup_fmap).
                    destruct (args !! i) eqn:Hai.
                    {
                        simpl.
                        apply f_equal.
                        apply take_drop_middle in Hai.
                        rewrite <- Hai in IHargs'.
                        rewrite Forall_app in IHargs'.
                        rewrite Forall_cons in IHargs'.
                        destruct IHargs' as [_ [Hmy _]].
                        simpl in Hmy.
                        unfold isSome in Hmy.
                        ltac1:(case_match)>[|inversion Hmy].
                        clear Hmy.
                        rewrite Hai in H.
                        rewrite H.
                        eapply Expression2_evaluate_extensive_Some in H.
                        apply H.
                        unfold Valuation2 in *.
                        ltac1:(rewrite map_subseteq_spec).
                        intros i0 x1 HHH.
                        rewrite map_lookup_filter in HHH.
                        rewrite map_lookup_filter.
                        rewrite bind_Some in HHH.
                        rewrite bind_Some.
                        destruct HHH as [x2 [H1x2 H2x2]].
                        ltac1:(simplify_option_eq).
                        {
                            exists x1.
                            split>[assumption|reflexivity].
                        }
                        {
                            ltac1:(exfalso).
                            apply H2. clear H2.
                            unfold vars_of; simpl.
                            unfold vars_of; simpl.
                            unfold vars_of in H1; simpl in H1.
                            rewrite elem_of_union.
                            right. assumption.
                        }
                    }
                    {
                        reflexivity.
                    }
                }
            }
        }
        {
            inversion HH.
        }
        {
            inversion HH.
        }
    }
    {
        intros HH. unfold satisfies in HH; simpl in HH.
        apply andb_prop in HH. destruct HH as [HH1 HH2].
        specialize (IHc1 ρ HH1).
        specialize (IHc2 ρ HH2).
        unfold satisfies; simpl.
        rewrite andb_true_iff.
        split.
        {
            eapply SideCondition_satisfies_extensive>[|apply IHc1].
            unfold vars_of; simpl.
            clear.
            unfold Valuation2 in *.
            ltac1:(rewrite map_filter_subseteq_ext).
            intros i x Hix H1.
            simpl in *.
            rewrite elem_of_union.
            left.
            exact H1.
        }
        {
            eapply SideCondition_satisfies_extensive>[|apply IHc2].
            unfold vars_of; simpl.
            clear.
            unfold Valuation2 in *.
            ltac1:(rewrite map_filter_subseteq_ext).
            intros i x Hix H2.
            simpl in *.
            rewrite elem_of_union.
            right.
            exact H2.
        }
    }
    {
        intros HH. unfold satisfies in HH; simpl in HH.
        apply orb_prop in HH.
        unfold satisfies; simpl.
        rewrite orb_true_iff.
        destruct (decide (SideCondition_evaluate program ρ nv c1 = true)) as [Heq|Hneq].
        {
            specialize (IHc1 ρ Heq).
            left.
            eapply SideCondition_satisfies_extensive>[|apply IHc1].
            unfold vars_of; simpl.
            clear.
            unfold Valuation2 in *.
            ltac1:(rewrite map_filter_subseteq_ext).
            intros i x Hix H1.
            simpl in *.
            rewrite elem_of_union.
            left.
            exact H1.
        }
        {
            right.
            unfold satisfies in IHc2; simpl in IHc2.
            specialize (IHc2 ρ ltac:(naive_solver)).
            eapply SideCondition_satisfies_extensive>[|apply IHc2].
            unfold vars_of; simpl.
            clear.
            unfold Valuation2 in *.
            ltac1:(rewrite map_filter_subseteq_ext).
            intros i x Hix H2.
            simpl in *.
            rewrite elem_of_union.
            right.
            exact H2.
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
