From Minuska Require Import
    prelude
    spec
    lowlang
    properties
    syntax_properties
    semantics_properties
    spec_lowlang_interpreter
    spec_interpreter
    basic_matching
.


Lemma wf2'_impl_wf2
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    :
    RewritingRule_wf2' r -> 
    RewritingRule_wf2 r
.
Proof.
    intros H.
    unfold RewritingRule_wf2' in H.
    unfold RewritingRule_wf2.
    intros g ρ Hfrom Hscs.
    clear Hscs.
    
    apply satisfies_matchesb in Hfrom.
    apply matchesb_vars_of in Hfrom.
    assert (Hvtρ : vars_of (fr_to r) ⊆ vars_of ρ).
    {
        eapply transitivity>[apply H|]. apply Hfrom.
    }
    clear H Hfrom.
    remember (fr_to r) as to.
    destruct to as [ao|e].
    {
        ltac1:(cut ({ g'' : PreTerm' symbol builtin_value & satisfies ρ g'' ao})).
        {
            intros [g'' Hg''].
            eexists. econstructor. apply Hg''.
        }
        clear Heqto.
        unfold vars_of in Hvtρ at 1; simpl in Hvtρ.
        induction ao; unfold vars_of in Hvtρ at 1; simpl in Hvtρ.
        {
            eexists. econstructor.
        }
        {
            specialize (IHao ltac:(set_solver)).
            destruct IHao as [g'' Hg''].
            assert (HH: vars_of b ⊆ vars_of ρ) by ltac1:(set_solver).
            apply Expression_evalute_total_T_2 in HH.
            destruct HH as [g''' Hg'''].
            destruct g'''.
            {
                exists (pt_app_ao g'' ao0).
                constructor; assumption.
            }
            {
                eexists. econstructor. apply Hg''.
                unfold satisfies; simpl.
                rewrite Hg'''. reflexivity.
            }
        }
        {
            specialize (IHao1 ltac:(set_solver)).
            specialize (IHao2 ltac:(set_solver)).
            destruct IHao1 as [g1 Hg1].
            destruct IHao2 as [g2 Hg2].
            eexists. econstructor; ltac1:(eassumption).
        }
    }
    {
        unfold vars_of in Hvtρ at 1. simpl in Hvtρ.
        apply Expression_evalute_total_T_2 in Hvtρ.
        destruct Hvtρ as [g' Hg'].
        exists g'.
        apply matchesb_satisfies.
        unfold matchesb; simpl.
        unfold ApppliedOperatorOr'_matches_Term'.
        destruct g'; unfold matchesb; simpl.
        {
            rewrite Hg'. apply bool_decide_eq_true. reflexivity.
        }
        {
            rewrite Hg'. apply bool_decide_eq_true. reflexivity.
        }
    }
Qed.

(*
#[export]
Instance RewritingRule_wf1_dec
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    :
    Decision (RewritingRule_wf1 r)
.
Proof.
    unfold RewritingRule_wf1.
    apply _.
Defined.


#[export]
Instance RewritingRule_wf2'_dec
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    :
    Decision (RewritingRule_wf2' r)
.
Proof.
    unfold RewritingRule_wf2'.
    apply _.
Defined.
*)

Definition RewritingRule_wf2_heuristics
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    :
    option (RewritingRule_wf2 r)
.
Proof.
    eapply option_map.
    { apply wf2'_impl_wf2. }
    unfold RewritingRule_wf2'.
    destruct (decide (vars_of (fr_to r) ⊆ (vars_of (fr_from r)))) as [H|H].
    {
        exact (Some H).
    }
    exact None.
Defined.

Definition RewritingRule_wf_heuristics
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    : option (RewritingRule_wf r)
.
Proof.
    unfold RewritingRule_wf.
    destruct (decide (vars_of (fr_scs r) ⊆ (vars_of (fr_from r)))) as [H|H].
    {

        assert (H2 := RewritingRule_wf2_heuristics r).
        unfold RewritingRule_wf1.
        destruct H2 as [H2|].
        {
            exact (Some (H, H2)).
        }
        exact None.
    }
    exact None.
Defined.

Definition RewritingTheory_wf_heuristics
    {Σ : StaticModel}
    {Act : Set}
    {_dAct : EqDecision Act}
    (Γ : RewritingTheory Act)
    : option (RewritingTheory_wf Γ)
.
Proof.
    unfold RewritingTheory_wf.
    induction Γ.
    {
        apply Some.
        intros r Hr.
        rewrite elem_of_nil in Hr.
        inversion Hr.
    }
    {
        destruct IHΓ as [IHΓ|].
        {
            assert (H := RewritingRule_wf_heuristics a).
            destruct H as [H|].
            {
                apply Some.
                intros r Hr.
                split.
                {
                    destruct (decide (r = a)).
                    {
                        subst. apply H.

                    }
                    {
                        assert (r ∈ Γ) by (ltac1:(set_solver)).
                        apply IHΓ; assumption.
                    }
                }
                {
                    destruct (decide (r = a)).
                    {
                        subst. apply H.

                    }
                    {
                        assert (r ∈ Γ) by (ltac1:(set_solver)).
                        apply IHΓ; assumption.
                    }
                }
            }
            exact None.
        }
        exact None.
    }
Defined.


Lemma vars_of_Expression2_to_Expression
    {Σ : StaticModel}
    (e : Expression2)
    :
    vars_of (Expression2_to_Expression e)
    = vars_of e
.
Proof.
    unfold vars_of; simpl.
    induction e; simpl; ltac1:(set_solver).
Qed.


Definition RewritingTheory2_wf_heuristics
    {Σ : StaticModel}
    {Act : Set}
    {_dAct : EqDecision Act}
    (Γ : RewritingTheory2 Act)
    : option (RewritingTheory2_wf Γ)
.
Proof.
    unfold RewritingTheory2 in *.
    remember (fmap r_to_fr Γ) as Γ'.
    assert (Hdec := RewritingTheory_wf_heuristics Γ').
    destruct Hdec eqn:Heq.
    {
        apply Some.
        unfold RewritingTheory_wf in r.
        assert (Hr': ∀ r0, r0 ∈ Γ -> RewritingRule2_wf r0).
        {
            intros r0 Hr0.
            clear Heq.
            specialize (r (r_to_fr r0)).
            
            ltac1:(ospecialize (r _)).
            {
                subst Γ'.
                rewrite elem_of_list_fmap.
                exists r0.
                split>[reflexivity|exact Hr0].
            }
            unfold RewritingRule2_wf.
            unfold RewritingRule_wf in r.
            destruct r as [H1 H2].
            split.
            {
                unfold RewritingRule_wf1 in H1.
                unfold RewritingRule2_wf1.
                clear -H1.
                rewrite elem_of_subseteq in H1.
                rewrite elem_of_subseteq.
                intros x Hx.
                specialize (H1 x).
                ltac1:(ospecialize (H1 _)).
                {
                    clear -Hx.
                    unfold vars_of; simpl.
                    destruct r0; simpl in *.
                    unfold vars_of in *; simpl in *.
                    unfold vars_of in *; simpl in *.
                    rewrite elem_of_union_list in Hx.
                    rewrite elem_of_union_list.
                    destruct Hx as [X [H1X H2X]].
                    exists X.
                    split>[|exact H2X].
                    rewrite elem_of_list_fmap in H1X.
                    destruct H1X as [y [H1y H2y]].
                    subst X.
                    rewrite elem_of_list_fmap.
                    exists (sc2_to_sc y).
                    split.
                    {
                        unfold vars_of_SideCondition.
                        destruct y; simpl in *.
                        unfold vars_of; simpl.
                        rewrite vars_of_Expression2_to_Expression.
                        rewrite vars_of_Expression2_to_Expression.
                        unfold vars_of; simpl.
                        reflexivity.
                    }
                    {
                        clear -H2y.
                        rewrite elem_of_list_fmap.
                        exists y.
                        split>[reflexivity|].
                        exact H2y.
                    }
                }
                clear -H1.
                destruct r0; simpl in *.
                ltac1:(rewrite vars_of_uglify' in H1).
                exact H1.
            }
            {
                clear -H2.
                destruct r0; simpl in *.
                unfold RewritingRule_wf2 in H2.
                unfold RewritingRule2_wf2.
                simpl in *.
                intros g ρ HH1 HH2.
                specialize (H2 (uglify' g)).
                specialize (H2 (uglify' <$> ρ)).
                ltac1:(ospecialize (H2 _ _)).
                {
                    apply sat2B_uglify.
                    exact HH1.
                }
                {
                    unfold satisfies; simpl.
                    intros x Hx.
                    unfold satisfies in HH2; simpl in HH2.
                    specialize (HH2 (sc_to_sc2 x)).
                    ltac1:(ospecialize (HH2 _)).
                    {
                        rewrite elem_of_list_fmap in Hx.
                        destruct Hx as [y [H1y H2y]].
                        subst.
                        rewrite (cancel sc_to_sc2 sc2_to_sc).
                        exact H2y.
                    }
                    unfold satisfies; simpl.
                    unfold satisfies in HH2; simpl in HH2.
                    unfold valuation_satisfies_sc.
                    destruct x; simpl in *.
                    destruct c; simpl in *.
                    unfold satisfies; simpl.
                    repeat (rewrite Expression2_Expression_evaluate in HH2).
                    rewrite (cancel Expression2_to_Expression Expression_to_Expression2) in HH2.
                    rewrite (cancel Expression2_to_Expression Expression_to_Expression2) in HH2.
                    destruct HH2 as [HH21 HH22].
                    unfold isSome in HH22.
                    destruct (prettify <$> Expression_evaluate (uglify' <$> ρ) e1) eqn:Heq.
                    {
                        apply (f_equal (fmap uglify')) in Heq.
                        rewrite fmap_uglify_prettify_option in Heq.
                        rewrite Heq.
                        apply (f_equal (fmap uglify')) in HH21.
                        rewrite fmap_uglify_prettify_option in HH21.
                        rewrite <- HH21.
                        split>[reflexivity|].
                        reflexivity.
                    }
                    {
                        inversion HH22.
                    }
                }
                destruct H2 as [g' Hg'].
                exists (prettify g').
                unfold Valuation in *.
                unfold Valuation2 in *.
                rewrite <- (cancel uglify' prettify g') in Hg'.
                apply uglify_sat2E in Hg'.
                exact Hg'.
            }
        }
        intros r'' Hr''.
        specialize (Hr' r'' Hr'').
        exact Hr'.
    }
    {
        exact None.
    }
Defined.
