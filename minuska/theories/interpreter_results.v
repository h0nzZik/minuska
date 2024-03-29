From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    syntax_properties
    semantics_properties
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

