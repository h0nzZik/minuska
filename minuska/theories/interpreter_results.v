From Minuska Require Import
    prelude
    spec
    properties
    basic_properties
    syntax_properties
    semantics_properties
    spec_interpreter
.


Lemma wf2'_impl_wf2
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    :
    RewritingRule2_wf2' r -> 
    RewritingRule2_wf2 r
.
Proof.
    intros H.
    unfold RewritingRule2_wf2' in H.
    unfold RewritingRule2_wf2.
    intros g ρ nv Hfrom Hscs.
    clear Hscs.
    
    unfold satisfies in Hfrom; simpl in Hfrom.
    apply vars_of_sat_tobov in Hfrom.
    assert (Hvtρ : vars_of (r_to r) ⊆ vars_of ρ).
    {
        eapply transitivity>[apply H|]. apply Hfrom.
    }
    clear H Hfrom.
    apply TermOverExpression2_evalute_total_2 with (nv := nv) in Hvtρ.
    exact Hvtρ.
Qed.

Definition RewritingRule2_wf2_heuristics
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    :
    option (RewritingRule2_wf2 r)
.
Proof.
    eapply option_map.
    { apply wf2'_impl_wf2. }
    unfold RewritingRule2_wf2'.
    destruct (decide (vars_of (r_to r) ⊆ (vars_of (r_from r)))) as [H|H].
    {
        exact (Some H).
    }
    exact None.
Defined.

Definition RewritingRule2_wf_heuristics
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    : option (RewritingRule2_wf r)
.
Proof.
    unfold RewritingRule2_wf.
    destruct (decide (vars_of (r_scs r) ⊆ (vars_of (r_from r)))) as [H|H].
    {

        assert (H2 := RewritingRule2_wf2_heuristics r).
        unfold RewritingRule2_wf1.
        destruct H2 as [H2|].
        {
            exact (Some (H, H2)).
        }
        exact None.
    }
    exact None.
Defined.

Definition RewritingTheory2_wf_heuristics
    {Σ : StaticModel}
    {Act : Set}
    {_dAct : EqDecision Act}
    (Γ : RewritingTheory2 Act)
    : option (RewritingTheory2_wf Γ)
.
Proof.
    unfold RewritingTheory2_wf.
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
            assert (H := RewritingRule2_wf_heuristics a).
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
