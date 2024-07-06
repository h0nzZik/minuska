From Minuska Require Import
    prelude
    spec
    properties
    basic_properties
    syntax_properties
    semantics_properties
    spec_interpreter
    basic_matching
.


Lemma vars_of_sat_tobov
    {Σ : StaticModel}
    (φ : TermOver BuiltinOrVar)
    (ρ : Valuation2)
    (g : TermOver builtin_value)
    :
    satisfies ρ g φ ->
    vars_of φ ⊆ vars_of ρ
.
Proof.
    unfold satisfies; simpl.
    revert g.
    induction φ; intros g HH; simpl in *.
    {
        ltac1:(simp sat2B in HH).
        destruct a; simpl in HH; simpl in *; subst.
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold Valuation2 in *.
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            rewrite elem_of_singleton in Hx0.
            subst.
            rewrite elem_of_dom.
            exists g.
            exact HH.
        }
    }
    {
        unfold Valuation2 in *.
        ltac1:(rewrite vars_of_t_term).
        rewrite elem_of_subseteq.
        intros x Hx.
        rewrite elem_of_union_list in Hx.
        destruct Hx as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst.
        rewrite Forall_forall in H.
        specialize (H _ H2y).
        destruct g;
            ltac1:(simp sat2B in HH).
        { destruct HH. }
        destruct HH as [HH1 [HH2 HH3]].
        subst.
        rewrite elem_of_list_lookup in H2y.
        destruct H2y as [i Hi].
        specialize (HH3 i).
        destruct (l0 !! i) eqn:Heq.
        {
            specialize (HH3 t y ltac:(assumption) erefl).
            specialize (H _ HH3).
            ltac1:(set_solver).
        }
        {
            apply lookup_ge_None in Heq.
            apply lookup_lt_Some in Hi.
            ltac1:(exfalso).
            unfold TermOver in *.
            ltac1:(lia).
        }
    }
Qed.    

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
    intros g ρ Hfrom Hscs.
    clear Hscs.
    
    unfold satisfies in Hfrom; simpl in Hfrom.
    apply vars_of_sat_tobov in Hfrom.
    assert (Hvtρ : vars_of (r_to r) ⊆ vars_of ρ).
    {
        eapply transitivity>[apply H|]. apply Hfrom.
    }
    clear H Hfrom.
    apply TermOverExpression2_evalute_total_2 in Hvtρ.
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
