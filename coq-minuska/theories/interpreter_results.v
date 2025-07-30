From Minuska Require Import
    prelude
    spec
    properties
    basic_properties
    spec_interpreter
.


Lemma vars_of_sat_tobov
    {Σ : BackgroundModel}
    (φ : @TermOver' TermSymbol BuiltinOrVar)
    (ρ : Valuation2)
    (g : @TermOver' TermSymbol BasicValue)
    :
    sat2B ρ g φ ->
    vars_of φ ⊆ vars_of ρ
.
Proof.
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
            ltac1:(lia).
        }
    }
Qed.    

#[export]
Instance RewritingTheory2_wf_dec
    {Σ : BackgroundModel}
    (Label : Set)
    (Γ : list (RewritingRule2 Label))
    :
    Decision (RewritingTheory2_wf Γ)
.
Proof.
    apply _.
Defined.
