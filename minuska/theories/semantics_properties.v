From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    syntax_properties
.

Lemma Expression_evalute_total_iff
    {Σ : Signature}
    (t : Expression)
    (ρ : Valuation)
    :
    (∃ e:GroundTerm, Expression_evaluate ρ t = Some e)
    <->
    ( vars_of_Expression t ⊆ dom ρ )
.
Proof.
    induction t; cbn.
    {
        split; intros H.
        {
            apply empty_subseteq.
        }
        {
            exists e.
            reflexivity.
        }
    }
    {
        split; intros H.
        {
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            rewrite elem_of_singleton in Hx0.
            subst x0.
            destruct H as [e H].
            ltac1:(rewrite elem_of_dom).
            exists e. exact H.
        }
        {
            rewrite elem_of_subseteq in H.
            specialize (H x).
            rewrite elem_of_singleton in H.
            specialize (H erefl).
            ltac1:(rewrite elem_of_dom in H).
            unfold is_Some in H.
            destruct H as [e H].
            exists e.
            exact H.
        }
    }
    {
        
        ltac1:(rewrite <- IHt).
        split; intros [e H].
        {
            unfold mbind,option_bind in H; cbn.
            ltac1:(case_match).
            {
                ltac1:(rewrite <- H0).
                eexists.
                exact H0.
            }
            {
                inversion H.
            }
        }
        {
            eexists. rewrite H. reflexivity.
        }
    }
    {
        rewrite union_subseteq.
        ltac1:(rewrite <- IHt1).
        ltac1:(rewrite <- IHt2).
        split; intros H.
        {
            destruct H as [e H].
            unfold mbind,option_bind in H.
            (repeat ltac1:(case_match)); ltac1:(simplify_eq /=);
                split; eexists; reflexivity.
        }
        {
            destruct H as [[e1 H1] [e2 H2]].
            unfold mbind,option_bind.
            rewrite H1.
            rewrite H2.
            eexists. reflexivity.
        }
    }
Qed.
