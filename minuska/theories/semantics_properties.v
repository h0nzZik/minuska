From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    syntax_properties
.

Lemma Expression_evalute_total_iff
    {Σ : StaticModel}
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
        split; intros H.
        {
            ltac1:(set_solver).
        }
        {
            eexists. reflexivity.
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

(*
Lemma Expression_evaluate_eq
    {Σ : StaticModel}
    (ρ1 ρ2 : gmap variable GroundTerm)
    (t : Expression)
    :
    vars_of t ⊆ vars_of ρ1 ->
    vars_of t ⊆ vars_of ρ2 ->
    Expression_evaluate ρ1 t = Expression_evaluate ρ2 t.
Proof.
    intros H1 H2.
    induction t; simpl.
    { reflexivity. }
    {
        unfold vars_of in *; simpl in *.
    }

Qed.
*)

Lemma Expression_evalute_total_same
    {Σ : StaticModel}
    (t : Expression)
    (ρ1 ρ2 ρ : Valuation)
    :
    ρ1 ⊆ ρ ->
    ρ2 ⊆ ρ ->
    vars_of t ⊆ vars_of ρ1 ->
    vars_of t ⊆ vars_of ρ2 ->
    Expression_evaluate ρ1 t = Expression_evaluate ρ2 t
.
Proof.
    intros H1 H2 H3 H4.
    induction t; simpl.
    { reflexivity. }
    {
        unfold vars_of in *; simpl in *.
        rewrite elem_of_subseteq in H3.
        rewrite elem_of_subseteq in H4.
        specialize (H3 x).
        specialize (H4 x).
        ltac1:(specialize(H3 ltac:(set_solver))).
        ltac1:(specialize(H4 ltac:(set_solver))).
        ltac1:(rewrite elem_of_dom in H3).
        ltac1:(rewrite elem_of_dom in H4).
        destruct H3 as [x1 Hx1].
        destruct H4 as [x2 Hx2].
        rewrite Hx1. rewrite Hx2.
        eapply lookup_weaken in Hx1>[|apply H1].
        eapply lookup_weaken in Hx2>[|apply H2].
        rewrite Hx1 in Hx2.
        inversion Hx2. subst; clear Hx2.
        reflexivity.
    }
    {
        reflexivity.
    }
    {
        unfold vars_of in *; simpl in *.
        specialize (IHt ltac:(assumption)).
        specialize (IHt ltac:(assumption)).
        rewrite IHt.
        reflexivity.
    }
    {
        unfold vars_of in *; simpl in *.
        rewrite union_subseteq in H3.
        rewrite union_subseteq in H4.
        destruct H3. destruct H4.
        specialize (IHt1 ltac:(assumption)).
        specialize (IHt2 ltac:(assumption)).
        specialize (IHt1 ltac:(assumption)).
        specialize (IHt2 ltac:(assumption)).
        rewrite IHt1. rewrite IHt2.
        reflexivity.
    }
Qed.