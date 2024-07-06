From Minuska Require Import
    prelude
    spec
    basic_properties
    lowlang
    properties
    semantics_properties
    varsof
    syntax_properties
    minusl_compile
    minusl_syntax
    minusl_semantics
.

Require Import Ring.
Require Import ArithRing.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Wf.

From Equations Require Export Equations.


#[global]
Set Equations Transparent.

Lemma satisfies_top_bov_cons_1
    {Σ : StaticModel}
    (ρ : Valuation)
    (topSymbol topSymbol' : symbol)
    (states : list (TermOver builtin_value))
    (lds : list (TermOver BuiltinOrVar))
    :
    length states = length lds ->
    topSymbol = topSymbol' ->
    ( forall (i : nat) s l,
            states !! i = Some s ->
            lds !! i = Some l ->
            satisfies ρ s l
    ) ->
    (
        satisfies ρ (fold_left helper (map uglify' states) (pt_operator topSymbol))
        (fold_left helper (map uglify' lds) (pt_operator topSymbol'))
    )
.
Proof.
    revert lds.
    induction states using rev_ind_T; intros lds Hlens H; simpl in *.
    {
        destruct lds; simpl in *.
        {
            subst.
            constructor.
        }
        {
            inversion Hlens.
        }
    }
    {
        destruct (analyze_list_from_end lds) as [?|He].
        {
            subst. simpl in *.
            rewrite app_length in Hlens.
            simpl in Hlens.
            ltac1:(lia).
        }
        {
            destruct He as [l' [x0 Hl']].
            subst lds.
            rewrite map_app.
            rewrite map_app.
            rewrite fold_left_app.
            rewrite fold_left_app.
            simpl.
            rewrite app_length in Hlens.
            rewrite app_length in Hlens.
            simpl in Hlens.
            assert (Hlens': length states = length l') by (ltac1:(lia)).
            intros HH.
            subst topSymbol'.
            unfold helper. simpl.
            destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                simpl in *.
            {
                constructor.
                apply IHstates.
                {
                    apply Hlens'.
                }
                {
                    reflexivity.
                }
                {
                    clear -HH.
                    intros i s l H1i H2i.
                    eapply HH.
                    {
                        rewrite lookup_app_l. apply H1i.
                        apply lookup_lt_Some in H1i. apply H1i.
                    }
                    {
                        rewrite lookup_app_l. apply H2i.
                        apply lookup_lt_Some in H2i. apply H2i.
                    }
                }
                {
                    apply (f_equal prettify) in Hux.
                    apply (f_equal prettify) in Hux0.
                    rewrite (cancel prettify uglify') in Hux.
                    rewrite (cancel prettify uglify') in Hux0.
                    subst.
                    unfold satisfies in HH; simpl in HH.
                    ltac1:(
                        replace (prettify' ao)
                        with (prettify (term_preterm ao))
                        in HH
                        by reflexivity
                    ).
                    ltac1:(
                        replace (prettify' ao0)
                        with (prettify (term_preterm ao0))
                        in HH
                        by reflexivity
                    ).
                    specialize (HH (length states)).
                    specialize (HH (prettify (term_preterm ao))).
                    specialize (HH (prettify (term_preterm ao0))).
                    rewrite (cancel uglify' prettify) in HH.
                    rewrite (cancel uglify' prettify) in HH.
                    rewrite lookup_app_r in HH>[|ltac1:(lia)].
                    rewrite lookup_app_r in HH>[|ltac1:(lia)].
                    rewrite Nat.sub_diag in HH.
                    rewrite Hlens' in HH.
                    rewrite Nat.sub_diag in HH.
                    simpl in HH.
                    specialize (HH eq_refl eq_refl).
                    inversion HH; subst; clear HH; assumption.
                }
            }
            {
                assert (HH' := HH).
                unfold satisfies in HH. simpl in HH.
                specialize (HH (length states) x x0).
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite Nat.sub_diag in HH.
                rewrite Hlens' in HH.
                rewrite Nat.sub_diag in HH.
                specialize (HH eq_refl eq_refl).
                rewrite Hux in HH. rewrite Hux0 in HH.
                inversion HH; subst; clear HH.
                constructor.
                {
                    apply IHstates; try assumption; try reflexivity.
                    intros i s l H1i H2i.
                    eapply HH'.
                    {
                        rewrite lookup_app_l. apply H1i.
                        apply lookup_lt_Some in H1i. apply H1i.
                    }
                    {
                        rewrite lookup_app_l. apply H2i.
                        apply lookup_lt_Some in H2i. apply H2i.
                    }
                }
                { assumption. }
            }
            {
                unfold satisfies in HH. simpl in HH.
                specialize (HH (length states) x x0).
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite Nat.sub_diag in HH.
                rewrite Hlens' in HH.
                rewrite Nat.sub_diag in HH.
                specialize (HH eq_refl eq_refl).
                rewrite Hux in HH. rewrite Hux0 in HH.
                inversion HH.
            }
            {
                assert (HH' := HH).
                unfold satisfies in HH. simpl in HH.
                specialize (HH (length states) x x0).
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite Nat.sub_diag in HH.
                rewrite Hlens' in HH.
                rewrite Nat.sub_diag in HH.
                specialize (HH eq_refl eq_refl).
                rewrite Hux in HH. rewrite Hux0 in HH.
                inversion HH; subst; clear HH.
                constructor.
                {
                    apply IHstates; try assumption; try reflexivity.
                    intros i s l H1i H2i.
                    eapply HH'.
                    {
                        rewrite lookup_app_l. apply H1i.
                        apply lookup_lt_Some in H1i. apply H1i.
                    }
                    {
                        rewrite lookup_app_l. apply H2i.
                        apply lookup_lt_Some in H2i. apply H2i.
                    }
                }
                { assumption. }
            }
        }
    }
Qed.

Lemma satisfies_top_bov_cons_2
    {Σ : StaticModel}
    (ρ : Valuation)
    (topSymbol topSymbol' : symbol)
    (states : list (TermOver builtin_value))
    (lds : list (TermOver BuiltinOrVar))
    :
    satisfies ρ (fold_left helper (map uglify' states) (pt_operator topSymbol))
        (fold_left helper (map uglify' lds) (pt_operator topSymbol')) ->
    (
        ((length states = length lds)
        * (topSymbol = topSymbol')
        * ( forall (i : nat) s l,
            states !! i = Some s ->
            lds !! i = Some l ->
            satisfies ρ s l
        )
        )%type
    )
.
Proof.
    revert lds.
    induction states using rev_ind_T; intros lds pf.
    {
        destruct lds; simpl in *.
        {
            (repeat split).
            inversion pf. subst. reflexivity.
            intros.
            rewrite lookup_nil in H. inversion H.
        }
        {
            inversion pf; subst; clear pf.
            ltac1:(exfalso).
            induction lds using rev_ind.
            {
                simpl in H2. unfold helper in H2.
                destruct (uglify' t); simpl in H2; inversion H2.
            }
            {
                rewrite map_app in H2.
                rewrite fold_left_app in H2.
                simpl in H2.
                unfold helper in H2.
                destruct (uglify' x) eqn:Hux.
                {
                    inversion H2.
                }
                {
                    inversion H2.
                }
            }
        }
    }
    {
        destruct (analyze_list_from_end lds); simpl in *.
        {
            ltac1:(exfalso).
            subst.

            rewrite map_app in pf.
            rewrite fold_left_app in pf.
            simpl in pf.
            unfold helper in pf.
            destruct (uglify' x) eqn:Hux.
            {
                inversion pf.
            }
            {
                inversion pf.
            }
        }
        {
            destruct s as [l' [x0 Hlds]].
            subst lds; simpl in *.
            rewrite map_app in pf.
            rewrite map_app in pf.
            simpl in pf.
            rewrite fold_left_app in pf.
            rewrite fold_left_app in pf.
            simpl in pf.
            specialize (IHstates l').
            ltac1:(ospecialize (IHstates _)).
            {
                destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                        simpl in *.
                {
                    inversion pf; subst; clear pf.
                    assumption.
                }
                {
                    inversion pf; subst; clear pf.
                    assumption.
                }
                {
                    inversion pf; subst; clear pf.
                    assumption.
                }
                {
                    inversion pf; subst; clear pf.
                    assumption.
                }
            }
            destruct IHstates as [[IHlen ?] IHstates].
            subst topSymbol'.
            do 2 (rewrite app_length).
            simpl.
            repeat split.
            { ltac1:(lia). }
            {
                intros i s l H1i H2i.
                destruct (decide (i < length states)).
                {
                    rewrite lookup_app_l in H1i>[|assumption].
                    rewrite lookup_app_l in H2i>[|ltac1:(lia)].
                    specialize (IHstates i s l H1i H2i).
                    apply IHstates.
                }
                {
                    assert (i = length states).
                    {
                        apply lookup_lt_Some in H1i.
                        rewrite app_length in H1i. simpl in H1i.
                        ltac1:(lia).
                    }
                    rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                    rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                    subst i.
                    rewrite Nat.sub_diag in H1i.
                    rewrite IHlen in H2i.
                    rewrite Nat.sub_diag in H2i.
                    simpl in *.
                    inversion H2i; subst; clear H2i.
                    inversion H1i; subst; clear H1i.
                    unfold satisfies; simpl.


                    destruct (uglify' s) eqn:Hux, (uglify' l) eqn:Hux0;
                        simpl in *; inversion pf; subst; clear pf;
                        try constructor; try assumption.
                    unfold satisfies in X0; simpl in X0. inversion X0.
                }
            }
        }
    }
Qed.

(* The proof if the same as for satisfies_top_bov_cons*)



Lemma satisfies_top_bov_cons_expr_1
    {Σ : StaticModel}
    (ρ : Valuation)
    (topSymbol topSymbol' : symbol)
    (states : list (TermOver builtin_value))
    (lds : list (TermOver Expression))
    :
    length states = length lds ->
    topSymbol = topSymbol' ->
    ( forall (i : nat) s l,
            states !! i = Some s ->
            lds !! i = Some l ->
            satisfies ρ s l
    ) ->
    (
        satisfies ρ (fold_left helper (map uglify' states) (pt_operator topSymbol))
        (fold_left helper (map uglify' lds) (pt_operator topSymbol'))
    )
.
Proof.
    revert lds.
    induction states using rev_ind_T; intros lds Hlens H; simpl in *.
    {
        destruct lds; simpl in *.
        {
            subst.
            constructor.
        }
        {
            inversion Hlens.
        }
    }
    {
        destruct (analyze_list_from_end lds) as [?|He].
        {
            subst. simpl in *.
            rewrite app_length in Hlens.
            simpl in Hlens.
            ltac1:(lia).
        }
        {
            destruct He as [l' [x0 Hl']].
            subst lds.
            rewrite map_app.
            rewrite map_app.
            rewrite fold_left_app.
            rewrite fold_left_app.
            simpl.
            rewrite app_length in Hlens.
            rewrite app_length in Hlens.
            simpl in Hlens.
            assert (Hlens': length states = length l') by (ltac1:(lia)).
            intros HH.
            subst topSymbol'.
            unfold helper. simpl.
            destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                simpl in *.
            {
                constructor.
                apply IHstates.
                {
                    apply Hlens'.
                }
                {
                    reflexivity.
                }
                {
                    clear -HH.
                    intros i s l H1i H2i.
                    eapply HH.
                    {
                        rewrite lookup_app_l. apply H1i.
                        apply lookup_lt_Some in H1i. apply H1i.
                    }
                    {
                        rewrite lookup_app_l. apply H2i.
                        apply lookup_lt_Some in H2i. apply H2i.
                    }
                }
                {
                    apply (f_equal prettify) in Hux.
                    apply (f_equal prettify) in Hux0.
                    rewrite (cancel prettify uglify') in Hux.
                    rewrite (cancel prettify uglify') in Hux0.
                    subst.
                    unfold satisfies in HH; simpl in HH.
                    ltac1:(
                        replace (prettify' ao)
                        with (prettify (term_preterm ao))
                        in HH
                        by reflexivity
                    ).
                    ltac1:(
                        replace (prettify' ao0)
                        with (prettify (term_preterm ao0))
                        in HH
                        by reflexivity
                    ).
                    specialize (HH (length states)).
                    specialize (HH (prettify (term_preterm ao))).
                    specialize (HH (prettify (term_preterm ao0))).
                    rewrite (cancel uglify' prettify) in HH.
                    rewrite (cancel uglify' prettify) in HH.
                    rewrite lookup_app_r in HH>[|ltac1:(lia)].
                    rewrite lookup_app_r in HH>[|ltac1:(lia)].
                    rewrite Nat.sub_diag in HH.
                    rewrite Hlens' in HH.
                    rewrite Nat.sub_diag in HH.
                    simpl in HH.
                    specialize (HH eq_refl eq_refl).
                    inversion HH; subst; clear HH; assumption.
                }
            }
            {
                assert (HH' := HH).
                unfold satisfies in HH. simpl in HH.
                specialize (HH (length states) x x0).
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite Nat.sub_diag in HH.
                rewrite Hlens' in HH.
                rewrite Nat.sub_diag in HH.
                specialize (HH eq_refl eq_refl).
                rewrite Hux in HH. rewrite Hux0 in HH.
                inversion HH; subst; clear HH.
                constructor.
                {
                    apply IHstates; try assumption; try reflexivity.
                    intros i s l H1i H2i.
                    eapply HH'.
                    {
                        rewrite lookup_app_l. apply H1i.
                        apply lookup_lt_Some in H1i. apply H1i.
                    }
                    {
                        rewrite lookup_app_l. apply H2i.
                        apply lookup_lt_Some in H2i. apply H2i.
                    }
                }
                { assumption. }
            }
            {
                unfold satisfies in HH. simpl in HH.
                specialize (HH (length states) x x0).
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite Nat.sub_diag in HH.
                rewrite Hlens' in HH.
                rewrite Nat.sub_diag in HH.
                specialize (HH eq_refl eq_refl).
                rewrite Hux in HH. rewrite Hux0 in HH.
                inversion HH.
            }
            {
                assert (HH' := HH).
                unfold satisfies in HH. simpl in HH.
                specialize (HH (length states) x x0).
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite lookup_app_r in HH>[|ltac1:(lia)].
                rewrite Nat.sub_diag in HH.
                rewrite Hlens' in HH.
                rewrite Nat.sub_diag in HH.
                specialize (HH eq_refl eq_refl).
                rewrite Hux in HH. rewrite Hux0 in HH.
                inversion HH; subst; clear HH.
                constructor.
                {
                    apply IHstates; try assumption; try reflexivity.
                    intros i s l H1i H2i.
                    eapply HH'.
                    {
                        rewrite lookup_app_l. apply H1i.
                        apply lookup_lt_Some in H1i. apply H1i.
                    }
                    {
                        rewrite lookup_app_l. apply H2i.
                        apply lookup_lt_Some in H2i. apply H2i.
                    }
                }
                { assumption. }
            }
        }
    }
Qed.

Lemma satisfies_top_bov_cons_expr_2
    {Σ : StaticModel}
    (ρ : Valuation)
    (topSymbol topSymbol' : symbol)
    (states : list (TermOver builtin_value))
    (lds : list (TermOver Expression))
    :
    satisfies ρ (fold_left helper (map uglify' states) (pt_operator topSymbol))
        (fold_left helper (map uglify' lds) (pt_operator topSymbol')) ->
    (
        ((length states = length lds)
        * (topSymbol = topSymbol')
        * ( forall (i : nat) s l,
            states !! i = Some s ->
            lds !! i = Some l ->
            satisfies ρ s l
        )
        )%type
    )
.
Proof.
    revert lds.
    induction states using rev_ind_T; intros lds pf.
    {
        destruct lds; simpl in *.
        {
            (repeat split).
            inversion pf. subst. reflexivity.
            intros.
            rewrite lookup_nil in H. inversion H.
        }
        {
            inversion pf; subst; clear pf.
            ltac1:(exfalso).
            induction lds using rev_ind.
            {
                simpl in H2. unfold helper in H2.
                destruct (uglify' t); simpl in H2; inversion H2.
            }
            {
                rewrite map_app in H2.
                rewrite fold_left_app in H2.
                simpl in H2.
                unfold helper in H2.
                destruct (uglify' x) eqn:Hux.
                {
                    inversion H2.
                }
                {
                    inversion H2.
                }
            }
        }
    }
    {
        destruct (analyze_list_from_end lds); simpl in *.
        {
            ltac1:(exfalso).
            subst.

            rewrite map_app in pf.
            rewrite fold_left_app in pf.
            simpl in pf.
            unfold helper in pf.
            destruct (uglify' x) eqn:Hux.
            {
                inversion pf.
            }
            {
                inversion pf.
            }
        }
        {
            destruct s as [l' [x0 Hlds]].
            subst lds; simpl in *.
            rewrite map_app in pf.
            rewrite map_app in pf.
            simpl in pf.
            rewrite fold_left_app in pf.
            rewrite fold_left_app in pf.
            simpl in pf.
            specialize (IHstates l').
            ltac1:(ospecialize (IHstates _)).
            {
                destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                        simpl in *.
                {
                    inversion pf; subst; clear pf.
                    assumption.
                }
                {
                    inversion pf; subst; clear pf.
                    assumption.
                }
                {
                    inversion pf; subst; clear pf.
                    assumption.
                }
                {
                    inversion pf; subst; clear pf.
                    assumption.
                }
            }
            destruct IHstates as [[IHlen ?] IHstates].
            subst topSymbol'.
            do 2 (rewrite app_length).
            simpl.
            repeat split.
            { ltac1:(lia). }
            {
                intros i s l H1i H2i.
                destruct (decide (i < length states)).
                {
                    rewrite lookup_app_l in H1i>[|assumption].
                    rewrite lookup_app_l in H2i>[|ltac1:(lia)].
                    specialize (IHstates i s l H1i H2i).
                    apply IHstates.
                }
                {
                    assert (i = length states).
                    {
                        apply lookup_lt_Some in H1i.
                        rewrite app_length in H1i. simpl in H1i.
                        ltac1:(lia).
                    }
                    rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                    rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                    subst i.
                    rewrite Nat.sub_diag in H1i.
                    rewrite IHlen in H2i.
                    rewrite Nat.sub_diag in H2i.
                    simpl in *.
                    inversion H2i; subst; clear H2i.
                    inversion H1i; subst; clear H1i.
                    unfold satisfies; simpl.


                    destruct (uglify' s) eqn:Hux, (uglify' l) eqn:Hux0;
                        simpl in *; inversion pf; subst; clear pf;
                        try constructor; try assumption.
                    unfold satisfies in X0; simpl in X0. inversion X0.
                }
            }
        }
    }
Qed.


Lemma satisfies_var
    {Σ : StaticModel}
    (ρ : Valuation)
    x γ:
    ρ !! x = Some (uglify' γ) ->
    satisfies ρ γ (t_over (bov_variable x))
.
Proof.
    intros H.
    destruct γ; (repeat constructor); assumption.
Qed.

Lemma satisfies_var_expr
    {Σ : StaticModel}
    (ρ : Valuation)
    x γ:
    ρ !! x = Some (uglify' γ) ->
    satisfies ρ γ (t_over (ft_variable x))
.
Proof.
    intros H.
    destruct γ; (repeat constructor); assumption.
Qed.


Lemma satisfies_var_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    x γ:
    satisfies ρ γ (t_over (bov_variable x)) ->
    ρ !! x = Some (uglify' γ)
.
Proof.
    intros H.
    inversion H; subst; clear H.
    {
        apply (f_equal prettify) in H2.
        rewrite (cancel prettify uglify') in H2.
        subst.
        inversion pf; subst; clear pf.
        assumption.
    }
    {
        apply (f_equal prettify) in H2.
        rewrite (cancel prettify uglify') in H2.
        subst.
        inversion X; subst; clear X.
        assumption.
    }
Qed.

Lemma satisfies_var_expr_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    x γ:
    satisfies ρ γ (t_over (ft_variable x)) ->
    ρ !! x = Some (uglify' γ)
.
Proof.
    intros H.
    inversion H; subst; clear H.
    {
        apply (f_equal prettify) in H2.
        rewrite (cancel prettify uglify') in H2.
        subst.
        inversion pf; subst; clear pf.
        assumption.
    }
    {
        apply (f_equal prettify) in H2.
        rewrite (cancel prettify uglify') in H2.
        subst.
        inversion X; subst; clear X.
        assumption.
    }
Qed.


Lemma weird_lemma
    {T1 T2 : Type}
    l s:
(fix go (pt : PreTerm' T1 T2) :
    list (@TermOver' T1 T2) :=
  match pt with
| pt_operator _ => []
| pt_app_operand x y => go x ++ [t_over y]
| pt_app_ao x y => go x ++ [prettify' y]
end)
  (fold_left helper'' (map uglify' l) (pt_operator s)) =
l
.
Proof.
    induction l using rev_ind.
    {
        reflexivity.
    }
    {
        rewrite map_app.
        rewrite fold_left_app.
        simpl.
        unfold helper.
        destruct (uglify' x) eqn:Hux.
        {
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            subst x.
            simpl.
            f_equal.
            {
                apply IHl.
            }
        }
        {
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            subst x.
            simpl.
            f_equal.
            {
                apply IHl.
            }
        }
    }
Qed.

Lemma get_symbol_satisfies
    {Σ : StaticModel}
    (ρ : Valuation)
    (x : PreTerm' symbol builtin_value)
    (y : PreTerm' symbol BuiltinOrVar) :
    aoxy_satisfies_aoxz ρ x y ->
    PreTerm'_get_symbol x = PreTerm'_get_symbol y
.
Proof.
    intros H.
    induction H; simpl; (ltac1:(congruence)).
Qed.


Lemma satisfies_term_expr_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (s : symbol)
    (l : list (TermOver Expression))
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
        intros H. exists []. inversion H; subst; clear H.
        unfold to_PreTerm'' in pf. simpl in pf.
        inversion pf. subst; clear pf.
        (repeat split).
        {
            rewrite <- (cancel prettify uglify' γ).
            rewrite <- H2.
            simpl.
            reflexivity.
        }
        {
            intros i γ0 e HH1 HH2.
            rewrite lookup_nil in HH1.
            inversion HH1.
        }
    }
    {
        intros H.
        inversion H; subst; clear H.
        unfold to_PreTerm'' in pf. simpl in pf.
        rewrite map_app in pf. rewrite fold_left_app in pf.
        simpl in pf.
        unfold helper in pf. simpl in pf.
        destruct (uglify' x) eqn:Hux.
        {
            simpl in *.
            apply (f_equal prettify) in H2.
            rewrite (cancel prettify uglify') in H2.
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            simpl in H2. simpl in Hux.
            subst x. simpl in *.
            subst γ. simpl in *.

            induction xy; inversion pf; subst; clear pf.
            {
            
                specialize (IHl (prettify' xy)).
                ltac1:(ospecialize (IHl _)).
                {
                    unfold satisfies; simpl.
                    ltac1:(
                        replace ((prettify' xy))
                        with (prettify (term_preterm xy))
                        by reflexivity
                    ).
                    rewrite (cancel uglify' prettify).
                    unfold apply_symbol'. simpl.
                    constructor.
                    apply X.
                }

                destruct IHl as [lγ [[IH1 IH2] IH3]].
                rewrite app_length.
                exists (lγ ++ [t_over b]).
                apply (f_equal uglify') in IH1.
                ltac1:(
                    replace ((prettify' xy))
                    with (prettify (term_preterm xy))
                    in IH1
                    by reflexivity
                ).
                rewrite (cancel uglify' prettify) in IH1.
                simpl in IH1. unfold apply_symbol'' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                repeat split.
                {
                    unfold to_PreTerm''.
                    simpl.
                    f_equal.
                    {
                        clear. induction lγ using rev_ind.
                        {
                            reflexivity.
                        }
                        {
                            rewrite map_app.
                            rewrite fold_left_app.
                            simpl.
                            unfold helper.
                            destruct (uglify' x); apply IHlγ.
                        }
                    }
                    {
                        f_equal.
                        apply weird_lemma.
                    }
                }
                {
                    rewrite IH2. reflexivity.
                }
                {
                    inversion X0.
                }
            }
            {
                assert (Hl : length l =
                    length
                    ((fix go (pt : PreTerm' symbol builtin_value) :
                        list (TermOver builtin_value) :=
                    match pt with
                    | pt_operator _ => []
                    | pt_app_operand x y => go x ++ [t_over y]
                    | pt_app_ao x y => go x ++ [prettify' y]
                    end)
                  xy1)).
                {
                    ltac1:(rename X into H3).
                    clear -H3.
                    revert xy1 H3.
                    induction l using rev_ind; intros xy1 H3.
                    {
                        simpl in *. inversion H3. reflexivity.
                    }
                    {
                        simpl.
                        rewrite app_length.
                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        simpl in H3.
                        destruct (uglify' x) eqn:Hux.
                        {
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                inversion H3; subst; clear H3.
                                ltac1:(rename X0 into H6).
                                unfold satisfies in H6; simpl in H6.
                                inversion H6.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { assumption. }
                            }
                        }
                        {
                            simpl.
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { 
                                    inversion H3;
                                    assumption.
                                }
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                {
                                    assumption.
                                }
                            }
                        }
                    }
                }

                assert(Hhelper: ∀ xy1 : PreTerm' symbol builtin_value,
                    aoxy_satisfies_aoxz ρ xy1
                    (fold_left (λ (a : PreTerm' symbol Expression) (b : Term' symbol
                    Expression),
                    match b with
                    | term_preterm b' => pt_app_ao a b'
                    | term_operand b' => pt_app_operand a b'
                    end) (map uglify' l)
                    (pt_operator s))
                → PreTerm'_get_symbol xy1 = s).
                {
                    clear.
                    induction l using rev_ind; simpl in *; intros xy1 H3.
                    {
                        inversion H3. reflexivity.
                    }
                    {

                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        ltac1:(case_match).
                        {
                            apply (f_equal prettify) in H.
                            rewrite (cancel prettify uglify') in H.
                            subst x.
                            inversion H3; subst; clear H3; simpl in *.
                            {
                                apply IHl. assumption.
                            }
                            {
                                apply IHl. assumption.
                            }
                        }
                        {
                            apply (f_equal prettify) in H.
                            rewrite (cancel prettify uglify') in H.
                            subst x.
                            inversion H3; subst; clear H3; simpl in *.
                            {
                                apply IHl. assumption.
                            }
                            {
                                apply IHl. assumption.
                            }
                        }
                    }
                }
                eexists.
                repeat split.
                {
                    simpl.
                    f_equal.
                    ltac1:(rename X into H3).
                    apply Hhelper; assumption.
                }
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {
                    intros i y e.
                    {
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' (@symbol Σ)).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm''. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            assumption.
                        }
                        destruct IHl as [lγ [[Hlγ1 Hlγ2] Hlγ3]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol'' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        intros x Hin.
                        unfold satisfies; simpl.

                        destruct (decide (i < length l)).
                        {
                            rewrite lookup_app_l in x.
                            {
                                rewrite lookup_app_l in Hin.
                                {
                                    eapply Hlγ3 with (i := i) (γ := y).
                                    {
                                        rewrite <- x.
                                        clear.
                                        unfold to_PreTerm''.
                                        rewrite weird_lemma.
                                        reflexivity.
                                    }
                                    {
                                        apply Hin.
                                    }
                                }
                                {
                                    ltac1:(lia).
                                }
                            }
                            {
                                unfold TermOver in *.
                                ltac1:(lia).
                            }
                        }
                        {
                            unfold TermOver in *.
                            assert (i = length l).
                            {
                                apply lookup_lt_Some in Hin.
                                rewrite app_length in Hin.
                                simpl in Hin.
                                ltac1:(lia).
                            }
                            subst i.
                            rewrite lookup_app_r in x.
                            {
                                rewrite lookup_app_r in Hin.
                                {
                                    rewrite <- Hl in x.
                                    rewrite Nat.sub_diag in x.
                                    rewrite Nat.sub_diag in Hin.
                                    simpl in x; simpl in Hin.
                                    inversion x; subst; clear x.
                                    inversion Hin; subst; clear Hin.
                                    rewrite uglify'_prettify'.
                                    rewrite uglify'_prettify'.
                                    constructor.
                                    apply X0.
                                }
                                {
                                    ltac1:(lia).
                                }
                            }
                            {
                                ltac1:(lia).
                            }
                        }
                    }
                }   
            }
        }
        {
            simpl in *.
            apply (f_equal prettify) in H2.
            rewrite (cancel prettify uglify') in H2.
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            simpl in H2. simpl in Hux.
            subst x. simpl in *.
            subst γ. simpl in *.

            induction xy; inversion pf; subst; clear pf.
            {
            
                specialize (IHl (prettify' xy)).
                ltac1:(ospecialize (IHl _)).
                {
                    unfold satisfies; simpl.
                    ltac1:(
                        replace ((prettify' xy))
                        with (prettify (term_preterm xy))
                        by reflexivity
                    ).
                    rewrite (cancel uglify' prettify).
                    unfold apply_symbol'. simpl.
                    constructor.
                    apply X.
                }

                destruct IHl as [lγ [[IH1 IH2] IH3]].
                rewrite app_length.
                exists (lγ ++ [t_over b]).
                apply (f_equal uglify') in IH1.
                ltac1:(
                    replace ((prettify' xy))
                    with (prettify (term_preterm xy))
                    in IH1
                    by reflexivity
                ).
                rewrite (cancel uglify' prettify) in IH1.
                simpl in IH1. unfold apply_symbol'' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                repeat split.
                {
                    unfold to_PreTerm''.
                    simpl.
                    f_equal.
                    {
                        clear. induction lγ using rev_ind.
                        {
                            reflexivity.
                        }
                        {
                            rewrite map_app.
                            rewrite fold_left_app.
                            simpl.
                            unfold helper.
                            destruct (uglify' x); apply IHlγ.
                        }
                    }
                    {
                        f_equal.
                        apply weird_lemma.
                    }
                }
                {
                    rewrite IH2. reflexivity.
                }
                intros i γ e H1i H2i.
                destruct (decide (i < length l)).
                {
                    rewrite lookup_app_l in H2i>[|ltac1:(lia)].
                    rewrite lookup_app_l in H1i>[|ltac1:(lia)].
                    apply (IH3 _ _ _ H1i H2i).
                }
                {
                    assert (i = length l).
                    {
                        apply lookup_lt_Some in H2i.
                        rewrite app_length in H2i. simpl in H2i.
                        ltac1:(lia).
                    }
                    subst i.
                    rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                    rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                    rewrite Nat.sub_diag in H2i. simpl in H2i.
                    rewrite IH2 in H1i.
                    rewrite Nat.sub_diag in H1i. simpl in H1i.
                    inversion H1i; subst; clear H1i.
                    inversion H2i; subst; clear H2i.
                    constructor.
                    assumption.
                }
            }
            {
                eexists.
                repeat split.
                {
                    simpl.
                    f_equal.
                    ltac1:(rename X into H3).
                    clear -H3.
                    fold (@helper Σ (@BuiltinOrVar Σ)) in H3.

                    revert xy1 H3.
                    induction l using rev_ind; simpl in *; intros xy1 H3.
                    {
                        inversion H3. reflexivity.
                    }
                    {

                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        destruct x, xy1; simpl in *;
                            inversion H3; subst; clear H3;
                            auto.
                    }
                }
                simpl.
                fold (@helper Σ (@BuiltinOrVar Σ)) in X.
                assert (Hl : length l =
                    length
                    ((fix go (pt : PreTerm' symbol builtin_value) :
                        list (TermOver builtin_value) :=
                    match pt with
                    | pt_operator _ => []
                    | pt_app_operand x y => go x ++ [t_over y]
                    | pt_app_ao x y => go x ++ [prettify' y]
                    end)
                  xy1)).
                {
                    ltac1:(rename X into H3).
                    clear -H3.
                    revert xy1 H3.
                    induction l using rev_ind; intros xy1 H3.
                    {
                        simpl in *. inversion H3. reflexivity.
                    }
                    {
                        simpl.
                        rewrite app_length.
                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        simpl in H3.
                        destruct (uglify' x) eqn:Hux.
                        {
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                inversion H3; subst; clear H3.
                                unfold satisfies in X0; simpl in X0.
                                inversion X0.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { assumption. }
                            }
                        }
                        {
                            simpl.
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { 
                                    inversion H3;
                                    assumption.
                                }
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                {
                                    assumption.
                                }
                            }
                        }
                    }
                }
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {

                    assert (Hl : length l =
                        length
                        ((fix go (pt : PreTerm' symbol builtin_value) :
                            list (TermOver builtin_value) :=
                        match pt with
                        | pt_operator _ => []
                        | pt_app_operand x y => go x ++ [t_over y]
                        | pt_app_ao x y => go x ++ [prettify' y]
                        end)
                    xy1)).
                    {
                        ltac1:(rename X into H3).
                        clear -H3.
                        revert xy1 H3.
                        induction l using rev_ind; intros xy1 H3.
                        {
                            simpl in *. inversion H3. reflexivity.
                        }
                        {
                            simpl.
                            rewrite app_length.
                            rewrite map_app in H3.
                            rewrite fold_left_app in H3.
                            simpl in H3.
                            simpl in H3.
                            destruct (uglify' x) eqn:Hux.
                            {
                                destruct xy1; simpl in *.
                                {
                                    inversion H3.
                                }
                                {
                                    inversion H3; subst; clear H3.
                                    ltac1:(rename X0 into H6).
                                    unfold satisfies in H6; simpl in H6.
                                    inversion H6.
                                }
                                {
                                    inversion H3; subst; clear H3.
                                    rewrite app_length. simpl.
                                    erewrite IHl.
                                    { reflexivity. }
                                    { assumption. }
                                }
                            }
                            {
                                simpl.
                                destruct xy1; simpl in *.
                                {
                                    inversion H3.
                                }
                                {
                                    rewrite app_length. simpl.
                                    erewrite IHl.
                                    { reflexivity. }
                                    { 
                                        inversion H3;
                                        assumption.
                                    }
                                }
                                {
                                    inversion H3; subst; clear H3.
                                    rewrite app_length. simpl.
                                    erewrite IHl.
                                    { reflexivity. }
                                    {
                                        assumption.
                                    }
                                }
                            }
                        }
                    }
                    intros i γ e HH1 HH2.
                    unfold TermOver in *.
                    destruct (decide (i < length l)).
                    {
                        rewrite lookup_app_l in HH1>[|ltac1:(lia)].
                        rewrite lookup_app_l in HH2>[|ltac1:(lia)].
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' (@symbol Σ)).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm''. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            assumption.
                        }
                        destruct IHl as [lγ [[Hlγ1 Hlγ2] Hlγ3]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol'' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        unfold TermOver in *.
                        eapply Hlγ3 with (i := i) (γ := γ).
                        {
                            rewrite <- HH1.
                            clear.
                            unfold to_PreTerm''.
                            rewrite weird_lemma.
                            reflexivity.
                        }
                        {
                            apply HH2.
                        }
                    }
                    {
                        assert (i = length l).
                        {
                            apply lookup_lt_Some in HH2.
                            rewrite app_length in HH2. simpl in HH2.
                            ltac1:(lia).
                        }
                        subst i.
                        rewrite lookup_app_r in HH1>[|ltac1:(lia)].
                        rewrite lookup_app_r in HH2>[|ltac1:(lia)].
                        rewrite <- Hl in HH1.
                        rewrite Nat.sub_diag in HH1.
                        rewrite Nat.sub_diag in HH2.
                        simpl in HH1,HH2.
                        inversion HH1; subst; clear HH1.
                        inversion HH2; subst; clear HH2.
                        unfold satisfies; simpl.
                        rewrite uglify'_prettify'.
                        constructor.
                        assumption.
                    }
                }   
            }
        }
    }
Qed.

Lemma satisfies_term_bov_inv
    {Σ : StaticModel}
    (ρ : Valuation)
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
        intros H. exists []. inversion H; subst; clear H.
        unfold to_PreTerm'' in pf. simpl in pf.
        inversion pf. subst; clear pf.
        (repeat split).
        {
            rewrite <- (cancel prettify uglify' γ).
            rewrite <- H2.
            simpl.
            reflexivity.
        }
        {
            intros i γ0 e HH1 HH2.
            rewrite lookup_nil in HH1.
            inversion HH1.
        }
    }
    {   
        unfold TermOver in *.
        intros H.
        inversion H; subst; clear H.
        unfold to_PreTerm'' in pf. simpl in pf.
        rewrite map_app in pf. rewrite fold_left_app in pf.
        simpl in pf.
        unfold helper in pf. simpl in pf.
        destruct (uglify' x) eqn:Hux.
        {
            simpl in *.
            apply (f_equal prettify) in H2.
            rewrite (cancel prettify uglify') in H2.
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            simpl in H2. simpl in Hux.
            subst x. simpl in *.
            subst γ. simpl in *.

            induction xy; inversion pf; subst; clear pf.
            {
            
                specialize (IHl (prettify' xy)).
                ltac1:(ospecialize (IHl _)).
                {
                    unfold satisfies; simpl.
                    ltac1:(
                        replace ((prettify' xy))
                        with (prettify (term_preterm xy))
                        by reflexivity
                    ).
                    rewrite (cancel uglify' prettify).
                    unfold apply_symbol'. simpl.
                    constructor.
                    apply X.
                }

                destruct IHl as [lγ [[IH1 IH2] IH3]].
                rewrite app_length.
                exists (lγ ++ [t_over b]).
                apply (f_equal uglify') in IH1.
                ltac1:(
                    replace ((prettify' xy))
                    with (prettify (term_preterm xy))
                    in IH1
                    by reflexivity
                ).
                rewrite (cancel uglify' prettify) in IH1.
                simpl in IH1. unfold apply_symbol'' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                repeat split.
                {
                    unfold to_PreTerm''.
                    simpl.
                    f_equal.
                    {
                        clear. induction lγ using rev_ind.
                        {
                            reflexivity.
                        }
                        {
                            rewrite map_app.
                            rewrite fold_left_app.
                            simpl.
                            unfold helper.
                            destruct (uglify' x); apply IHlγ.
                        }
                    }
                    {
                        f_equal.
                        apply weird_lemma.
                    }
                }
                {
                    rewrite IH2. reflexivity.
                }
                {
                    inversion X0.
                }
            }
            {
                assert (Hl : length l =
                    length
                    ((fix go (pt : PreTerm' symbol builtin_value) :
                        list (TermOver builtin_value) :=
                    match pt with
                    | pt_operator _ => []
                    | pt_app_operand x y => go x ++ [t_over y]
                    | pt_app_ao x y => go x ++ [prettify' y]
                    end)
                  xy1)).
                {
                    ltac1:(rename X into H3).
                    clear -H3.
                    revert xy1 H3.
                    induction l using rev_ind; intros xy1 H3.
                    {
                        simpl in *. inversion H3. reflexivity.
                    }
                    {
                        simpl.
                        rewrite app_length.
                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        simpl in H3.
                        destruct (uglify' x) eqn:Hux.
                        {
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                inversion H3; subst; clear H3.
                                ltac1:(rename X0 into H6).
                                unfold satisfies in H6; simpl in H6.
                                inversion H6.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { assumption. }
                            }
                        }
                        {
                            simpl.
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { 
                                    inversion H3;
                                    assumption.
                                }
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                {
                                    assumption.
                                }
                            }
                        }
                    }
                }

                assert(Hhelper: ∀ xy1 : PreTerm' symbol builtin_value,
                    aoxy_satisfies_aoxz ρ xy1
                    (fold_left (λ (a : PreTerm' symbol BuiltinOrVar) (b : Term' symbol
                    BuiltinOrVar),
                    match b with
                    | term_preterm b' => pt_app_ao a b'
                    | term_operand b' => pt_app_operand a b'
                    end) (map uglify' l)
                    (pt_operator s))
                → PreTerm'_get_symbol xy1 = s).
                {
                    clear.
                    induction l using rev_ind; simpl in *; intros xy1 H3.
                    {
                        inversion H3. reflexivity.
                    }
                    {

                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        ltac1:(case_match).
                        {
                            apply (f_equal prettify) in H.
                            rewrite (cancel prettify uglify') in H.
                            subst x.
                            inversion H3; subst; clear H3; simpl in *.
                            {
                                apply IHl. assumption.
                            }
                            {
                                apply IHl. assumption.
                            }
                        }
                        {
                            apply (f_equal prettify) in H.
                            rewrite (cancel prettify uglify') in H.
                            subst x.
                            inversion H3; subst; clear H3; simpl in *.
                            {
                                apply IHl. assumption.
                            }
                            {
                                apply IHl. assumption.
                            }
                        }
                    }
                }
                eexists.
                repeat split.
                {
                    simpl.
                    f_equal.
                    ltac1:(rename X into H3).
                    apply Hhelper; assumption.
                }
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {
                    intros i y e.
                    {
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' (@symbol Σ)).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm''. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            assumption.
                        }
                        destruct IHl as [lγ [[Hlγ1 Hlγ2] Hlγ3]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol'' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        intros x Hin.
                        unfold satisfies; simpl.

                        destruct (decide (i < length l)).
                        {
                            rewrite lookup_app_l in x.
                            {
                                rewrite lookup_app_l in Hin.
                                {
                                    eapply Hlγ3 with (i := i) (γ := y).
                                    {
                                        rewrite <- x.
                                        clear.
                                        unfold to_PreTerm''.
                                        rewrite weird_lemma.
                                        reflexivity.
                                    }
                                    {
                                        apply Hin.
                                    }
                                }
                                {
                                    ltac1:(lia).
                                }
                            }
                            {
                                unfold TermOver in *.
                                ltac1:(lia).
                            }
                        }
                        {
                            assert (i = length l).
                            {
                                apply lookup_lt_Some in Hin.
                                rewrite app_length in Hin.
                                simpl in Hin.
                                ltac1:(lia).
                            }
                            subst i.
                            unfold TermOver in *.
                            rewrite lookup_app_r in x.
                            {
                                rewrite lookup_app_r in Hin.
                                {
                                    rewrite <- Hl in x.
                                    rewrite Nat.sub_diag in x.
                                    rewrite Nat.sub_diag in Hin.
                                    simpl in x; simpl in Hin.
                                    inversion x; subst; clear x.
                                    inversion Hin; subst; clear Hin.
                                    rewrite uglify'_prettify'.
                                    rewrite uglify'_prettify'.
                                    constructor.
                                    apply X0.
                                }
                                {
                                    ltac1:(lia).
                                }
                            }
                            {
                                ltac1:(lia).
                            }
                        }
                    }
                }   
            }
        }
        {
            simpl in *.
            apply (f_equal prettify) in H2.
            rewrite (cancel prettify uglify') in H2.
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            simpl in H2. simpl in Hux.
            subst x. simpl in *.
            subst γ. simpl in *.

            induction xy; inversion pf; subst; clear pf.
            {
            
                specialize (IHl (prettify' xy)).
                ltac1:(ospecialize (IHl _)).
                {
                    unfold satisfies; simpl.
                    ltac1:(
                        replace ((prettify' xy))
                        with (prettify (term_preterm xy))
                        by reflexivity
                    ).
                    rewrite (cancel uglify' prettify).
                    unfold apply_symbol'. simpl.
                    constructor.
                    apply X.
                }

                destruct IHl as [lγ [[IH1 IH2] IH3]].
                rewrite app_length.
                exists (lγ ++ [t_over b]).
                apply (f_equal uglify') in IH1.
                ltac1:(
                    replace ((prettify' xy))
                    with (prettify (term_preterm xy))
                    in IH1
                    by reflexivity
                ).
                rewrite (cancel uglify' prettify) in IH1.
                simpl in IH1. unfold apply_symbol'' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                repeat split.
                {
                    unfold to_PreTerm''.
                    simpl.
                    f_equal.
                    {
                        clear. induction lγ using rev_ind.
                        {
                            reflexivity.
                        }
                        {
                            rewrite map_app.
                            rewrite fold_left_app.
                            simpl.
                            unfold helper.
                            destruct (uglify' x); apply IHlγ.
                        }
                    }
                    {
                        f_equal.
                        apply weird_lemma.
                    }
                }
                {
                    rewrite IH2. reflexivity.
                }
                intros i γ e H1i H2i.
                destruct (decide (i < length l)).
                {
                    rewrite lookup_app_l in H2i>[|ltac1:(lia)].
                    rewrite lookup_app_l in H1i>[|ltac1:(lia)].
                    apply (IH3 _ _ _ H1i H2i).
                }
                {
                    assert (i = length l).
                    {
                        apply lookup_lt_Some in H2i.
                        rewrite app_length in H2i. simpl in H2i.
                        ltac1:(lia).
                    }
                    subst i.
                    rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                    rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                    rewrite Nat.sub_diag in H2i. simpl in H2i.
                    rewrite IH2 in H1i.
                    rewrite Nat.sub_diag in H1i. simpl in H1i.
                    inversion H1i; subst; clear H1i.
                    inversion H2i; subst; clear H2i.
                    constructor.
                    assumption.
                }
            }
            {
                eexists.
                repeat split.
                {
                    simpl.
                    f_equal.
                    ltac1:(rename X into H3).
                    clear -H3.
                    fold (@helper Σ (@BuiltinOrVar Σ)) in H3.

                    revert xy1 H3.
                    induction l using rev_ind; simpl in *; intros xy1 H3.
                    {
                        inversion H3. reflexivity.
                    }
                    {

                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        destruct x, xy1; simpl in *;
                            inversion H3; subst; clear H3;
                            auto.
                    }
                }
                simpl.
                fold (@helper Σ (@BuiltinOrVar Σ)) in X.
                assert (Hl : length l =
                    length
                    ((fix go (pt : PreTerm' symbol builtin_value) :
                        list (TermOver builtin_value) :=
                    match pt with
                    | pt_operator _ => []
                    | pt_app_operand x y => go x ++ [t_over y]
                    | pt_app_ao x y => go x ++ [prettify' y]
                    end)
                  xy1)).
                {
                    ltac1:(rename X into H3).
                    clear -H3.
                    revert xy1 H3.
                    induction l using rev_ind; intros xy1 H3.
                    {
                        simpl in *. inversion H3. reflexivity.
                    }
                    {
                        simpl.
                        rewrite app_length.
                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        simpl in H3.
                        destruct (uglify' x) eqn:Hux.
                        {
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                inversion H3; subst; clear H3.
                                unfold satisfies in X0; simpl in X0.
                                inversion X0.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { assumption. }
                            }
                        }
                        {
                            simpl.
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { 
                                    inversion H3;
                                    assumption.
                                }
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                {
                                    assumption.
                                }
                            }
                        }
                    }
                }
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {

                    assert (Hl : length l =
                        length
                        ((fix go (pt : PreTerm' symbol builtin_value) :
                            list (TermOver builtin_value) :=
                        match pt with
                        | pt_operator _ => []
                        | pt_app_operand x y => go x ++ [t_over y]
                        | pt_app_ao x y => go x ++ [prettify' y]
                        end)
                    xy1)).
                    {
                        ltac1:(rename X into H3).
                        clear -H3.
                        revert xy1 H3.
                        induction l using rev_ind; intros xy1 H3.
                        {
                            simpl in *. inversion H3. reflexivity.
                        }
                        {
                            simpl.
                            rewrite app_length.
                            rewrite map_app in H3.
                            rewrite fold_left_app in H3.
                            simpl in H3.
                            simpl in H3.
                            destruct (uglify' x) eqn:Hux.
                            {
                                destruct xy1; simpl in *.
                                {
                                    inversion H3.
                                }
                                {
                                    inversion H3; subst; clear H3.
                                    ltac1:(rename X0 into H6).
                                    unfold satisfies in H6; simpl in H6.
                                    inversion H6.
                                }
                                {
                                    inversion H3; subst; clear H3.
                                    rewrite app_length. simpl.
                                    erewrite IHl.
                                    { reflexivity. }
                                    { assumption. }
                                }
                            }
                            {
                                simpl.
                                destruct xy1; simpl in *.
                                {
                                    inversion H3.
                                }
                                {
                                    rewrite app_length. simpl.
                                    erewrite IHl.
                                    { reflexivity. }
                                    { 
                                        inversion H3;
                                        assumption.
                                    }
                                }
                                {
                                    inversion H3; subst; clear H3.
                                    rewrite app_length. simpl.
                                    erewrite IHl.
                                    { reflexivity. }
                                    {
                                        assumption.
                                    }
                                }
                            }
                        }
                    }
                    unfold TermOver in *.
                    intros i γ e HH1 HH2.
                    destruct (decide (i < length l)).
                    {
                        rewrite lookup_app_l in HH1>[|ltac1:(lia)].
                        rewrite lookup_app_l in HH2>[|ltac1:(lia)].
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' (@symbol Σ)).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm''. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            assumption.
                        }
                        destruct IHl as [lγ [[Hlγ1 Hlγ2] Hlγ3]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol'' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        eapply Hlγ3 with (i := i) (γ := γ).
                        {
                            rewrite <- HH1.
                            clear.
                            unfold to_PreTerm''.
                            rewrite weird_lemma.
                            reflexivity.
                        }
                        {
                            apply HH2.
                        }
                    }
                    {
                        assert (i = length l).
                        {
                            apply lookup_lt_Some in HH2.
                            rewrite app_length in HH2. simpl in HH2.
                            ltac1:(lia).
                        }
                        subst i.
                        rewrite lookup_app_r in HH1>[|ltac1:(lia)].
                        rewrite lookup_app_r in HH2>[|ltac1:(lia)].
                        rewrite <- Hl in HH1.
                        rewrite Nat.sub_diag in HH1.
                        rewrite Nat.sub_diag in HH2.
                        simpl in HH1,HH2.
                        inversion HH1; subst; clear HH1.
                        inversion HH2; subst; clear HH2.
                        unfold satisfies; simpl.
                        rewrite uglify'_prettify'.
                        constructor.
                        assumption.
                    }
                }   
            }
        }
    }
Qed.

Lemma vars_of_uglify
    {Σ : StaticModel}
    (h : variable) a:
    h ∈ vars_of_to_l2r a
    <->
    h ∈ (vars_of (uglify' a))
.
Proof.
    induction a; unfold vars_of; simpl.
    {
        destruct a; unfold vars_of; simpl.
        { ltac1:(set_solver). }
        { ltac1:(set_solver). }
    }
    {
        unfold TermOver in *.
        unfold to_PreTerm''; simpl.
        revert s h H.
        induction l using rev_ind; intros s h H.
        {
            simpl. unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            rewrite map_app.
            rewrite map_app.
            rewrite concat_app.
            rewrite fold_left_app.
            rewrite elem_of_app.
            simpl.

            rewrite Forall_app in H.
            destruct H as [H1 H2].
            specialize (IHl s h H1). clear H1.
            rewrite IHl. clear IHl.
            rewrite Forall_cons in H2.
            destruct H2 as [H2 _].
            unfold helper; simpl.
            destruct (uglify' x) eqn:Hux;
                unfold vars_of; simpl;
                rewrite elem_of_union;
                rewrite app_nil_r;
                rewrite H2; clear H2;
                unfold vars_of; simpl.
            {
                reflexivity.
            }
            {
                destruct operand; unfold vars_of; simpl.
                {
                    ltac1:(tauto).
                }
                {
                    rewrite elem_of_singleton.
                    ltac1:(tauto).
                }
            }
        }
    }
Qed.



Lemma length_filter_l_1_impl_h_in_l
    {Σ : StaticModel}
    (l : list variable)
    (h : variable):
    length (filter (eq h) l) = 1 ->
    h ∈ l
.
Proof.
    intros H.
    induction l; simpl in *.
    { inversion H. }
    {
        rewrite filter_cons in H.
        destruct (decide (h = a)).
        {
            subst. left.
        }
        {
            right. apply IHl. apply H.
        }
    }
Qed.

Lemma h_in_l_impl_length_filter_l_gt_1
    {T : Type}
    (P : T -> Prop)
    {_dP: forall x, Decision (P x)}
    (l : list T)
    (h : T)
    :
    h ∈ l ->
    P h ->
    length (filter P l) >= 1
.
Proof.
    induction l; simpl.
    {
        intros HH. inversion HH.
    }
    {
        intros HH1 HH2.
        rewrite elem_of_cons in HH1.
        destruct HH1 as [HH1|HH1].
        {
            subst. rewrite filter_cons.
            destruct (decide (P a))>[|ltac1:(contradiction)].
            simpl.
            ltac1:(lia).
        }
        {
            specialize (IHl HH1 HH2).
            rewrite filter_cons.
            ltac1:(case_match).
            {
                simpl. ltac1:(lia).
            }
            {
                exact IHl.
            }
        }
    }
Qed.


Lemma length_filter_l_1_impl_h_in_l'
    {T : Type}
    (P : T -> Prop)
    {_dP: forall x, Decision (P x)}
    (l : list T)
    :
    length (filter P l) = 1 ->
    exists h, 
    h ∈ l /\ P h
.
Proof.
    intros H.
    induction l; simpl in *.
    { inversion H. }
    {
        rewrite filter_cons in H.
        destruct (decide (P a)).
        {
            subst. exists a. split. left. assumption.
        }
        {
            specialize (IHl H).
            destruct IHl as [h [H1h H2h]].
            exists h. split.
            right. assumption. assumption.
        }
    }
Qed.


Lemma size_subst_1
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    TermOver_size φ <= TermOver_size (TermOverBoV_subst φ h ψ)
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        { ltac1:(lia). }
        {
            destruct (decide (h = x)); simpl.
            {
                destruct ψ; simpl; ltac1:(lia).
            }
            {
                ltac1:(lia).
            }
        }
    }
    {
        revert H.
        induction l; intros H; simpl in *.
        { ltac1:(lia). }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            ltac1:(lia).
        }
    }
Qed.

Lemma size_subst_2
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∈ vars_of_to_l2r φ ->
    TermOver_size ψ <= TermOver_size (TermOverBoV_subst φ h ψ)
.
Proof.
    revert h ψ.
    induction φ; intros h ψ Hin; simpl in *.
    {
        destruct a.
        {
            inversion Hin.
        }
        {
            inversion Hin; subst; clear Hin.
            {
                destruct (decide (x = x))>[|ltac1:(contradiction)].
                ltac1:(lia).
            }
            {
                inversion H1.
            }
        }
    }
    {
        revert H Hin.
        induction l; intros H Hin; simpl in *.
        {
            inversion Hin.
        }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            destruct (decide (h ∈ vars_of_to_l2r a )) as [Hin'|Hnotin'].
            {
                specialize (H1 h ψ Hin'). clear Hin.
                ltac1:(lia).
            }
            {
                specialize (IHl ltac:(set_solver)).
                ltac1:(lia).
            }
        }
    }
Qed.

Lemma to_preterm_is_pt_operator_inv
    {T0 T : Type}
    (s s' : T0)
    (l : list (Term' T0 T)):
    pt_operator s' = to_PreTerm'' s l ->
    s' = s /\ l = []
.
Proof.
    revert s s'.
    destruct l using rev_ind; intros s s' H1.
    {
        inversion H1. subst. split; reflexivity.
    }
    {
        unfold to_PreTerm'' in H1.
        
        rewrite fold_left_app in H1. simpl in H1.
        unfold helper in H1; simpl in H1.
        destruct x.
        {
            inversion H1.
        }
        {
            inversion H1.
        }
    }
Qed.

Lemma satisfies_TermOverBuiltin_to_TermOverBoV
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    :
    satisfies ρ γ (TermOverBuiltin_to_TermOverBoV γ)
.
Proof.
    unfold satisfies; simpl.
    ltac1:(induction γ using TermOver_rect); constructor.
    {
        constructor.
    }
    {
        fold (@uglify' (@symbol Σ)).
        fold (@TermOver_map Σ).
        unfold to_PreTerm''.
        apply satisfies_top_bov_cons_1.
        {
            rewrite map_length. reflexivity.
        }
        { reflexivity. }
        {
            intros i s0 l0 H1i H2i.
            specialize (X s0).
            ltac1:(ospecialize (X _)).
            {
                rewrite elem_of_list_lookup.
                exists i. exact H1i.
            }
            {
                ltac1:(replace (map) with (@fmap _ list_fmap) in H2i by reflexivity).
                rewrite list_lookup_fmap in H2i.
                rewrite H1i in H2i.
                simpl in H2i.
                inversion H2i; subst; clear H2i.
                apply X.
            }
        }
    }
Qed.

Lemma satisfies_builtin_inv {Σ : StaticModel} (ρ : Valuation) l s b:
    satisfies ρ (fold_left helper l (pt_operator s)) (bov_builtin b) ->
    False
.
Proof.
    destruct l using rev_ind; simpl; intros HH.
    {
        inversion HH.
    }
    {
        rewrite fold_left_app in HH. simpl in HH.
        inversion HH.
    }
Qed.

Lemma to_preterm_eq_inv
    {T0 T : Type}
    (s1 s2 : T0)
    (l1 l2 : list (Term' T0 T))
    :
    to_PreTerm'' s1 l1 = to_PreTerm'' s2 l2
    -> s1 = s2 /\ l1 = l2
.
Proof.
    revert l2.
    induction l1 using rev_ind; intros l2 HH; destruct l2 using rev_ind.
    {
        inversion HH. subst. repeat split.
    }
    {
        unfold to_PreTerm'' in *.
        rewrite fold_left_app in HH. simpl in HH.
        destruct l2 using rev_ind.
        {
            simpl in HH. unfold helper in HH.
            destruct x.
            {
                inversion HH.
            }
            {
                inversion HH.
            }
        }
        {
            rewrite fold_left_app in HH. simpl in HH.
            unfold helper in HH.
            destruct x; inversion HH.
        }
    }
    {
        unfold to_PreTerm'' in *.
        rewrite fold_left_app in HH. simpl in HH.
        destruct l1 using rev_ind.
        {
            simpl in HH. unfold helper in HH.
            destruct x.
            {
                inversion HH.
            }
            {
                inversion HH.
            }
        }
        {
            rewrite fold_left_app in HH. simpl in HH.
            unfold helper in HH.
            destruct x; inversion HH.
        }
    }
    {
        unfold to_PreTerm'' in *.
        rewrite fold_left_app in HH.
        rewrite fold_left_app in HH.
        simpl in HH.
        unfold helper in HH.
        destruct x,x0; simpl in *; inversion HH; subst; clear HH.
        {
            simpl in *.
            specialize (IHl1 l2 H0). clear H0.
            destruct IHl1 as [IH1 IH2].
            subst.
            split>[reflexivity|].
            reflexivity.
        }
        {
            simpl in *.
            specialize (IHl1 l2 H0). clear H0.
            destruct IHl1 as [IH1 IH2].
            subst.
            split>[reflexivity|].
            reflexivity.
        }
    }
Qed.

Lemma map_uglify'_inj
    {Σ : StaticModel}
    {T : Type}
    (l1 l2 : list (TermOver T))
    :
    map uglify' l1 = map uglify' l2 ->
    l1 = l2
.
Proof.
    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
    intros H.
    apply list_fmap_eq_inj in H.
    exact H.
    apply cancel_inj.
Qed.

Lemma forall_satisfies_inv'
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation)
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
    (ρ : Valuation)
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
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            inversion pf; subst; clear pf;
            inversion pf0; subst; clear pf0;
            try reflexivity.
            ltac1:(simplify_eq /=).
            reflexivity.
        }
        {
            inversion H1.
        }
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            destruct az.
            {
                inversion pf; subst; clear pf.
                unfold to_PreTerm'' in H3.
                apply satisfies_builtin_inv in X.
                inversion X.
            }
            {
                inversion pf; subst; clear pf.
                inversion X; subst; clear X.
                ltac1:(simplify_eq /=).
            }
        }
        {
            inversion H1.
        }
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            destruct az.
            {
                inversion pf; subst; clear pf.
                unfold to_PreTerm'' in X.
                apply satisfies_builtin_inv in X.
                inversion X.
            }
            {
                inversion pf; subst; clear pf.
                inversion X; subst; clear X.
                ltac1:(simplify_eq /=).
            }
        }
        {
            inversion H2.
        }
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            destruct az.
            {
                apply satisfies_builtin_inv in X.
                inversion X.
            }
            {
                inversion X; subst; clear X.
                inversion X0; subst; clear X0.
                ltac1:(simplify_eq /=).
                apply to_preterm_eq_inv in H.
                destruct H as [H1 H2].
                subst cy.
                apply map_uglify'_inj in H2.
                subst ly.
                reflexivity.
            }
        }
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            unfold to_PreTerm'' in pf.
            unfold to_PreTerm'' in pf0.
            apply satisfies_top_bov_cons_2 in pf.
            apply satisfies_top_bov_cons_2 in pf0.
            destruct pf as [H1 H2].
            destruct pf0 as [H3 H4].
            assert (IH1 := forall_satisfies_inv' Σ sz ρ lx ly lz).
            destruct H1. subst cx.
            destruct H3. subst cy.
            simpl in Hsz.
            specialize (IH1 ltac:(lia)).
            specialize (IH1 ltac:(assumption)).
            specialize (IH1 ltac:(assumption)).
            specialize (IH1 ltac:(assumption)).
            specialize (IH1 ltac:(assumption)).
            subst.
            reflexivity.
        }
    }
Qed.

Lemma forall_satisfies_inv
    {Σ : StaticModel}
    (ρ : Valuation)
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
    (ρ : Valuation)
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
    (ρ : Valuation)
    (x : variable)
    (t t' : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    x ∈ vars_of (uglify' φ) ->
    ρ !! x = Some (uglify' t') ->
    satisfies ρ t φ ->
    TermOver_size t' <= TermOver_size t
.
Proof.
    revert t.
    induction φ; intros t Hin Hsome Hsat.
    {
        destruct a.
        {
            inversion Hsat; subst; clear Hsat.
            {
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                simpl in *.
                unfold vars_of in Hin; simpl in Hin.
                unfold vars_of in Hin; simpl in Hin.
                clear -Hin.
                ltac1:(exfalso).
                ltac1:(set_solver).
            }
            {
                unfold vars_of in Hin; simpl in Hin.
                unfold vars_of in Hin; simpl in Hin.
                clear -Hin.
                ltac1:(exfalso).
                ltac1:(set_solver).
            }
        }
        {
            unfold vars_of in Hin; simpl in Hin.
            unfold vars_of in Hin; simpl in Hin.
            rewrite elem_of_singleton in Hin. subst x0.
            inversion Hsat; subst; clear Hsat.
            {
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                simpl in *.
                inversion pf; subst; clear pf.
                rewrite H1 in Hsome. inversion Hsome; subst; clear Hsome.
                apply (f_equal prettify) in H0.
                rewrite (cancel prettify uglify') in H0.
                subst t'.
                simpl.
                ltac1:(lia).
            }
            {
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                simpl in *.
                inversion X; subst; clear X.
                rewrite H0 in Hsome. inversion Hsome; subst; clear Hsome.
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t'.
                simpl.
                ltac1:(lia).
            }
        }
    }
    {
        apply satisfies_term_bov_inv in Hsat.
        destruct Hsat as [lγ [[H1 H2] H3]].
        subst.
        simpl.
        rewrite <- vars_of_uglify in Hin.
        simpl in Hin.
        rewrite elem_of_list_In in Hin.
        rewrite in_concat in Hin.
        destruct Hin as [x0 [H1x0 H2x0]].
        rewrite <- elem_of_list_In in H1x0.
        rewrite <- elem_of_list_In in H2x0.
        ltac1:(replace map with (@fmap _ list_fmap) in H1x0 by reflexivity).
        ltac1:(rewrite elem_of_list_lookup in H1x0).
        destruct H1x0 as [i Hi].
        rewrite list_lookup_fmap in Hi.
        unfold TermOver in *.
        destruct (l !! i) eqn:Hli.
        {
            simpl in Hi. inversion Hi; subst; clear Hi.
            rewrite Forall_forall in H.
            specialize (H t).
            ltac1:(ospecialize (H _)).
            {
                rewrite elem_of_list_lookup.
                exists i. exact Hli.
            }
            destruct (lγ !! i) eqn:Hlγi.
            {
                specialize (H3 _ _ _ Hlγi Hli).
                specialize (H t0).
                rewrite <- vars_of_uglify in H.
                specialize (H H2x0 Hsome H3).
                apply take_drop_middle in Hlγi.
                rewrite <- Hlγi.
                rewrite sum_list_with_app.
                simpl.
                ltac1:(lia).
            }
            {
                apply lookup_ge_None_1 in Hlγi.
                apply lookup_lt_Some in Hli.
                ltac1:(lia).
            }
        }
        {
            simpl in Hi. inversion Hi.
        }
    }
Qed.

Lemma double_satisfies_contradiction
    {Σ : StaticModel}
    (ρ : Valuation)
    (ay : BuiltinOrVar)
    (cz cx : symbol)
    (lx : list (TermOver builtin_value))
    (lz : list (TermOver BuiltinOrVar))
    :
    vars_of (@uglify' (@symbol Σ) BuiltinOrVar (t_over ay)) = vars_of (uglify' (t_term cz lz)) ->
    satisfies ρ (t_term cx lx) (t_over ay) ->
    satisfies ρ (t_term cx lx) (t_term cz lz) ->
    False
.
Proof.
    intros Hvars H1 H2.
        inversion H1; subst; clear H1.
        inversion H2; subst; clear H2.
        unfold to_PreTerm'' in pf.
        apply satisfies_top_bov_cons_2 in pf.
        destruct pf as [[pf1 pf2] pf3].
        subst cz.
        destruct ay.
        {
            inversion X; subst; clear X.
        }
        {
            
            ltac1:(exfalso).
            simpl in Hvars.
            assert (Htmp1 := satisfies_in_size ρ x).
            unfold vars_of in Hvars; simpl in Hvars.
            unfold vars_of in Hvars; simpl in Hvars.

            inversion X; subst; clear X.
            assert (∃ z, z ∈ map uglify' lz /\ x ∈ (vars_of z)).
            {
                clear -Hvars.
                revert Hvars.
                induction lz using rev_ind; intros Hvars.
                {
                    simpl in Hvars. ltac1:(set_solver).
                }
                {
                    rewrite map_app in Hvars.
                    unfold to_PreTerm'' in Hvars.
                    rewrite fold_left_app in Hvars.
                    simpl in Hvars.
                    unfold helper in Hvars.
                    destruct (uglify' x0) eqn:Hux0.
                    {
                        simpl in Hvars.
                        destruct (decide (x ∈ vars_of ao)).
                        {
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0.
                            exists (term_preterm ao).
                            rewrite map_app.
                            split.
                            {
                                rewrite elem_of_app.
                                right. ltac1:(rewrite /map).
                                rewrite (cancel uglify' prettify).
                                clear. constructor.
                            }
                            {
                                unfold vars_of; simpl. assumption.
                            }
                        }
                        {
                            specialize (IHlz ltac:(set_solver)).
                            destruct IHlz as [z [H1z H2z]].
                            exists z.
                            split.
                            {
                                rewrite map_app.
                                rewrite elem_of_app.
                                left. assumption.
                            }
                            {
                                assumption.
                            }
                    }
                }
                {
                    simpl in Hvars.
                    destruct (decide (x ∈ vars_of operand)).
                    {
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x0.
                        exists (term_operand operand).
                        rewrite map_app.
                        split.
                        {
                            rewrite elem_of_app.
                            right. ltac1:(rewrite /map).
                            rewrite (cancel uglify' prettify).
                            clear. constructor.
                        }
                        {
                            unfold vars_of; simpl. assumption.
                        }
                    }
                    {
                        specialize (IHlz ltac:(set_solver)).
                        destruct IHlz as [z [H1z H2z]].
                        exists z.
                        split.
                        {
                            rewrite map_app.
                            rewrite elem_of_app.
                            left. assumption.
                        }
                        {
                            assumption.
                        }
                    }
                }
            }
        }
        {
            destruct H as [z [H1z H2z]].
            ltac1:(replace map with (@fmap _ list_fmap) in H1z by reflexivity).
            rewrite elem_of_list_lookup in H1z.
            destruct H1z as [i Hi].
            rewrite list_lookup_fmap in Hi.
            unfold TermOver in *.
            destruct (lz !! i) eqn:Hlzi.
            {
                inversion Hi; subst; clear Hi.

                destruct (lx !! i) eqn:Hlxi.
                {
                    specialize (pf3 _ _ _ Hlxi Hlzi).
                    specialize (Htmp1 t0 (t_term cx lx)).
                    specialize (Htmp1 t H2z H0 pf3).
                    simpl in Htmp1.
                    clear - Htmp1 Hlxi.
                    apply take_drop_middle in Hlxi.
                    rewrite <- Hlxi in Htmp1.
                    rewrite sum_list_with_app in Htmp1.
                    simpl in Htmp1.
                    ltac1:(lia).
                }
                {
                    apply lookup_ge_None_1 in Hlxi.
                    apply lookup_lt_Some in Hlzi.
                    ltac1:(lia).
                }
            }
            {
                inversion Hi.
            }
        }
    }
Qed.

Lemma double_satisfies_contradiction_weaker
    {Σ : StaticModel}
    (ρ : Valuation)
    (ay : BuiltinOrVar)
    (cz cx : symbol)
    (lx : list (TermOver builtin_value))
    (lz : list (TermOver BuiltinOrVar))
    :
    vars_of_to_l2r ((t_over ay)) = vars_of_to_l2r ((t_term cz lz)) ->
    satisfies ρ (t_term cx lx) (t_over ay) ->
    satisfies ρ (t_term cx lx) (t_term cz lz) ->
    False
.
Proof.
    intros.
    eapply double_satisfies_contradiction>[|apply X|apply X0].
    apply set_eq.
    intros x.
    rewrite <- vars_of_uglify.
    rewrite <- vars_of_uglify.
    rewrite H.
    ltac1:(tauto).
Qed.

Lemma vars_of_apply_symbol
    {Σ : StaticModel}
    {T0 : Type}
    (s : T0)
    (l : list (Term' T0 BuiltinOrVar))
    :
    vars_of (apply_symbol'' s l) = union_list (fmap vars_of l)
.
Proof.
    induction l using rev_ind.
    {
        simpl. reflexivity.
    }
    {
        rewrite fmap_app.
        rewrite union_list_app_L.
        unfold apply_symbol'' in *; simpl in *.
        unfold vars_of in *; simpl in *.
        unfold to_PreTerm'' in *.
        rewrite fold_left_app.
        simpl.
        rewrite <- IHl. clear IHl.
        unfold helper''.
        ltac1:(repeat case_match); subst; simpl in *.
        {
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
    }
Qed.


Definition size_of_var_in_val
    {Σ : StaticModel}
    (ρ : Valuation)
    (x : variable)
    : nat
:=
    match ρ!!x with
    | None => 0
    | Some g => pred (TermOver_size (prettify g))
    end
.

Definition delta_in_val
    {Σ : StaticModel}
    (ρ : Valuation)
    (ψ : TermOver BuiltinOrVar)
    : nat
:=
    sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ)
.



Lemma concrete_is_larger_than_symbolic
    {Σ : StaticModel}
    (ρ : Valuation)
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
        inversion H1; subst; clear H1.
        apply (f_equal prettify) in H3.
        rewrite (cancel prettify uglify') in H3.
        subst φ.
        simpl.
        unfold delta_in_val.
        unfold vars_of_to_l2r.
        destruct z.
        {
            simpl. reflexivity.
        }
        {
            simpl.
            unfold size_of_var_in_val.
            inversion pf; subst; clear pf.
            rewrite H1. simpl.
            reflexivity.
        }
    }
    {
        simpl.
        destruct φ.
        {
            destruct a.
            {
                inversion H1; subst; clear H1.
                inversion X.
            }
            {
                inversion H1; subst; clear H1.
                inversion X; subst; clear X.
                simpl.
                unfold delta_in_val. simpl.
                unfold size_of_var_in_val.
                rewrite H1. simpl.
                unfold TermOver in *.
                apply f_equal.
                ltac1:(replace ((prettify' (to_PreTerm'' s (map uglify' l))))
                with ((t_term s l))).
                {
                    simpl. ltac1:(lia).
                }
                {
                    rewrite <- (cancel prettify uglify').
                    simpl.
                    reflexivity.
                }
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
    (ρ : Valuation)
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
    rewrite app_length in H5. simpl in H5.

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
                            rewrite take_length.
                            ltac1:(replace ((length l1 - length l1 `min` length lγ)) with 0 by lia).
                            simpl. reflexivity.
                        }
                        {
                            rewrite take_length.
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
                    rewrite drop_length.
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
                        rewrite app_length in H6.
                        rewrite app_length in H6.
                        rewrite take_length in H6.
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
                            rewrite app_length in H6.
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
                            rewrite app_length. simpl.
                            ltac1:(lia).
                        }
                    }
                    {
                        rewrite app_length.
                        rewrite app_length.
                        rewrite take_length.
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

Lemma sum_list_with_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 >= f2 x2) ->
    sum_list_with f1 l1 >= sum_list_with f2 l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 ≥ sum_list_with f2 l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.

Lemma sum_list_with_eq_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 = f2 x2) ->
    sum_list_with f1 l1 = sum_list_with f2 l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 = sum_list_with f2 l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.

Lemma sum_list_with_eq_plus_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (g : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 = f2 x2 + g x2) ->
    sum_list_with f1 l1 = sum_list_with f2 l2 + sum_list_with g l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 = sum_list_with f2 l2 + sum_list_with g l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.


Lemma subst_notin_2
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of (uglify' ψ) ->
    h ∉ vars_of (uglify' (TermOverBoV_subst φ h ψ))
.
Proof.
    induction φ; intros HH; simpl in *.
    {
        destruct a.
        {
            simpl. unfold vars_of; simpl. unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            destruct (decide (h = x)).
            {
                subst. apply HH.
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                ltac1:(set_solver).
            }
        }
    }
    {
        intros HContra. apply HH. clear HH.
        unfold apply_symbol'' in HContra; simpl in HContra.
        unfold to_PreTerm'' in HContra; simpl in HContra.
        unfold vars_of in HContra; simpl in HContra.
        revert s ψ  H HContra.
        induction l using rev_ind; intros s ψ HH HContra.
        {
            simpl in *. inversion HContra.
        }
        {
            rewrite Forall_app in HH.
            rewrite map_app in HContra.
            rewrite map_app in HContra.
            rewrite fold_left_app in HContra.
            simpl in HContra.
            destruct HH as [HH1 HH2].
            rewrite Forall_cons in HH2.
            destruct HH2 as [HH2 _].
            specialize (IHl s ψ HH1).
            simpl in *.
            unfold helper in HContra.
            destruct (uglify' (TermOverBoV_subst x h ψ)) eqn:Hugl.
            {
                unfold vars_of in HContra; simpl in HContra.
                rewrite elem_of_union in HContra.
                destruct HContra as [HContra|HContra].
                {
                    specialize (IHl HContra).
                    apply IHl.
                }
                {
                    destruct (decide (h ∈ vars_of (uglify' ψ))) as [Hyes|Hno].
                    {
                        assumption.
                    }
                    {
                        specialize (HH2 Hno). clear Hno. ltac1:(exfalso).
                        unfold vars_of in HH2; simpl in HH2.
                        unfold vars_of in HH2; simpl in HH2.
                        apply HH2. exact HContra.
                    }
                }
            }
            {
                unfold vars_of in HContra; simpl in HContra.
                rewrite elem_of_union in HContra.
                destruct HContra as [HContra|HContra].
                {
                    simpl in *.
                    destruct (decide (h ∈ vars_of (uglify' ψ))) as [Hyes|Hno].
                    {
                        assumption.
                    }
                    {
                        specialize (HH2 Hno). clear Hno. ltac1:(exfalso).
                        unfold vars_of in HH2; simpl in HH2.
                        unfold vars_of in HH2; simpl in HH2.
                        apply HH2. exact HContra.
                    }
                }
                {

                    specialize (IHl HContra).
                    apply IHl.
                }
            }
        }
    }
Qed.

(*
Lemma subst_preserves_or_increases_delta
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ1 γ2 : TermOver builtin_value)
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of (uglify' ψ) ->
    h ∉ vars_of ρ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    satisfies ρ γ1 φ ->
    satisfies ρ γ2 (TermOverBoV_subst φ h ψ) ->
    (((TermOver_size γ2)) = (((TermOver_size (TermOverBoV_subst φ h ψ))) + (delta_in_val ρ φ ) + (delta_in_val ρ ψ)))
.
Proof.
    intros Hnotinpsi Hnotinrho Hfilter Hsat1 Hsat2.


    revert γ1 γ2 Hnotinpsi Hnotinrho Hfilter Hsat1 Hsat2.
    induction φ; intros γ1 γ2 Hnotinpsi Hnotinrho Hfilter Hsat1 Hsat2.
    {
        simpl in *.
        destruct a; simpl in *.
        {
            ltac1:(lia).
        }
        {
            rewrite filter_cons in Hfilter.
            destruct (decide (h = x)).
            {
                subst.
                simpl in *.
                apply concrete_is_larger_than_symbolic in Hsat2.
                inversion Hsat1; subst; clear Hsat1.
                {
                    apply (f_equal prettify) in H1.
                    rewrite (cancel prettify uglify') in H1.
                    subst. simpl in *.
                    unfold delta_in_val. simpl.
                    inversion pf; subst; clear pf.
                    unfold size_of_var_in_val.
                    rewrite H1. simpl. rewrite Hsat2. clear Hsat2.
                    unfold delta_in_val. unfold size_of_var_in_val.
                    ltac1:(lia).
                }
                {
                    apply (f_equal prettify) in H1.
                    rewrite (cancel prettify uglify') in H1.
                    subst. simpl in *.
                    inversion X; subst; clear X.
                    clear -H0 Hnotinrho.
                    unfold vars_of in Hnotinrho; simpl in Hnotinrho.
                    rewrite elem_of_dom in Hnotinrho.
                    ltac1:(rewrite H0 in Hnotinrho).
                    ltac1:(exfalso).
                    apply Hnotinrho.
                    unfold is_Some. exists (term_preterm axy).
                    reflexivity.
                }
            }
            {
                simpl in Hfilter. ltac1:(lia).
            }
        }
    }
    {
        simpl in *.
        apply satisfies_term_bov_inv in Hsat2.
        destruct Hsat2 as [lγ [[H1 H2] H3]].
        subst. simpl in *.
        rewrite map_length in H2.

        apply satisfies_term_bov_inv in Hsat1.
        destruct Hsat1 as [l'γ [[H4 H5] H6]].
        subst. simpl in *.
        clear Hnotover.

        assert (Hconcat: h ∈ concat (map vars_of_to_l2r l)).
        {
            clear -Hfilter.
            induction l; simpl in *.
            { ltac1:(lia). }
            {
                rewrite filter_app in Hfilter.
                rewrite app_length in Hfilter.
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
        rewrite <- elem_of_list_In in H2x0.
        rewrite elem_of_list_lookup in H2x0.
        destruct H2x0 as [i Hi].
        assert (H'i := Hi).
        apply take_drop_middle in Hi.
        rewrite <- Hi.
        rewrite <- Hi in Hfilter.
        rewrite <- Hi in H3.
        rewrite map_app in H3.
        rewrite map_app.
        rewrite sum_list_with_app.
        simpl in *.

        destruct (lγ !! i) eqn:Hlγi.
        {
            destruct (l'γ !! i) eqn:Hl'γi.
            {
                apply take_drop_middle in Hlγi.
                apply take_drop_middle in Hl'γi.
                rewrite <- Hlγi.
                rewrite sum_list_with_app.
                simpl.
                rewrite <- Hi in H.
                rewrite Forall_app in H.
                destruct H as [IH1 IH2].
                rewrite Forall_cons in IH2.
                destruct IH2 as [IH2 IH3].
                rewrite <- Hlγi in H3.

                assert (
                        (sum_list_with
                            (S ∘ TermOver_size)
                            (take i lγ)) =
                        (sum_list_with
                            (S ∘ TermOver_size)
                            (take i l)
                        ) +
                        sum_list_with (delta_in_val ρ) (take i l)).
                {
                    apply sum_list_with_eq_plus_pairwise.
                    {
                        rewrite take_length.
                        rewrite take_length.
                        ltac1:(lia).
                    }
                    {
                        intros i0 x1 x2 HH1 HH2.
                        unfold compose. simpl.
                        simpl in HH2.
                        assert (HH'1 := HH1).
                        rewrite lookup_take in HH2.
                        {
                            destruct (l !! i0) eqn:H'li0.
                            {
                                simpl in HH2. inversion HH2.
                                subst; clear HH2.
                                
                                assert (Hhx2: h ∉ vars_of_to_l2r x2).
                                {
                                    {
                                        intros HContra.
                                        rewrite map_app in Hfilter.
                                        rewrite concat_app in Hfilter.
                                        assert (H_i0_lt_i: i0 < i).
                                        {
                                            apply lookup_lt_Some in HH1.
                                            rewrite take_length in HH1.
                                            ltac1:(lia).
                                        }
                                        simpl in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        simpl in Hfilter.
                                        rewrite app_length in Hfilter.
                                        rewrite app_length in Hfilter.
                                        assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (take i l))))).
                                        {
                                            destruct ((take i l) !! i0) eqn:Heq.
                                            {
                                                assert (Heq' := Heq).
                                                apply take_drop_middle in Heq.
                                                rewrite <- Heq.
                                                rewrite map_app.
                                                rewrite concat_app.
                                                rewrite filter_app.
                                                simpl.
                                                rewrite filter_app.
                                                apply lookup_take_Some in Heq'.
                                                rewrite H'li0 in Heq'.
                                                destruct Heq' as [Heq'1 _].
                                                inversion Heq'1; subst; clear Heq'1.
                                                rewrite app_length.
                                                rewrite app_length.
                                                rewrite elem_of_list_lookup in HContra.
                                                destruct HContra as [j Hj].
                                                apply take_drop_middle in Hj.
                                                rewrite <- Hj.
                                                rewrite filter_app.
                                                rewrite app_length.
                                                rewrite filter_cons.
                                                destruct (decide (h = h))>[|ltac1:(contradiction)].
                                                simpl.
                                                ltac1:(lia).
                                            }
                                            {
                                                apply lookup_ge_None_1 in Heq.
                                                rewrite take_length in Heq.
                                                apply lookup_lt_Some in H'li0.
                                                ltac1:(lia).
                                            }
                                        }
                                        (* TODO this should be extracted somehow somewhere *)
                                        clear -Hfilter H2x H'i Htmp.
                                        apply take_drop_middle in H'i.
                                        rewrite <- H'i in Hfilter at 2.
                                        rewrite drop_app in Hfilter.
                                        rewrite map_app in Hfilter.
                                        rewrite concat_app in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        rewrite app_length in Hfilter.
                                        rewrite <- elem_of_list_In in H2x.
                                        assert (H'2x := H2x).
                                        rewrite elem_of_list_lookup in H2x.
                                        destruct H2x as [i0 H2x].
                                        apply take_drop_middle in H2x.
                                        rewrite <- H2x in Hfilter.
                                        rewrite take_length in Hfilter.
                                        simpl in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        rewrite filter_cons in Hfilter.
                                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                                        rewrite app_length in Hfilter.
                                        simpl in Hfilter.
                                        ltac1:(lia).
                                    }
                                }
                                apply f_equal.
                                apply concrete_is_larger_than_symbolic.
                                eapply H3 with (i := i0).
                                {
                                    rewrite lookup_app_l.
                                    {
                                        apply HH'1.
                                    }
                                    {
                                        apply lookup_lt_Some in HH'1.
                                        rewrite take_length.
                                        rewrite take_length in HH'1.
                                        ltac1:(lia).
                                    }
                                }
                                rewrite lookup_app_l.
                                {
                                    ltac1:(replace (map) with (@fmap _ list_fmap) by reflexivity).
                                    rewrite list_lookup_fmap.
                                    rewrite lookup_take.
                                    {
                                        rewrite H'li0. simpl.
                                        rewrite subst_notin.
                                        {
                                            reflexivity.
                                        }
                                        {
                                            apply Hhx2.
                                        }
                                    }
                                    {
                                        apply lookup_lt_Some in HH'1.
                                        rewrite take_length in HH'1.
                                        ltac1:(lia).                                        
                                    }
                                }
                                {
                                    rewrite map_length.
                                    apply lookup_lt_Some in HH'1.
                                    rewrite take_length.
                                    rewrite take_length in HH'1.
                                    ltac1:(lia).
                                }
                            }
                            {
                                simpl in HH2. inversion HH2.
                            }
                        }
                        {
                            apply lookup_lt_Some in HH1.
                            rewrite take_length in HH1.
                            ltac1:(lia).
                        }
                    }
                }

                assert (
                        (sum_list_with
                            (S ∘ TermOver_size)
                            (drop (S i) lγ)) =
                        (sum_list_with
                            (S ∘ TermOver_size)
                            (drop (S i) l)
                        ) +
                        sum_list_with (delta_in_val ρ) (drop (S i) l)).
                {
                    apply sum_list_with_eq_plus_pairwise.
                    {
                        rewrite drop_length.
                        rewrite drop_length.
                        ltac1:(lia).
                    }
                    {
                        intros i0 x1 x2 HH1 HH2.
                        unfold compose. simpl.
                        simpl in HH2.
                        assert (HH'1 := HH1).
                        rewrite lookup_drop in HH2.
                        {
                            destruct (l !! i0) eqn:H'li0.
                            {
                                simpl in HH2. inversion HH2.
                                subst; clear HH2.
                                
                                assert (Hhx2: h ∉ vars_of_to_l2r x2).
                                {
                                    {
                                        intros HContra.
                                        rewrite map_app in Hfilter.
                                        rewrite concat_app in Hfilter.
                                        simpl in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        simpl in Hfilter.
                                        rewrite app_length in Hfilter.
                                        rewrite app_length in Hfilter.
                                        ltac1:(
                                            replace ( S (i + i0))
                                            with ((S i) + i0)
                                            in H1
                                            by lia
                                        ).
                                        ltac1:(rewrite <- lookup_drop in H1).
                                        apply take_drop_middle in H1.
                                        rewrite <- H1 in Hfilter.
                                        rewrite map_app in Hfilter.
                                        rewrite concat_app in Hfilter.
                                        simpl in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        rewrite app_length in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        rewrite app_length in Hfilter.
                                        rewrite elem_of_list_lookup in HContra.
                                        destruct HContra as [j HContra].
                                        apply take_drop_middle in HContra.
                                        rewrite <- HContra in Hfilter.
                                        rewrite filter_app in Hfilter.
                                        rewrite filter_cons in Hfilter.
                                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                                        rewrite app_length in Hfilter.
                                        simpl in Hfilter.
                                        rewrite <- elem_of_list_In in H2x.
                                        rewrite elem_of_list_lookup in H2x.
                                        destruct H2x as [j' H2x].
                                        apply take_drop_middle in H2x.
                                        rewrite <- H2x in Hfilter.
                                        clear -Hfilter.
                                        rewrite filter_app in Hfilter.
                                        rewrite filter_cons in Hfilter.
                                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                                        simpl in Hfilter.
                                        rewrite app_length in Hfilter.
                                        simpl in Hfilter.
                                        ltac1:(lia).
                                    }
                                }
                                
                                apply f_equal.
                                apply concrete_is_larger_than_symbolic.
                                apply H3 with (i := S i0 + (i `min` length lγ)).
                                {
                                    rewrite lookup_app_r.
                                    rewrite take_length.
                                    ltac1:(
                                        replace (S i0 + i `min` length lγ - i `min` length lγ)
                                        with (S i0)
                                        by lia
                                    ).
                                    rewrite <- HH1.
                                    simpl. reflexivity.
                                    {
                                        rewrite take_length.
                                        ltac1:(lia).
                                    }
                                }
                                rewrite lookup_app_r.
                                {
                                    rewrite map_length.
                                    rewrite take_length.
                                    ltac1:(
                                        replace (S i0 + i `min` length lγ - i `min` length l)
                                        with (S i0)
                                        by lia
                                    ).
                                    simpl.
                                    ltac1:(replace (map) with (@fmap _ list_fmap) by reflexivity).
                                    rewrite list_lookup_fmap.
                                    rewrite lookup_drop.
                                    simpl.
                                    rewrite H1.
                                    simpl.
                                    rewrite subst_notin.
                                    {
                                        reflexivity.
                                    }
                                    {
                                        exact Hhx2.
                                    }
                                }
                                {
                                    rewrite map_length.
                                    rewrite take_length.
                                    ltac1:(lia).
                                }
                            }
                            {
                                apply lookup_ge_None_1 in H'li0.
                                apply lookup_lt_Some in HH'1.
                                rewrite drop_length in HH'1.
                                ltac1:(lia).
                            }
                        }
                    }
                }
                
                    (* new attempt:*)
                    (*injection Hsz as Hsz.*)
                rewrite <- Hi in H6.
                rewrite <- Hl'γi in H6.

                specialize (IH2 t0 t).

                remember ((sum_list_with (S ∘ TermOver_size) (take i lγ))) as Y1.
                remember ((sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (take i l)))) as Y1'.
                remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) lγ) ) as Y2.
                remember ( sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (drop (S i) l)) ) as Y2'.
                remember (sum_list_with (S ∘ TermOver_size) (take i l)) as Y3.
                remember (sum_list_with (S ∘ TermOver_size) (take i l'γ)) as Y3'.
                remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) l) ) as Y4.
                remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) l'γ) ) as Y4'.


                specialize (IH2 ltac:(assumption) ltac:(assumption)).
                ltac1:(ospecialize (IH2 _)).
                {
                    rewrite map_app in Hfilter.
                    rewrite concat_app in Hfilter.
                    rewrite filter_app in Hfilter.
                    rewrite app_length in Hfilter.
                    simpl in Hfilter.
                    clear - H2x Hfilter.
                    rewrite filter_app in Hfilter.
                    rewrite app_length in Hfilter.
                    ltac1:(cut (length (filter (eq h) (vars_of_to_l2r x0)) >= 1)).
                    {
                        intros HH. ltac1:(lia).
                    }
                    clear Hfilter.
                    rewrite <- elem_of_list_In in H2x.
                    rewrite elem_of_list_lookup in H2x.
                    destruct H2x as [j Hj].
                    apply take_drop_middle in Hj.
                    rewrite <- Hj. clear Hj.
                    rewrite filter_app. 
                    simpl. 
                    rewrite app_length.
                    rewrite filter_cons.
                    destruct (decide (h = h))>[|ltac1:(contradiction)].
                    simpl.
                    ltac1:(lia).
                }
                ltac1:(ospecialize (IH2 _ _)).
                {
                    apply H6 with (i := length (take i l'γ)).
                    {
                        rewrite lookup_app_r.
                        {
                            rewrite Nat.sub_diag.
                            reflexivity.
                        }
                        {
                            ltac1:(lia).
                        }
                    }
                    {
                        rewrite lookup_app_r.
                        {
                            do 2 (rewrite take_length).
                            rewrite H5.
                            rewrite Nat.sub_diag.
                            reflexivity.
                        }
                        {
                            do 2 (rewrite take_length).
                            ltac1:(lia).
                        }
                    }
                }
                {
                    eapply H3 with (i := length (take i l)).
                    {
                        rewrite lookup_app_r.
                        {
                            rewrite take_length.
                            rewrite take_length.
                            rewrite H2.
                            rewrite Nat.sub_diag.
                            reflexivity.
                        }
                        {
                            rewrite take_length.
                            rewrite take_length.
                            ltac1:(lia).
                        }
                    }
                    {
                        rewrite lookup_app_r.
                        {
                            rewrite take_length.
                            rewrite map_length.
                            rewrite take_length.
                            rewrite H2.
                            rewrite Nat.sub_diag.
                            reflexivity.
                        }
                        {
                            rewrite take_length.
                            rewrite map_length.
                            rewrite take_length.
                            ltac1:(lia).
                        } 
                    }
                }

                unfold delta_in_val.
                simpl.
                rewrite map_app. simpl.
                rewrite concat_app. simpl.
                apply f_equal.
                rewrite sum_list_with_app.
                rewrite sum_list_with_app.
                subst.
                remember (sum_list_with (S ∘ TermOver_size) (take i lγ)) as B1.
                remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) lγ) ) as B2.
                remember ( sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (take i l)) ) as B3.
                remember ( sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (drop (S i) l))) as B4.
                remember ( sum_list_with (size_of_var_in_val ρ) (concat (map vars_of_to_l2r (take i l)) )) as B5.
                remember ( sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r x0) ) as B6.
                remember ( sum_list_with (size_of_var_in_val ρ) (concat (map vars_of_to_l2r (drop (S i) l)))) as B7.
                remember ( delta_in_val ρ x0 ) as DX0.
                unfold delta_in_val in *. simpl in *.
                remember (sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ)) as Dψ.
                remember ((TermOver_size (TermOverBoV_subst x0 h ψ))) as Bsubst.
                remember (sum_list_with (size_of_var_in_val ρ)) as F.
                remember ((vars_of_to_l2r (TermOverBoV_subst x0 h ψ))) as VS.
                
                (*
                    rewrite zip_with_app in H6.
                    {
                        simpl in H6.
                        rewrite Forall_app in H6.
                        rewrite Forall_cons in H6.
                        destruct H6 as [H61 [H62 H63]].



                        assert (H32' := H32).
                        assert (H62' := H62).
                        apply concrete_is_larger_than_symbolic in H32'.
                        apply concrete_is_larger_than_symbolic in H62'.



                        apply concrete_is_larger_than_symbolic in H32.
                        apply concrete_is_larger_than_symbolic in H62.
                        *)
                        
                        rewrite H32'.



                        ltac1:(cut(B1 + (F VS + B2) = B3 + (B4) + (B5 + (B6 + B7)) + Dψ)).
                        {
                            intros HH. ltac1:(lia).
                        }

                        assert (Htmp1: DX0 + Dψ = F VS).
                        {
                            ltac1:(lia).
                        }
                        rewrite <- Htmp1.

                        ltac1:( cut (B1 + (DX0 + B2) = B3 + B4 + (B5 + (B6 + B7))) ).
                        {
                            intros HH. ltac1:(lia).
                        }

                        clear H32'.

                        rewrite <- Htmp1 in H32. clear Htmp1.
                        rewrite sum_list_with_compose in HeqB2.
                        ltac1:(rewrite sum_list_with_compose in HeqB2).
                        rewrite sum_list_with_compose in HeqB1.
                        ltac1:(rewrite sum_list_with_compose in HeqB1).
                        ltac1:(rewrite sum_list_with_compose in HeqB4).
                        unfold compose in HeqB4.
                        ltac1:(rewrite sum_list_with_S in HeqB4).
                        rewrite fmap_length in HeqB4.
                        rewrite map_length in HeqB4.
                        rewrite drop_length in HeqB4.
                        ltac1:(rewrite sum_list_with_compose in H0).
                        unfold compose in H0.
                        ltac1:(rewrite sum_list_with_S in H0).
                        rewrite fmap_length in H0.
                        rewrite drop_length in H0.
                        subst F.
                        unfold compose in HeqB1.
                        ltac1:(rewrite sum_list_with_S in HeqB1).
                        ltac1:(replace (@fmap _ list_fmap) with map in HeqB1 by reflexivity).
                        rewrite map_id in HeqB1.
                        rewrite map_length in HeqB1.
                        rewrite take_length in HeqB1.
                        unfold compose in HeqB2.
                        ltac1:(replace (@fmap _ list_fmap) with map in HeqB2 by reflexivity).
                        rewrite map_id in HeqB2.
                        rewrite sum_list_with_S in HeqB2.
                        rewrite map_length in HeqB2.
                        rewrite drop_length in HeqB2.
                        rewrite sum_list_with_compose in HeqB3.
                        unfold compose in HeqB3.
                        rewrite sum_list_with_S in HeqB3.
                        rewrite fmap_length in HeqB3.
                        rewrite map_length in HeqB3.
                        rewrite take_length in HeqB3.
                        rewrite sum_list_with_compose in H.
                        unfold compose in H.
                        rewrite sum_list_with_S in H.
                        rewrite fmap_length in H.
                        rewrite take_length in H.
                        

                        ltac1:(replace map with (@fmap _ list_fmap) in HeqB3 by reflexivity).
                        subst.
                        (* the only use of [TermOver_size t] *)
                        clear H32 IH2.

                        assert (H0': sum_list (map TermOver_size (drop (S i) lγ))
                        = sum_list (TermOver_size <$> drop (S i) l)
                        + sum_list_with (λ ψ0 : TermOver BuiltinOrVar,  sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0)) (drop (S i) l) ).
                        {
                            ltac1:(lia).
                        }
                        clear H0.
                        rewrite H0'.
                        clear Hlγi H0' H33.

                        assert(HeqB1': sum_list (TermOver_size <$> take i l) + sum_list_with (λ ψ0 : TermOver BuiltinOrVar, sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0)) (take i l) = sum_list (map TermOver_size (take i lγ))).
                        {
                            ltac1:(lia).
                        }
                        clear HeqB1. clear H31.
                        clear H61 H62'.
                        ltac1:(
                            replace
                            (sum_list_with
                                (λ ψ0 : TermOver BuiltinOrVar,
                                sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0))
                                (take i l))
                            with
                            (sum_list_with ((sum_list_with (size_of_var_in_val ρ)) ∘ vars_of_to_l2r) (take i l) )
                            in HeqB1'
                            by reflexivity
                        ).
                        rewrite sum_list_with_compose in HeqB1'.
                        ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                        repeat (rewrite sum_list_fmap).
                        repeat (rewrite sum_list_fmap in HeqB1').
                        ltac1:(
                            replace
                            (sum_list_with (λ ψ0 : TermOver BuiltinOrVar, sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0)))
                            with
                            (sum_list_with (sum_list_with (size_of_var_in_val ρ) ∘ (vars_of_to_l2r)))
                            by reflexivity
                        ).
                        repeat (rewrite sum_list_with_compose).
                        repeat (rewrite sum_list_fmap).
                        unfold compose.
                        do 2 (rewrite sum_list_with_sum_list_with).
                        remember ((sum_list_with (size_of_var_in_val ρ) (concat (vars_of_to_l2r <$> take i l)) )) as N1.
                        remember (sum_list_with TermOver_size (take i l)) as N0.
                        remember (sum_list_with TermOver_size ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> take i l)) as N0'.
                        remember ((sum_list_with TermOver_size (drop (S i) l) )) as N3.
                        remember ( (sum_list_with TermOver_size ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> drop (S i) l) )) as N3'.
                        remember ( (sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r x0) ) ) as N2.
                        remember ( sum_list_with (size_of_var_in_val ρ) (concat (vars_of_to_l2r <$> drop (S i) l)) ) as N4.

                        ltac1:(assert (N0 = (N0'))).
                        {
                            (* TODO reuse in the N3=N3' case *)
                            subst N0 N0'.
                            apply sum_list_with_eq_pairwise.
                            {
                                rewrite fmap_length.
                                reflexivity.
                            }
                            {
                                intros i0 x1 x2 Hx1 Hx2.
                                rewrite list_lookup_fmap in Hx2.
                                simpl in Hx2.
                                rewrite Hx1 in Hx2. simpl in Hx2.
                                rewrite subst_notin in Hx2.
                                {
                                    inversion Hx2; subst; clear Hx2.
                                    reflexivity.
                                }
                                {
                                    intros HContra.
                                    rewrite map_app in Hfilter.
                                    rewrite concat_app in Hfilter.
                                    assert (H_i0_lt_i: i0 < i).
                                    {
                                        apply lookup_lt_Some in Hx1.
                                        rewrite take_length in Hx1.
                                        ltac1:(lia).
                                    }
                                    simpl in Hfilter.
                                    rewrite filter_app in Hfilter.
                                    rewrite filter_app in Hfilter.
                                    simpl in Hfilter.
                                    rewrite app_length in Hfilter.
                                    rewrite app_length in Hfilter.
                                    assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (take i l))))).
                                    {
                                        destruct ((take i l) !! i0) eqn:Heq.
                                        {
                                            assert (Heq' := Heq).
                                            apply take_drop_middle in Heq.
                                            rewrite <- Heq.
                                            rewrite map_app.
                                            rewrite concat_app.
                                            rewrite filter_app.
                                            simpl.
                                            rewrite filter_app.
                                            apply lookup_take_Some in Heq'.
                                            inversion Hx1; subst; clear Hx1.
                                            destruct Heq' as [Heq'1 _].
                                            inversion Heq'1; subst; clear Heq'1.
                                            rewrite app_length.
                                            rewrite app_length.
                                            rewrite elem_of_list_lookup in HContra.
                                            destruct HContra as [j Hj].
                                            apply take_drop_middle in Hj.
                                            rewrite <- Hj.
                                            rewrite filter_app.
                                            rewrite app_length.
                                            rewrite filter_cons.
                                            destruct (decide (h = h))>[|ltac1:(contradiction)].
                                            simpl.
                                            ltac1:(lia).
                                        }
                                        {
                                            apply lookup_ge_None_1 in Heq.
                                            rewrite take_length in Heq.
                                            inversion Hx1.
                                        }
                                    }
                                    clear -Hfilter H2x H'i Htmp.
                                    apply take_drop_middle in H'i.
                                    rewrite <- H'i in Hfilter at 2.
                                    rewrite drop_app in Hfilter.
                                    rewrite map_app in Hfilter.
                                    rewrite concat_app in Hfilter.
                                    rewrite filter_app in Hfilter.
                                    rewrite app_length in Hfilter.
                                    rewrite <- elem_of_list_In in H2x.
                                    assert (H'2x := H2x).
                                    rewrite elem_of_list_lookup in H2x.
                                    destruct H2x as [i0 H2x].
                                    apply take_drop_middle in H2x.
                                    rewrite <- H2x in Hfilter.
                                    rewrite take_length in Hfilter.
                                    simpl in Hfilter.
                                    rewrite filter_app in Hfilter.
                                    rewrite filter_cons in Hfilter.
                                    destruct (decide (h=h))>[|ltac1:(contradiction)].
                                    rewrite app_length in Hfilter.
                                    simpl in Hfilter.
                                    ltac1:(lia).
                                }
                            }
                        }

                        ltac1:(assert(N3 = N3')).
                        {
                            subst N3 N3'.

                            apply sum_list_with_eq_pairwise.
                            {
                                rewrite fmap_length.
                                reflexivity.
                            }
                            {
                                intros i0 x1 x2 Hx1 Hx2.
                                rewrite list_lookup_fmap in Hx2.
                                simpl in Hx2.
                                rewrite Hx1 in Hx2. simpl in Hx2.
                                rewrite subst_notin in Hx2.
                                {
                                    inversion Hx2; subst; clear Hx2.
                                    reflexivity.
                                }
                                {
                                    clear Hx2.
                                    intros HContra.
                                    rewrite map_app in Hfilter.
                                    rewrite concat_app in Hfilter.
                                    (*
                                    assert (H_i0_lt_i: i0 < i).
                                    {
                                        apply lookup_lt_Some in Hx1.
                                        rewrite take_length in Hx1.
                                        ltac1:(lia).
                                    }
                                    *)
                                    simpl in Hfilter.
                                    rewrite filter_app in Hfilter.
                                    rewrite filter_app in Hfilter.
                                    simpl in Hfilter.
                                    rewrite app_length in Hfilter.
                                    rewrite app_length in Hfilter.
                                    assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (drop (S i) l))))).
                                    {
                                        destruct ((drop (S i) l) !! i0) eqn:Heq.
                                        {
                                            assert (Heq' := Heq).
                                            apply take_drop_middle in Heq.
                                            rewrite <- Heq.
                                            rewrite map_app.
                                            rewrite concat_app.
                                            rewrite filter_app.
                                            simpl.
                                            rewrite filter_app.
                                            inversion Hx1; subst; clear Hx1.
                                            (*
                                            apply lookup_take_Some in Heq'.
                                            inversion Hx1; subst; clear Hx1.
                                            destruct Heq' as [Heq'1 _].
                                            inversion Heq'1; subst; clear Heq'1.
                                            *)
                                            rewrite app_length.
                                            rewrite app_length.
                                            rewrite elem_of_list_lookup in HContra.
                                            destruct HContra as [j Hj].
                                            apply take_drop_middle in Hj.
                                            rewrite <- Hj.
                                            rewrite filter_app.
                                            rewrite app_length.
                                            rewrite filter_cons.
                                            destruct (decide (h = h))>[|ltac1:(contradiction)].
                                            simpl.
                                            ltac1:(lia).
                                        }
                                        {
                                            inversion Hx1.
                                        }
                                    }
                                    ltac1:(cut (length (filter (eq h) (vars_of_to_l2r x0)) >= 1)).
                                    {
                                        intros HH. ltac1:(lia).
                                    }
                                    clear Hfilter.
                                    rewrite <- elem_of_list_In in H2x.
                                    rewrite elem_of_list_lookup in H2x.
                                    destruct H2x as [j Hj].
                                    apply take_drop_middle in Hj.
                                    rewrite <- Hj. clear Hj.
                                    rewrite filter_app. 
                                    simpl. 
                                    rewrite app_length.
                                    rewrite filter_cons.
                                    destruct (decide (h = h))>[|ltac1:(contradiction)].
                                    simpl.
                                    ltac1:(lia).
                                }
                            }
                        }

                        ltac1:(lia).
                    }
                    {
                        rewrite take_length.
                        rewrite take_length.
                        ltac1:(lia).
                    }
                }
                {
                    rewrite map_length.
                    rewrite take_length.
                    rewrite take_length.
                    ltac1:(lia).
                }
                
            }
            {
                apply lookup_ge_None_1 in Hl'γi.
                apply lookup_lt_Some in H'i.
                ltac1:(lia).                
            }
        }
        {
            apply lookup_ge_None_1 in Hlγi.
            apply lookup_lt_Some in H'i.
            ltac1:(lia).
        }
    }
Qed.
*)

Lemma list_filter_Forall_not
    {T : Type}
    (P : T -> Prop)
    {_dP : forall x, Decision (P x)}
    (l : list T)
    :
    Forall (fun x => not (P x)) l ->
    filter P l = []
.
Proof.
    induction l; simpl; intros H.
    {
        reflexivity.
    }
    {
        apply Forall_cons in H.
        destruct H as [H1 H2].
        specialize (IHl H2). clear H2.
        rewrite filter_cons.
        destruct (decide (P a)).
        {
            ltac1:(contradiction).
        }
        apply IHl.
    }
Qed.


Lemma list_filter_Forall_all
    {T : Type}
    (P : T -> Prop)
    {_dP : forall x, Decision (P x)}
    (l : list T)
    :
    Forall P l ->
    filter P l = l
.
Proof.
    induction l; simpl; intros H.
    {
        reflexivity.
    }
    {
        apply Forall_cons in H.
        destruct H as [H1 H2].
        specialize (IHl H2). clear H2.
        rewrite filter_cons.
        destruct (decide (P a)).
        {
            rewrite IHl. reflexivity.
        }
        ltac1:(contradiction).
    }
Qed.

Lemma TermOver_size_not_zero
    {Σ : StaticModel}
    {A : Type}
    (t : TermOver A)
    : TermOver_size t <> 0
.
Proof.
    destruct t; simpl; ltac1:(lia).
Qed.

Lemma TermOverBoV_subst_once_size
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of (uglify' ψ) ->
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
        rewrite fmap_length.

        assert (Hconcat: h ∈ concat (map vars_of_to_l2r l)).
        {
            clear -Hexactlyonce.
            induction l; simpl in *.
            { ltac1:(lia). }
            {
                rewrite filter_app in Hexactlyonce.
                rewrite app_length in Hexactlyonce.
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
        rewrite app_length.
        rewrite sum_list_with_app.
        rewrite map_app.
        rewrite sum_list_with_app.
        simpl.

        rewrite <- Hj in Hexactlyonce.
        rewrite map_app in Hexactlyonce. simpl in Hexactlyonce.
        rewrite concat_app in Hexactlyonce. simpl in Hexactlyonce.
        do 2 (rewrite filter_app in Hexactlyonce).
        do 2 (rewrite app_length in Hexactlyonce).
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
                rewrite app_length.
                rewrite app_length.
                rewrite elem_of_list_lookup in HContra.
                destruct HContra as [k Hk].
                apply take_drop_middle in Hk.
                rewrite <- Hk.
                rewrite filter_app.
                rewrite app_length.
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
            rewrite app_length in Hexactlyonce.
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
                rewrite app_length.
                rewrite app_length.
                rewrite elem_of_list_lookup in HContra.
                destruct HContra as [k Hk].
                apply take_drop_middle in Hk.
                rewrite <- Hk.
                rewrite filter_app.
                rewrite app_length.
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
            rewrite app_length in Hexactlyonce.
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
        rewrite take_length.
        rewrite drop_length.

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
        rewrite app_length.
        simpl.
        rewrite drop_length.
        rewrite take_length.
        ltac1:(lia).
    }
Qed.

Lemma count_one_split
    {T : Type}
    (P : T -> Prop)
    (_dP : forall x, Decision (P x))
    (l : list T)
    :
    length (filter P l) = 1 ->
    exists (la : list T) (b : T) (lc : list T),
    l = la ++ b::lc
    /\ P b
    /\ Forall (fun x => not (P x)) la
    /\ Forall (fun x => not (P x)) lc
.
Proof.
    remember (list_find P l) as lf.
    destruct lf.
    {
        symmetry in Heqlf.
        destruct p.
        apply list_find_Some in Heqlf.
        intros HH.
        destruct Heqlf as [H1 [H2 H3]].
        apply take_drop_middle in H1.
        exists (take n l).
        exists t.
        exists (drop (S n) l).
        split.
        {
            symmetry. exact H1.
        }
        split>[exact H2|].
        split.
        {
            rewrite Forall_forall.
            intros x Hx.
            rewrite elem_of_list_lookup in Hx.
            destruct Hx as [i Hi].
            rewrite lookup_take_Some in Hi.
            destruct Hi as [Hi H'i].
            eapply H3.
            { apply Hi. }
            { apply H'i. }
        }
        {
            rewrite Forall_forall.
            intros x Hx HContra.
            rewrite elem_of_list_lookup in Hx.
            destruct Hx as [i Hi].
            apply take_drop_middle in Hi.
            rewrite <- Hi in H1.
            rewrite <- H1 in HH.
            clear H1 Hi.
            rewrite filter_app in HH.
            rewrite filter_cons in HH.
            destruct (decide (P t))>[|ltac1:(contradiction)].
            rewrite filter_app in HH.
            rewrite filter_cons in HH.
            destruct (decide (P x))>[|ltac1:(contradiction)].
            rewrite app_length in HH. simpl in HH.
            rewrite app_length in HH. simpl in HH.
            ltac1:(lia).
        }
    }
    {
        symmetry in Heqlf.
        apply list_find_None in Heqlf.
        intros Hlength.
        apply length_filter_l_1_impl_h_in_l' in Hlength.
        destruct Hlength as [h [H1h H2h]].
        rewrite Forall_forall in Heqlf.
        ltac1:(exfalso).
        ltac1:(naive_solver).
    }
Qed.

Lemma length_filter_eq__eq__length_filter_in__zero
    {T : Type}
    {_edT: EqDecision T}
    (h : T)
    (l : list (list T))
    :
    length (filter (eq h) (concat l)) = 0 ->
    length (filter (elem_of h) l) = 0
.
Proof.
    induction l; simpl; intros HH.
    {
        ltac1:(lia).
    }
    {
        rewrite filter_app in HH.
        rewrite filter_cons.
        destruct (decide (h ∈ a)) as [Hin|Hnotin].
        {
            simpl. rewrite app_length in HH.
            assert(Htmp := h_in_l_impl_length_filter_l_gt_1 (eq h) a h Hin eq_refl).
            ltac1:(exfalso).
            ltac1:(lia).
        }
        {
            simpl. rewrite app_length in HH.
            apply IHl. ltac1:(lia).
        }
    }
Qed.


Lemma length_filter_eq__eq__length_filter_in__one
    {T : Type}
    {_edT: EqDecision T}
    (h : T)
    (l : list (list T))
    :
    length (filter (eq h) (concat l)) = 1 ->
    length (filter (elem_of h) l) = 1
.
Proof.
    {
        induction l; simpl; intros HH.
        {
            ltac1:(lia).
        }
        {
            rewrite filter_cons.
            rewrite filter_app in HH.
            rewrite app_length in HH.
            destruct (decide (h ∈ a)) as [Hin|Hnotin].
            {
                assert(Htmp := h_in_l_impl_length_filter_l_gt_1 (eq h) a h Hin eq_refl).
                simpl in *.
                assert (length (filter (eq h) (concat l)) = 0).
                {
                    ltac1:(lia).
                }
                apply length_filter_eq__eq__length_filter_in__zero in H.
                rewrite H.
                reflexivity.                
            }
            {
                apply IHl. clear IHl.
                assert (length (filter (eq h) a) = 0).
                {
                    clear -Hnotin.
                    induction a.
                    {
                        simpl. reflexivity.
                    }
                    {
                        rewrite elem_of_cons in Hnotin.
                        apply Decidable.not_or in Hnotin.
                        destruct Hnotin as [Hnotin1 Hnotin2].
                        rewrite filter_cons.
                        destruct (decide (h = a))>[ltac1:(subst;contradiction)|].
                        apply IHa. exact Hnotin2.
                    }
                }
                ltac1:(lia).
            }
        }
    }
Qed.

Lemma filter_fmap
    {T1 T2: Type}
    (f : T1 -> T2)
    (P : T2 -> Prop)
    {_decP : forall x, Decision (P x)}
    {_decfP : forall x, Decision ((P ∘ f) x)}
    (l : list T1)
    :
    filter P (f <$> l) = f <$> (filter (P ∘ f) l)
.
Proof.
    induction l.
    {
        simpl. rewrite filter_nil. reflexivity.
    }
    {
        rewrite filter_cons.
        rewrite fmap_cons.
        rewrite filter_cons.
        rewrite IHl.
        unfold compose.
        simpl in *.
        ltac1:(repeat case_match); try (ltac1:(contradiction)).
        {
            reflexivity.
        }
        {
            reflexivity.
        }
    }
Qed.

Lemma on_a_shared_prefix
    {T : Type}
    (_edT : EqDecision T)
    (b : T)
    (l1 l2 l1' l2' : list T)
    :
    b ∉ l1 ->
    b ∉ l1' ->
    l1 ++ b::l2 = l1' ++ b::l2' ->
    l1 = l1'
.
Proof.
    revert l1'.
    induction l1; simpl; intros l1' H1 H2 H3.
    {
        destruct l1'; simpl in *.
        { reflexivity. }
        {
            ltac1:(exfalso).
            inversion H3; subst; clear H3.
            apply H2. clear H2.
            rewrite elem_of_cons. left. reflexivity.
        }
    }
    {
        destruct l1'.
        {
            ltac1:(exfalso).
            inversion H3; subst; clear H3.
            apply H1. clear H1.
            rewrite elem_of_cons. left. reflexivity.
        }
        {
            rewrite elem_of_cons in H1.
            rewrite elem_of_cons in H2.
            apply Decidable.not_or in H1.
            apply Decidable.not_or in H2.
            destruct H1 as [H11 H12].
            destruct H2 as [H21 H22].
            simpl in H3. inversion H3; subst; clear H3.
            specialize (IHl1 l1' H12 H22 H1).
            subst l1'.
            reflexivity.
        }
    }
Qed.

Lemma vars_of_to_l2r_subst
    {Σ : StaticModel}
    (φ ψ : TermOver BuiltinOrVar)
    (h : variable)
    :
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    h ∉ vars_of_to_l2r ψ ->
    vars_of_to_l2r (TermOverBoV_subst φ h ψ)
    ≡ₚ ((filter (fun x => x <> h) (vars_of_to_l2r φ)) ++ (vars_of_to_l2r ψ))
.
Proof.
    intros Hinφ Hnotinψ.
    induction φ; simpl.
    {
        destruct a; simpl in *.
        {
            ltac1:(lia).
        }
        {
            rewrite filter_cons in Hinφ.
            rewrite filter_cons.
            destruct (decide (h = x)); simpl in *.
            {
                subst x.
                destruct (decide (h<>h))>[ltac1:(contradiction)|].
                rewrite filter_nil. simpl. reflexivity.
            }
            {
                ltac1:(lia).
            }
        }
    }
    {
        simpl in *.
        assert (H'inφ := Hinφ).
        assert (Hlen: length (filter (fun x => h ∈ vars_of_to_l2r x) l) = 1).
        {
            apply length_filter_eq__eq__length_filter_in__one in H'inφ.
            ltac1:(replace map with (@fmap _ list_fmap) in H'inφ by reflexivity).
            ltac1:(unshelve(erewrite filter_fmap in H'inφ)).
            {
                intros x.
                unfold compose.
                apply _.
            }
            rewrite fmap_length in H'inφ.
            apply H'inφ.
        }
        apply count_one_split in Hlen.
        destruct Hlen as [la1 [b1 [lc1 [HH'1 [HH'2 [HH'3 HH'4]]]]]].

        assert (Hvl := HH'1).
        apply (f_equal (fmap vars_of_to_l2r)) in Hvl.
        rewrite fmap_app in Hvl.
        rewrite fmap_cons in Hvl.
        ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
        rewrite Hvl.
        rewrite concat_app.
        rewrite concat_cons.
        rewrite filter_app.
        rewrite filter_app.
        rewrite HH'1.
        rewrite fmap_app.
        rewrite fmap_cons.
        rewrite fmap_app.
        rewrite concat_app.
        rewrite fmap_cons.
        rewrite concat_cons.

        assert (HJ1: Forall (λ x : variable, h ≠ x) (concat (vars_of_to_l2r <$> la1))).
        {
            rewrite Forall_forall.
            rewrite Forall_forall in HH'3.
            intros x Hx.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [l0 [H1 H2]].
            rewrite <- elem_of_list_In in H2.
            rewrite <- elem_of_list_In in H1.
            rewrite elem_of_list_fmap in H1.
            destruct H1 as [t [H1t H2t]].
            subst l0.
            specialize (HH'3 t H2t).
            clear -HH'3 H2.
            intros HContra. subst.
            apply HH'3. apply H2.
        }

        assert (HJ2 : Forall (λ x : variable, h ≠ x) (concat (vars_of_to_l2r <$> lc1))).
        {
            rewrite Forall_forall.
            rewrite Forall_forall in HH'4.
            intros x Hx.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [l0 [H1 H2]].
            rewrite <- elem_of_list_In in H2.
            rewrite <- elem_of_list_In in H1.
            rewrite elem_of_list_fmap in H1.
            destruct H1 as [t [H1t H2t]].
            subst l0.
            specialize (HH'4 t H2t).
            clear -HH'4 H2.
            intros HContra. subst.
            apply HH'4. apply H2.
        }


        rewrite HH'1 in H.
        rewrite Forall_app in H.
        rewrite Forall_cons in H.
        destruct H as [IHH1 [IH2 IH3]].


        ltac1:(ospecialize (IH2 _)).
        {

            rewrite HH'1 in H'inφ.
            ltac1:(replace map with (@fmap _ list_fmap) in H'inφ by reflexivity).
            rewrite fmap_app in H'inφ.
            rewrite fmap_cons in H'inφ.
            rewrite concat_app in H'inφ.
            rewrite concat_cons in H'inφ.
            rewrite filter_app in H'inφ.
            rewrite filter_app in H'inφ.
            rewrite app_length in H'inφ.
            rewrite app_length in H'inφ.
            assert (Hfil1 : length (filter (eq h) (concat (vars_of_to_l2r <$> la1))) = 0).
            {
                rewrite list_filter_Forall_not.
                { reflexivity. }
                {
                    assumption.
                }
            }
            assert (Hfil2 : length (filter (eq h) (concat (vars_of_to_l2r <$> lc1))) = 0).
            {
                rewrite list_filter_Forall_not.
                { reflexivity. }
                {
                    assumption.
                }
            }
            ltac1:(lia).
        }
        rewrite IH2. clear IH2.

        assert (Heq1: ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> la1) = la1).
        {
            clear -HH'3.
            induction la1.
            { reflexivity. }
            {
                rewrite Forall_cons in HH'3.
                destruct HH'3 as [H1 H2].
                specialize (IHla1 H2).
                rewrite fmap_cons.
                rewrite IHla1.
                rewrite subst_notin.
                { reflexivity. }
                { apply H1. }
            }
        }

        assert (Heq2: ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> lc1) = lc1).
        {
            clear -HH'4.
            induction lc1.
            { reflexivity. }
            {
                rewrite Forall_cons in HH'4.
                destruct HH'4 as [H1 H2].
                specialize (IHlc1 H2).
                rewrite fmap_cons.
                rewrite IHlc1.
                rewrite subst_notin.
                { reflexivity. }
                { apply H1. }
            }
        }
        rewrite Heq1. rewrite Heq2. clear Heq1 Heq2.

        assert (HJ1': filter (λ x : variable, x ≠ h) (concat (vars_of_to_l2r <$> la1)) = concat (vars_of_to_l2r <$> la1)).
        {
            clear -HJ1.
            rewrite list_filter_Forall_all.
            { reflexivity. }
            {
                eapply List.Forall_impl>[|apply HJ1].
                intros x Ha. simpl in Ha. ltac1:(congruence).
            }
        }

        assert (HJ2': filter (λ x : variable, x ≠ h) (concat (vars_of_to_l2r <$> lc1)) = concat (vars_of_to_l2r <$> lc1)).
        {
            clear -HJ2.
            rewrite list_filter_Forall_all.
            { reflexivity. }
            {
                eapply List.Forall_impl>[|apply HJ2].
                intros x Ha. simpl in Ha. ltac1:(congruence).
            }
        }

        rewrite HJ1'. clear HJ1 HJ1'.
        rewrite HJ2'. clear HJ2 HJ2'.
        clear.
        ltac1:(solve_Permutation).
    }
Qed.

Lemma sum_list_with_perm
    {T : Type}
    (f : T -> nat)
    (l1 l2 : list T)
    :
    l1 ≡ₚ l2 ->
    sum_list_with f l1 = sum_list_with f l2
.
Proof.
    intros H.
    induction H.
    {
        reflexivity.
    }
    {
        simpl. rewrite IHPermutation. reflexivity.
    }
    {
        simpl. ltac1:(lia).
    }
    {
        ltac1:(congruence).
    }
Qed.


Lemma frto_step_app
    {Σ : StaticModel}
    (Act : Set)
    :
    forall
        Γ
        (t1 t2 t3 : TermOver builtin_value)
        (w : list Act)
        (a : Act)
        r,
    r ∈ Γ ->
    flattened_rewrites_to_over Γ t1 w t2 ->
    flattened_rewrites_to r (uglify' t2) a (uglify' t3) ->
    flattened_rewrites_to_over Γ t1 (w++[a]) t3
.
Proof.
    intros Γ t1 t2 t3 w a r Hr H1 H2.
    induction H1.
    {
        simpl.
        eapply frto_step.
        { exact Hr. }
        { exact H2. }
        { apply frto_base. }
    }
    {
        simpl.
        specialize (IHflattened_rewrites_to_over H2).
        eapply frto_step.
        { exact e. }
        { exact f. }
        { apply IHflattened_rewrites_to_over. }
    }
Qed.


Lemma frto_app
    {Σ : StaticModel}
    (Act : Set)
    :
    forall
        Γ
        (t1 t2 t3 : TermOver builtin_value)
        (w1 w2 : list Act),
    flattened_rewrites_to_over Γ t1 w1 t2 ->
    flattened_rewrites_to_over Γ t2 w2 t3 ->
    flattened_rewrites_to_over Γ t1 (w1++w2) t3
.
Proof.
    intros.
    revert t1 t2 t3 w2 X X0.
    induction w1; intros t1 t2 t3 w2 H0 H1.
    {
        inversion H0; subst; clear H0.
        simpl.
        exact H1.
    }
    {
        simpl.
        inversion H0; subst; clear H0.
        eapply frto_step>[|apply X|].
        { assumption. }
        {
            eapply IHw1.
            { apply X0. }
            { apply H1. }
        }
    }
Qed.


Lemma val_elem_of_dom_1
    {Σ : StaticModel}
    (ρ : gmap variable GroundTerm)
    (x : variable)
    :
    x ∈ dom ρ -> isSome (ρ !! x) = true
.
Proof.
    rewrite elem_of_dom.
    destruct (ρ!!x); simpl.
    {
        intros _. reflexivity.
    }
    {
        intros H. unfold is_Some in H.
        destruct H as [x0 Hx0].
        inversion Hx0.
    }
Qed.


Lemma satisfies_TermOverBoV_to_TermOverExpr
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    satisfies ρ γ (TermOverBoV_to_TermOverExpr φ)
    ->
    satisfies ρ γ φ
.
Proof.
    revert γ.
    ltac1:(induction φ using TermOver_rect); intros γ.
    {
        unfold TermOverBoV_to_TermOverExpr.
        simpl.
        intros H.
        {
            destruct a; simpl in *.
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    constructor.
                    inversion pf; subst; clear pf.
                    constructor.
                }   
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    inversion X.
                }             
            }
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    constructor.
                    inversion pf; subst; clear pf.
                    constructor.
                    assumption.
                }
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    inversion X; subst; clear X.
                    simpl.
                    apply satisfies_var.
                    rewrite uglify'_prettify'.
                    assumption.
                }
            }
        }
    }
    {
        intros HH.
        {
            unfold TermOverBoV_to_TermOverExpr in HH.
            simpl in HH.
            apply satisfies_term_expr_inv in HH.
            destruct HH as [lγ [[H1 H2] H3]].
            subst γ.
            unfold satisfies; simpl.
            unfold apply_symbol'; simpl.
            constructor.
            unfold to_PreTerm'; simpl.
            apply satisfies_top_bov_cons_1.
            {
                rewrite map_length in H2. ltac1:(lia).
            }
            { reflexivity. }
            {
                intros i s0 l0 H1i H2i.
                apply X.
                {
                    rewrite elem_of_list_lookup.
                    exists i. assumption.
                }
                eapply H3.
                { apply H1i. }
                {
                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                    rewrite list_lookup_fmap.
                    rewrite H2i.
                    simpl.      
                    reflexivity.              
                }
            }
        }
    }
Qed.

Lemma satisfies_TermOverBoV_to_TermOverExpr_2
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :    
    satisfies ρ γ φ ->
    satisfies ρ γ (TermOverBoV_to_TermOverExpr φ)
.
Proof.
    revert γ.
    ltac1:(induction φ using TermOver_rect); intros γ.
    {
        unfold TermOverBoV_to_TermOverExpr.
        simpl.
        intros H.
        {
            destruct a; simpl in *.
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    constructor.
                    inversion pf; subst; clear pf.
                    constructor.
                }   
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    inversion X.
                }             
            }
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    constructor.
                    inversion pf; subst; clear pf.
                    assumption.
                }
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    inversion X; subst; clear X.
                    simpl.
                    unfold satisfies; simpl.
                    rewrite uglify'_prettify'.
                    constructor.
                    assumption.
                }
            }
        }
    }
    {
        intros HH.
        {
            unfold TermOverBoV_to_TermOverExpr in HH.
            simpl in HH.
            unfold TermOverBoV_to_TermOverExpr.
            

            apply satisfies_term_bov_inv in HH.
            destruct HH as [lγ [[HH1 HH2] HH3]].
            subst.
            constructor.
            fold (@uglify' (@symbol Σ)).
            fold (@TermOver_map Σ).
            unfold to_PreTerm''.
            eapply satisfies_top_bov_cons_expr_1.
            {
                rewrite map_length. ltac1:(lia).
            }
            { reflexivity. }
                
            intros i s0 l0 HH'1 HH'2.
            ltac1:(replace (map) with (@fmap _ list_fmap) in HH'2 by reflexivity).
            rewrite list_lookup_fmap in HH'2.
            destruct (l!!i) as [l0'|] eqn:Hli > [|ltac1:(rewrite Hli in HH'2);inversion HH'2].
            specialize (X l0').
            simpl in HH'2.
            ltac1:(rewrite Hli in HH'2).
             injection HH'2 as HH'2.
            subst l0.
            specialize (HH3 _ _ _ HH'1 Hli).
            ltac1:(ospecialize (X _)).
            {
                rewrite elem_of_list_lookup.
                exists i. apply Hli.
            }
            specialize (X _ HH3).
            exact X.
        }
    }
Qed.


(*
Lemma vars_of_t_term
    {Σ : StaticModel}
    (s : symbol)
    (l : list (TermOver BuiltinOrVar))
    :
    vars_of (t_term s l) = union_list ( vars_of <$> l)
.
Proof.
    induction l using rev_ind.
    {
        reflexivity.
    }
    {
        unfold vars_of in *; simpl in *.
        unfold apply_symbol'' in *.
        unfold to_Term' in *.
        unfold vars_of in *; simpl in *.
        unfold to_PreTerm'' in *.
        rewrite map_app.
        rewrite fold_left_app.
        simpl. unfold helper at 1.
        destruct (uglify' x) eqn:Hux.
        {
            unfold vars_of in *; simpl in *.
            rewrite IHl.
            rewrite fmap_app.
            rewrite union_list_app_L.
            simpl.
            rewrite Hux. simpl.
            ltac1:(set_solver).
        }
        {
            unfold vars_of in *; simpl in *.
            rewrite IHl.
            rewrite fmap_app.
            rewrite union_list_app_L.
            simpl.
            rewrite Hux. simpl.
            ltac1:(set_solver).
        }
    }
Qed.
*)

Equations? TermOverBoV_eval
    {Σ : StaticModel}
    (ρ : Valuation)
    (φ : TermOver BuiltinOrVar)
    (pf : vars_of φ ⊆ vars_of ρ)
    : TermOver builtin_value
    by wf (TermOver_size φ) lt
:=

    TermOverBoV_eval ρ (t_over (bov_builtin b)) pf := t_over b
    ;

    TermOverBoV_eval ρ (t_over (bov_variable x)) pf with (inspect (ρ !! x)) => {
        | (@exist _ _ (Some t) pf') := prettify t;
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
        rewrite elem_of_dom in pf;
        ltac1:(rewrite pf' in pf);
        eapply is_Some_None;
        apply pf).
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
    (ρ : Valuation)
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
        inversion HH; subst; clear HH.
        {
            apply (f_equal prettify) in H1.
            rewrite (cancel prettify uglify') in H1.
            simpl in H1.
            destruct a; simpl in *.
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                apply empty_subseteq.
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                inversion pf; subst; clear pf.
                rewrite elem_of_subseteq.
                intros x' Hx'.
                rewrite elem_of_singleton in Hx'.
                subst x'.
                rewrite elem_of_dom.
                exists (term_operand y).
                exact H2.
            }
        }
        {
            destruct a; simpl in *.
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                apply empty_subseteq.
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                inversion X; subst; clear X.
                rewrite elem_of_subseteq.
                intros x' Hx'.
                rewrite elem_of_singleton in Hx'.
                subst x'.
                rewrite elem_of_dom.
                exists (term_preterm axy).
                exact H0.
            }
        }
    }
    {
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
        apply satisfies_term_bov_inv in HH.
        destruct HH as [lγ [[H4 H5] H6]].
        subst c.
        rewrite <- (firstn_skipn (length l1) lγ) in H6.
        destruct (drop (length l1) lγ) as [|m ms] eqn:Hed.
        {
            clear -Hed H5.
            rewrite <- (firstn_skipn (length l1) lγ) in H5.
            rewrite app_length in H5.
            rewrite app_length in H5.
            rewrite take_length in H5.
            rewrite Hed in H5.
            simpl in H5.
            ltac1:(lia).
        }

        eapply H2>[|apply Hx].
        eapply H6 with (i := length l1).
        {
            rewrite lookup_app_r.
            {
                rewrite take_length.
                rewrite app_length in H5.
                simpl in H5.
                ltac1:(
                    replace (length l1 - length l1 `min` length lγ)
                    with 0
                    by lia
                ).
                reflexivity.
            }
            {
                rewrite take_length. ltac1:(lia).
            }
        }
        {
            rewrite lookup_app_r.
            {
                rewrite Nat.sub_diag. simpl. reflexivity.
            }
            {
                ltac1:(lia).
            }
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
            unfold vars_of at 2; simpl.
            unfold vars_of at 2; simpl.
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


Lemma satisfies_TermOverBoV_eval
    {Σ : StaticModel}
    (ρ : Valuation)
    (φ : TermOver BuiltinOrVar)
    pf
    :
    satisfies ρ (TermOverBoV_eval ρ φ pf) φ
.
Proof.
    ltac1:(funelim (TermOverBoV_eval ρ φ pf)).
    {
        constructor. constructor.
    }
    {
        rewrite <- Heqcall.
        constructor.
        fold (@uglify' (@symbol Σ)).
        unfold to_PreTerm''.
        apply satisfies_top_bov_cons_1.
        {
            rewrite length_pfmap. reflexivity.
        }
        {
            reflexivity.
        }
        {
            intros i s0 l0 H1i H2i.
            assert (HP4 := @pfmap_lookup_Some_1 (TermOver BuiltinOrVar)).
            specialize (HP4 (TermOver builtin_value) l).
            specialize (HP4 _ i _ H1i).
            simpl in HP4.
            (*subst s0.*)
            rewrite HP4.
            assert (Htmp1: Some (proj1_sig ((pflookup l i (pfmap_lookup_Some_lt H1i)))) = Some l0).
            {
                rewrite <- H2i.
                apply pflookup_spec.
            }
            apply (inj Some) in Htmp1.
            rewrite <- Htmp1.
            ltac1:(unshelve(eapply X0))>[()|()|reflexivity|()].
            unfold eq_rect. reflexivity.
        }
    }
    {
        simpl.
        apply satisfies_var.
        unfold Valuation in *.
        ltac1:(rewrite pf').
        apply f_equal.
        rewrite <- Heqcall.
        rewrite (cancel uglify' prettify).
        reflexivity.
    }
    {
        unfold vars_of in pf; simpl in pf.
        unfold vars_of in pf; simpl in pf.
        unfold vars_of in pf; simpl in pf.
        clear H Heqcall.
        unfold Valuation in *.
        apply not_elem_of_dom_2 in pf'.
        ltac1:(exfalso).
        apply pf'. clear pf'.
        rewrite elem_of_subseteq in pf.
        apply pf.
        rewrite elem_of_singleton.
        reflexivity.
    }
Qed.

Lemma TermOverBoV_eval__varsofindependent
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (φ : TermOver BuiltinOrVar)
    pf1 pf2
    :
    (∀ x, x ∈ vars_of φ -> ρ1 !! x = ρ2 !! x) ->
    TermOverBoV_eval ρ1 φ pf1 = TermOverBoV_eval ρ2 φ pf2
.
Proof.
    unfold TermOver in *.
    ltac1:(funelim (TermOverBoV_eval ρ1 φ pf1)).
    {
        unfold TermOver in *.
        intros HH.
        (* rewrite <- Heqcall. *)
        ltac1:(simp TermOverBoV_eval).
        reflexivity.
    }
    {
        intros HH.
        rewrite <- Heqcall.
        ltac1:(simp TermOverBoV_eval).
        apply f_equal.
        apply f_equal.
        simpl.
        ltac1:(move: TermOverBoV_eval_obligation_2).
        intros HHpf.

        eapply functional_extensionality_dep.
        intros x.
        eapply functional_extensionality_dep.
        intros pf3.
        ltac1:(unshelve(eapply H0)).
        { exact x. }
        { exact pf3. }
        { 
            abstract(
                apply f_equal;
                apply f_equal;
                apply f_equal;
                apply proof_irrelevance
            ).
        }
        {
            unfold eq_rect.
            ltac1:(move: (TermOverBoV_eval__varsofindependent_subproof _ _ _ _ _ _ _ _)).
            intros mypf.
            assert(Htmp1:
                TermOverBoV_eval_obligation_2 Σ ρ s l pf
                (λ (x0 : StaticModel) (x1 : Valuation) (x2 : TermOver
                BuiltinOrVar) (x3 : vars_of
                x2
                ⊆ vars_of
                x1) (_ : TermOver_size
                x2 <
                TermOver_size
                (t_term
                s
                l)),
                TermOverBoV_eval x1 x2 x3)
                x
                pf3
            =
                HHpf Σ ρ s l pf
                (λ (x0 : StaticModel) (x1 : Valuation) (x2 : TermOver
                BuiltinOrVar) (x3 : vars_of
                x2
                ⊆ vars_of
                x1) (_ : TermOver_size
                x2 <
                S
                (sum_list_with
                (S
                ∘ TermOver_size)
                l)),
                TermOverBoV_eval x1 x2 x3)
                x
                pf3
            ).
            {
                apply proof_irrelevance.
            }
            revert mypf.
            rewrite Htmp1.
            intros mypf.
            assert (Htmp2: mypf = eq_refl).
            {
                apply proof_irrelevance.
            }
            rewrite Htmp2.
            reflexivity.
        }
        unfold TermOver in *.
        intros x0 Hx0.
        apply HH.
        clear -pf3 Hx0.
        rewrite vars_of_t_term.
        rewrite elem_of_union_list.
        exists (vars_of x).
        split>[|assumption].
        rewrite elem_of_list_fmap.
        exists x.
        split>[reflexivity|].
        exact pf3.
    }
    {
        intros HH.
        rewrite <- Heqcall.
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        simpl.
        unfold TermOverBoV_eval_obligation_1.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ x)).
        assert (pf'2 : ρ2 !! x = Some t).
        {
            rewrite <- HH.
            exact pf'.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            rewrite elem_of_singleton.
            reflexivity.
        }
        ltac1:(rewrite -> pf').
        intros HHH.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ2 x)).
        ltac1:(rewrite -> pf'2).
        intros HHH2.
        reflexivity.
    }
    {
        intros HH.
        rewrite <- Heqcall.
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        simpl.
        unfold TermOverBoV_eval_obligation_1.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ x)).
        rewrite pf'.
        intros ?.
        f_equal.
        assert (pf'2 : ρ2 !! x = None).
        {
            rewrite <- HH.
            exact pf'.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            rewrite elem_of_singleton.
            reflexivity.
        }
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ2 x)).
        rewrite pf'2.
        intros ?.
        f_equal.
        apply proof_irrelevance.
    }
Qed.


Lemma Expression_evaluate_subst
    {Σ : StaticModel}
    (ρ : Valuation)
    (e : Expression)
    (g g' : GroundTerm)
    (h : variable)
    :
    Expression_evaluate ρ (Expression_subst e h (ft_element g)) = Some g' ->
    Expression_evaluate (<[h := g]>ρ) e = Some g'
.
Proof.
    revert h g g'.
    induction e; simpl; intros h g g' HH.
    {
        exact HH.
    }
    {
        unfold Valuation in *.
        destruct (decide (x = h)).
        {
            subst.
            simpl in *.
            inversion HH; subst; clear HH.
            apply lookup_insert.
        }
        {
            rewrite lookup_insert_ne>[|ltac1:(congruence)].
            simpl in HH.
            exact HH.
        }
    }
    {
        exact HH.
    }
    {
        rewrite bind_Some in HH.
        destruct HH as [x [H1 H2]].
        rewrite bind_Some.
        injection H2 as H2.
        subst g'.
        rewrite fmap_Some in H1.
        destruct H1 as [y [H1y H2y]].
        subst x.
        specialize (IHe _ _ _ H1y).
        exists (prettify y).
        split>[|reflexivity].
        rewrite IHe. reflexivity.
    }
    {
        rewrite bind_Some in HH.
        destruct HH as [x1 [Hx1 HH]].
        rewrite bind_Some in HH.
        destruct HH as [x2 [Hx2 HH]].
        inversion HH; subst; clear HH.
        
        rewrite fmap_Some in Hx1.
        destruct Hx1 as [y [H1y H2y]].

        rewrite fmap_Some in Hx2.
        destruct Hx2 as [z [H1z H2z]].
        subst x1 x2.
        specialize (IHe1 _ _ _ H1y).
        specialize (IHe2 _ _ _ H1z).
        rewrite bind_Some.
        exists (prettify y).
        rewrite IHe1.
        split>[reflexivity|].
        rewrite bind_Some.
        exists (prettify z).
        rewrite IHe2.
        split>[reflexivity|].
        reflexivity.
    }
    {
        rewrite bind_Some in HH.
        destruct HH as [x1 [Hx1 HH]].
        rewrite bind_Some in HH.
        destruct HH as [x2 [Hx2 HH]].
        rewrite bind_Some in HH.
        destruct HH as [x3 [Hx3 HH]].
        inversion HH; subst; clear HH.


        rewrite fmap_Some in Hx1.
        destruct Hx1 as [y [H1y H2y]].
        rewrite fmap_Some in Hx2.
        destruct Hx2 as [z [H1z H2z]].
        rewrite fmap_Some in Hx3.
        destruct Hx3 as [t [H1t H2t]].
        subst x1 x2 x3.
        specialize (IHe1 _ _ _ H1y).
        specialize (IHe2 _ _ _ H1z).
        specialize (IHe3 _ _ _ H1t).
        rewrite bind_Some.
        exists (prettify y).
        rewrite IHe1.
        split>[reflexivity|].
        rewrite bind_Some.
        exists (prettify z).
        rewrite IHe2.
        split>[reflexivity|].
        rewrite bind_Some.
        exists (prettify t).
        rewrite IHe3.
        split>[reflexivity|].
        reflexivity.
    }
Qed.


Lemma satisfies__MinusL_isValue__subst
    {Σ : StaticModel}
    (ρ : Valuation)
    (g : GroundTerm)
    (Act : Set)
    (D : MinusL_LangDef Act)
    :
    satisfies ρ () (MinusL_isValue Act D (ft_element g)) ->
    satisfies (<[(mlld_isValue_var Act D) := g]>ρ) () (mlld_isValue_scs Act D)
.
Proof.
    intros HH.
    unfold satisfies in *; simpl in *.
    intros sc1. intros H1.
    unfold MinusL_isValue in HH.
    (* specialize (HH sc1). *)
    unfold satisfies in *; simpl in *.
    unfold valuation_satisfies_sc in *.
    destruct sc1 as [[e1 e2]].
    unfold satisfies in *; simpl.

    specialize (HH (sc_constraint (apeq (Expression_subst e1 (mlld_isValue_var Act D) (ft_element g)) (Expression_subst e2 (mlld_isValue_var Act D) (ft_element g))))).
    simpl in HH.
    ltac1:(ospecialize (HH _)).
    {
        rewrite elem_of_list_fmap.
        exists (sc_constraint (apeq e1 e2)).
        split>[reflexivity|].
        exact H1.
    }
    destruct HH as [HH1 HH2].
    unfold is_true in *. unfold isSome in *.
    destruct (Expression_evaluate ρ (Expression_subst e1 (mlld_isValue_var Act D) (ft_element g)))
        eqn:HH2'>[|inversion HH2].
    
    assert(Htmp1 := Expression_evaluate_subst ρ e1 g g0 (mlld_isValue_var Act D)).
    specialize (Htmp1 ltac:(congruence)).
    rewrite Htmp1.
    assert(Htmp2 := Expression_evaluate_subst ρ e2 g g0 (mlld_isValue_var Act D)).
    specialize (Htmp2 ltac:(congruence)).
    rewrite Htmp2.
    split>[reflexivity|].
    unfold is_Some. reflexivity.
Qed.

Lemma Expression_subst_notin
    {Σ : StaticModel}
    (e e' : Expression)
    (h : variable)
    :
    h ∉ vars_of e ->
    (Expression_subst e h e') = e
.
Proof.
    induction e; simpl; intros HH.
    { reflexivity. }
    {
        destruct (decide (x = h)); simpl.
        {
            subst. unfold vars_of in HH; simpl in HH.
            ltac1:(set_solver).
        }
        {
            reflexivity.
        }
    }
    {
        reflexivity.
    }
    {
        specialize (IHe HH).
        rewrite IHe.
        reflexivity.
    }
    {
        unfold vars_of in HH; simpl in HH.
        specialize (IHe1 ltac:(set_solver)).
        specialize (IHe2 ltac:(set_solver)).
        rewrite IHe1, IHe2.
        reflexivity.
    }
    {
        unfold vars_of in HH; simpl in HH.
        specialize (IHe1 ltac:(set_solver)).
        specialize (IHe2 ltac:(set_solver)).
        specialize (IHe3 ltac:(set_solver)).
        rewrite IHe1, IHe2, IHe3.
        reflexivity.
    }
Qed.


Lemma Expression_evaluate_subst_var
    {Σ : StaticModel}
    (ρ : Valuation)
    (e : Expression)
    (g : GroundTerm)
    (h1 h2 : variable)
    :
    h1 ∉ vars_of e ->
    Expression_evaluate (<[h1 := g]>ρ) (Expression_subst e h2 (ft_variable h1))
    = Expression_evaluate (<[h2 := g]>ρ) e
.
Proof.
    revert g h1 h2.
    induction e; simpl; intros g h1 h2 Hh1.
    {
        reflexivity.
    }
    {
        unfold Valuation in *.
        destruct (decide (x = h2)); simpl.
        {
            subst.
            rewrite lookup_insert.
            rewrite lookup_insert.
            reflexivity.
        }
        {
            unfold vars_of in Hh1; simpl in Hh1.
            rewrite elem_of_singleton in Hh1.
            rewrite lookup_insert_ne>[|ltac1:(congruence)].
            rewrite lookup_insert_ne>[|ltac1:(congruence)].
            reflexivity.
        }
    }
    {
        reflexivity.
    }
    {
        specialize (IHe g h1 h2 Hh1).
        rewrite IHe.
        reflexivity.
    }
    {
        unfold vars_of in Hh1; simpl in Hh1.
        rewrite elem_of_union in Hh1.
        apply Decidable.not_or in Hh1.
        destruct Hh1 as [H1h1 H2h1].
        specialize (IHe1 g h1 h2 H1h1).
        specialize (IHe2 g h1 h2 H2h1).
        rewrite IHe1.
        rewrite IHe2.
        reflexivity.
    }
    {
        unfold vars_of in Hh1; simpl in Hh1.
        rewrite elem_of_union in Hh1.
        apply Decidable.not_or in Hh1.
        destruct Hh1 as [Hh1 H3h1].
        rewrite elem_of_union in Hh1.
        apply Decidable.not_or in Hh1.
        destruct Hh1 as [H1h1 H2h1].
        specialize (IHe1 g h1 h2 H1h1).
        specialize (IHe2 g h1 h2 H2h1).
        specialize (IHe3 g h1 h2 H3h1).
        rewrite IHe1.
        rewrite IHe2.
        rewrite IHe3.
        reflexivity.
    }
Qed.

Lemma satisfies_insert_MinusL_isValue
    {Σ : StaticModel}
    (ρ : Valuation)
    (g : GroundTerm)
    (h : variable)
    (Act : Set)
    (D : MinusL_LangDef Act)
    :
    h ∉ vars_of (mlld_isValue_scs Act D) ->
    satisfies
        (<[mlld_isValue_var Act D:=g]> ρ)
        ()
        (mlld_isValue_scs Act D)  ->
    satisfies
        (<[h:=g]>  ρ)
        ()
        (MinusL_isValue Act D (ft_variable h))
.
Proof.
    intros Hh HH.
    unfold satisfies in *; simpl in *.
    intros sc1. intros H1.
    unfold MinusL_isValue in *.
    apply elem_of_list_fmap_T_1 in H1.
    destruct H1 as [y [H1y H2y]].
    subst sc1.
    destruct y as [ [e1 e2] ].
    specialize (HH _ H2y).
    unfold satisfies in HH; simpl in HH.
    unfold satisfies in HH; simpl in HH.
    
    unfold satisfies; simpl.
    unfold satisfies; simpl.

    unfold vars_of in Hh; simpl in Hh.

    rewrite Expression_evaluate_subst_var.
    rewrite Expression_evaluate_subst_var.
    exact HH.
    {
        intros HContra. apply Hh. clear Hh.
        rewrite elem_of_union_list.
        exists (vars_of e1 ∪ vars_of e2).
        split>[|ltac1:(set_solver)].
        rewrite elem_of_list_fmap.
        exists (sc_constraint (apeq e1 e2)).
        split>[|exact H2y].
        unfold vars_of at 2; simpl.
        unfold vars_of at 2; simpl.
        ltac1:(set_solver).
    }
    {
        intros HContra. apply Hh. clear Hh.
        rewrite elem_of_union_list.
        exists (vars_of e1 ∪ vars_of e2).
        split>[|ltac1:(set_solver)].
        rewrite elem_of_list_fmap.
        exists (sc_constraint (apeq e1 e2)).
        split>[|exact H2y].
        unfold vars_of at 2; simpl.
        unfold vars_of at 2; simpl.
        ltac1:(set_solver).
    }
Qed.

(*
Lemma compile_correct_1
    {Σ : StaticModel}
    {Act : Set}
    {_AD : EqDecision Act}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable) 
    (D : MinusL_LangDef Act)
    (HcvD: continuationVariable ∉ vars_of D)
    (wfD : MinusL_LangDef_wf Act D)
    :
    ~ (invisible_act ∈ actions_of_ldef Act D) ->
    let Γ := compile invisible_act topSymbol cseqSymbol holeSymbol continuationVariable D in
    forall
        (lc ld rc rd : TermOver builtin_value)
        (w : list Act),
        MinusL_rewrites Act D lc ld w rc rd
        -> (* TODO we also need the backwards implication but the actions might be different*)
        (
            { w' : list Act &
            (
            (w = (filter (fun x => x <> invisible_act) w')) *
            forall cont,
            flattened_rewrites_to_over Γ
                (downC topSymbol cseqSymbol lc ld cont)
                w'
                (downC topSymbol cseqSymbol rc rd cont)
            )%type
            }
        )
.
Proof.
    intros Hinvisible.
    intros Γ c1 d1 c2 d2 w HH.
    destruct D as [iV_scs iV_var ds]; simpl in *.

    induction HH.
    {
        exists [].
        rewrite filter_nil.
        split>[reflexivity|].
        intros cont.
        constructor.
    }
    {
        exists [a].
        unfold compile in Γ.
        ltac1:(rename e into H).
        simpl in H. simpl in Γ.
        eapply list_find_elem_of_isSome with (P := (eq (mld_rewrite Act lc ld a rc rd scs))) in H as H''.
        {
            unfold isSome,is_true in H''.
            ltac1:(case_match)>[|ltac1:(congruence)].
            ltac1:(rename H0 into Hfound).
            destruct p as [idx decl].
            rewrite -> list_find_Some in Hfound.
            clear H''.
            destruct Hfound as [Hdsidx [? HfoundIsFirst]].
            subst decl.

            ltac1:(unfold Γ).
            assert (idx < length ds).
            {
                apply lookup_lt_Some in Hdsidx.
                exact Hdsidx.
            }
            
            rewrite <- (firstn_skipn idx ds) in Hdsidx.
            rewrite lookup_app_r in Hdsidx>[|rewrite take_length; ltac1:(lia)].
            rewrite take_length in Hdsidx.
            ltac1:(replace ((idx - idx `min` length ds)) with (0) in Hdsidx by lia).
            remember (drop idx ds) as ds'.
            ltac1:(rename idx into i).
            ltac1:(rename Hdsidx into Hi).

            destruct ds'.
            {
                simpl in Hi. inversion Hi.
            }
            simpl in Hi. inversion Hi; subst; clear Hi.
            rewrite filter_cons. rewrite filter_nil.

            split.
            {
                destruct (decide (a <> invisible_act)).
                {
                    reflexivity.
                }
                {
                    unfold actions_of_ldef in Hinvisible.
                    simpl in Hinvisible.
                    rewrite elem_of_list_In in Hinvisible.
                    rewrite in_concat in Hinvisible.
                    ltac1:(exfalso).
                    apply n.
                    clear n. intros Hsub. subst a. apply Hinvisible. clear Hinvisible.
                    exists [invisible_act].
                    split>[|constructor].
                    rewrite in_map_iff.
                    rewrite <- (firstn_skipn i ds).
                    exists (mld_rewrite Act lc ld invisible_act rc rd scs).
                    simpl.
                    split>[reflexivity|].
                    apply in_or_app.
                    right.
                    rewrite <- Heqds'.
                    constructor. reflexivity. reflexivity.
                }
            }
            {
                intros cont.
                unfold flattened_rewrites_to.
                rewrite <- (firstn_skipn i ds).
                rewrite map_app.
                rewrite concat_app.
                rewrite <- Heqds'.
                simpl.
                eapply frto_step>[()|()|apply frto_base].
                {
                    rewrite elem_of_app.
                    right.
                    rewrite elem_of_cons.
                    left.
                    reflexivity.
                }
                {
                    unfold flattened_rewrites_to.
                    exists (<[continuationVariable := (uglify' cont)]>ρ).
                    unfold flattened_rewrites_in_valuation_under_to.
                    (repeat split).
                    {
                        simpl.
                        ltac1:(cut(satisfies (<[continuationVariable := uglify' cont]>ρ)
                            (uglify' (t_term topSymbol [(t_term cseqSymbol [ctrl1; cont]);(state1)]))
                            (uglify' (t_term topSymbol [(t_term cseqSymbol [lc;(t_over (bov_variable continuationVariable))]);(ld)]))
                        )).
                        {
                            intros Htmp. apply Htmp.
                        }
                        constructor.
                        apply satisfies_top_bov_cons_1.
                        { reflexivity. }
                        { reflexivity. }
                        {
                            intros i0 s4 l HH1 HH2.
                            destruct i0; simpl in *.
                            {
                                injection HH1 as HH1.
                                injection HH2 as HH2.
                                subst s4.
                                subst l.
                                constructor.
                                eapply satisfies_top_bov_cons_1.
                                {
                                    reflexivity.
                                }
                                {
                                    reflexivity.
                                }
                                intros i0 s4 l.
                                destruct i0; simpl in *.
                                {
                                    intros HH1 HH2.
                                    symmetry in HH1. symmetry in HH2.
                                    inversion HH1; subst; clear HH1.
                                    inversion HH2; subst; clear HH2.

                                    eapply satisfies_TermOver_vars_of>[|apply s].
                                    intros x Hx.

                                    destruct (decide (continuationVariable = x)).
                                    {
                                        subst x.
                                        unfold vars_of in HcvD. simpl in HcvD.
                                        ltac1:(exfalso).
                                        apply HcvD. clear HcvD.
                                        rewrite elem_of_union_list.
                                        exists (vars_of ((mld_rewrite Act lc ld a rc rd scs))).
                                        split.
                                        {
                                            rewrite elem_of_list_fmap.
                                            exists (mld_rewrite Act lc ld a rc rd scs).
                                            split>[reflexivity|].
                                            rewrite <- (take_drop i ds).
                                            rewrite elem_of_app.
                                            rewrite <- Heqds'.
                                            right.
                                            rewrite elem_of_cons. left.
                                            reflexivity.
                                        }
                                        {
                                            clear -Hx.
                                            unfold Valuation in *.
                                            unfold Valuation2 in *.
                                            rewrite vars_of_uglify' in Hx.
                                            simpl in Hx.
                                            ltac1:(set_solver).
                                        }
                                    }
                                    {
                                        ltac1:(rewrite lookup_insert_ne).
                                        { assumption. }
                                        { reflexivity. }
                                    }
                                }
                                {
                                    destruct i0; simpl in *.
                                    {
                                        intros HH1 HH2.
                                        symmetry in HH1. symmetry in HH2.
                                        inversion HH1; subst; clear HH1.
                                        inversion HH2; subst; clear HH2.
                                        apply satisfies_var.
                                        ltac1:(rewrite lookup_insert).
                                        reflexivity.
                                    }
                                    {
                                        intros HContra.
                                        rewrite lookup_nil in HContra.
                                        inversion HContra.
                                    }
                                }
                            }
                            {
                                destruct i0; simpl in *.
                                {
                                    symmetry in HH1; inversion HH1; subst; clear HH1.
                                    symmetry in HH2; inversion HH2; subst; clear HH2.
                                    

                                    eapply satisfies_TermOver_vars_of>[|apply s0].
                                    intros x Hx.

                                    destruct (decide (continuationVariable = x)).
                                    {
                                        subst x.
                                        unfold vars_of in HcvD. simpl in HcvD.
                                        ltac1:(exfalso).
                                        apply HcvD. clear HcvD.
                                        rewrite elem_of_union_list.
                                        exists (vars_of ((mld_rewrite Act lc ld a rc rd scs))).
                                        split.
                                        {
                                            rewrite elem_of_list_fmap.
                                            exists (mld_rewrite Act lc ld a rc rd scs).
                                            split>[reflexivity|].
                                            rewrite <- (take_drop i ds).
                                            rewrite elem_of_app.
                                            rewrite <- Heqds'.
                                            right.
                                            rewrite elem_of_cons. left.
                                            reflexivity.
                                        }
                                        {
                                            rewrite vars_of_uglify' in Hx.
                                            simpl in Hx.
                                            clear -Hx.
                                            ltac1:(set_solver).
                                        }
                                    }
                                    {
                                        ltac1:(rewrite lookup_insert_ne).
                                        { assumption. }
                                        { reflexivity. }
                                    }

                                }
                                {
                                    rewrite lookup_nil in HH1.
                                    inversion HH1.
                                }
                            }
                        }
                    }
                    {
                        simpl.
                        ltac1:(cut(satisfies (<[continuationVariable := uglify' cont]>ρ)
                            (uglify' (t_term topSymbol [(t_term cseqSymbol [ctrl2; cont]);(state2)]))
                            (uglify' (t_term topSymbol [(t_term cseqSymbol [rc;(t_over (ft_variable continuationVariable))]);(rd)]))
                        )).
                        {
                            intros Htmp. apply Htmp.
                        }
                        constructor.
                        apply satisfies_top_bov_cons_expr_1.
                        { reflexivity. }
                        { reflexivity. }
                        {
                            intros i0 s4 l HH1 HH2.
                            destruct i0; simpl in *.
                            {
                                inversion HH1; subst; clear HH1.
                                inversion HH2; subst; clear HH2.
                                constructor.
                                eapply satisfies_top_bov_cons_expr_1.
                                { reflexivity. }
                                { reflexivity. }
                                intros i0 s4 l HH1 HH2.
                                destruct i0; simpl in *.
                                {
                                    symmetry in HH1; inversion HH1; subst; clear HH1.
                                    symmetry in HH2; inversion HH2; subst; clear HH2.
                                    eapply satisfies_TermOverExpression_vars_of>[|apply s1].
                                    intros x Hx.
                                    destruct (decide (continuationVariable = x)).
                                    {
                                        subst x.
                                        unfold vars_of in HcvD. simpl in HcvD.
                                        ltac1:(exfalso).
                                        apply HcvD. clear HcvD.
                                        rewrite elem_of_union_list.
                                        exists (vars_of ((mld_rewrite Act lc ld a rc rd scs))).
                                        split.
                                        {
                                            rewrite elem_of_list_fmap.
                                            exists (mld_rewrite Act lc ld a rc rd scs).
                                            split>[reflexivity|].
                                            rewrite <- (take_drop i ds).
                                            rewrite elem_of_app.
                                            rewrite <- Heqds'.
                                            right.
                                            rewrite elem_of_cons. left.
                                            reflexivity.
                                        }
                                        {
                                            rewrite vars_of_uglify' in Hx.
                                            clear -Hx.
                                            ltac1:(set_solver).
                                        }
                                    }
                                    {
                                        ltac1:(rewrite lookup_insert_ne).
                                        { assumption. }
                                        { reflexivity. }
                                    }
                                }
                                {
                                    destruct i0; simpl in *.
                                    {
                                        symmetry in HH1; inversion HH1; subst; clear HH1.
                                        symmetry in HH2; inversion HH2; subst; clear HH2.
                                        apply satisfies_var_expr.
                                        ltac1:(rewrite lookup_insert).
                                        reflexivity.
                                    }
                                    {
                                        rewrite lookup_nil in HH1. inversion HH1.
                                    }
                                }
                            }
                            {
                                destruct i0; simpl in *.
                                {
                                    symmetry in HH1; inversion HH1; subst; clear HH1.
                                    symmetry in HH2; inversion HH2; subst; clear HH2.
                                    eapply satisfies_TermOverExpression_vars_of>[|apply s2].
                                    intros x Hx.
                                    destruct (decide (continuationVariable = x)).
                                    {
                                        subst x.
                                        unfold vars_of in HcvD. simpl in HcvD.
                                        ltac1:(exfalso).
                                        apply HcvD. clear HcvD.
                                        rewrite elem_of_union_list.
                                        exists (vars_of ((mld_rewrite Act lc ld a rc rd scs))).
                                        split.
                                        {
                                            rewrite elem_of_list_fmap.
                                            exists (mld_rewrite Act lc ld a rc rd scs).
                                            split>[reflexivity|].
                                            rewrite <- (take_drop i ds).
                                            rewrite elem_of_app.
                                            rewrite <- Heqds'.
                                            right.
                                            rewrite elem_of_cons. left.
                                            reflexivity.
                                        }
                                        {
                                            rewrite vars_of_uglify' in Hx.
                                            clear -Hx.
                                            unfold vars_of; simpl.
                                            ltac1:(set_solver).
                                        }
                                    }
                                    {
                                        ltac1:(rewrite lookup_insert_ne).
                                        { assumption. }
                                        { reflexivity. }
                                    }
                                }
                                {
                                    rewrite lookup_nil in HH1. inversion HH1.
                                }
                            }
                        }
                    }
                    {
                        simpl.
                        eapply satisfies_scs_vars_of>[|apply s3].
                        intros x Hx.
                        destruct (decide (continuationVariable = x)).
                        {
                            subst x.
                            unfold vars_of in HcvD. simpl in HcvD.
                            ltac1:(exfalso).
                            apply HcvD. clear HcvD.
                            rewrite elem_of_union_list.
                            exists (vars_of ((mld_rewrite Act lc ld a rc rd scs))).
                            split.
                            {
                                rewrite elem_of_list_fmap.
                                exists (mld_rewrite Act lc ld a rc rd scs).
                                split>[reflexivity|].
                                rewrite <- (take_drop i ds).
                                rewrite elem_of_app.
                                rewrite <- Heqds'.
                                right.
                                rewrite elem_of_cons. left.
                                reflexivity.
                            }
                            {
                                unfold vars_of; simpl.
                                unfold vars_of; simpl.
                                clear -Hx.
                                ltac1:(set_solver).
                            }
                        }
                        {
                            ltac1:(rewrite lookup_insert_ne).
                            { assumption. }
                            { reflexivity. }
                        }
                    }
                }
            }

        }
        { reflexivity. }
        Unshelve.
        {
            intros d. apply _.
        }
    }
    {
        destruct IHHH1 as [w'1 [H1w'1 H2w'1]].
        destruct IHHH2 as [w'2 [H1w'2 H2w'2]].
        exists (w'1 ++ w'2).
        split.
        {
            subst w1 w2.
            clear.
            rewrite filter_app.
            reflexivity.
        }
        {
            intros cont.
            eapply frto_app.
            { apply H2w'1. }
            { apply H2w'2. }
        }
    }
    {
        destruct IHHH as [w' [Hw' IH]].
        exists (invisible_act::(w' ++ [invisible_act])).
        split.
        {
            rewrite filter_cons.
            destruct (decide (invisible_act <> invisible_act))>[ltac1:(congruence)|].
            rewrite filter_app.
            rewrite filter_cons.
            destruct (decide (invisible_act <> invisible_act))>[ltac1:(congruence)|].
            rewrite filter_nil.
            rewrite app_nil_r.
            exact Hw'.
        }
        {

            assert (Hheat:
                ctx_heat invisible_act topSymbol cseqSymbol holeSymbol
                (fresh (h::(vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))))
                (fresh (h:: (fresh (h :: (vars_of_to_l2r c ++ ( elements (vars_of scs) ++ (elements (vars_of iV_scs)))))) :: (vars_of_to_l2r c ++  elements (vars_of scs) ++ (elements (vars_of iV_scs)))))
                (MinusL_isValue Act (@mkMinusL_LangDef Σ Act iV_scs iV_var ds)) c h scs ∈ Γ).
            {
                ltac1:(rename e into H).
                rewrite elem_of_list_lookup in H.
                destruct H as [ir Hir].
                apply take_drop_middle in Hir.
                ltac1:(unfold Γ in IH).
                ltac1:(unfold Γ).
                simpl in *.
                ltac1:(rewrite - Hir).
                unfold compile.
                simpl.
                ltac1:(rewrite map_app).
                ltac1:(rewrite map_cons).
                simpl.
                ltac1:(rewrite concat_app).
                ltac1:(rewrite concat_cons).
                ltac1:(unfold Γ).
                clear.
                rewrite elem_of_app. right.
                rewrite elem_of_app. left.
                rewrite elem_of_cons. left.
                reflexivity.
            }

            assert (Hcool:
                ctx_cool invisible_act topSymbol cseqSymbol holeSymbol
                (fresh (h::(vars_of_to_l2r c ++  elements (vars_of scs) ++ (elements (vars_of iV_scs)))))
                (fresh (h:: (fresh (h::(vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))))) :: (vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))))
                (MinusL_isValue Act (@mkMinusL_LangDef Σ Act iV_scs iV_var ds)) c h ∈ Γ).
            {
                ltac1:(rename e into H).
                rewrite elem_of_list_lookup in H.
                destruct H as [ir Hir].
                apply take_drop_middle in Hir.
                ltac1:(unfold Γ in IH).
                ltac1:(unfold Γ).
                simpl in *.
                ltac1:(rewrite - Hir).
                unfold compile.
                simpl.
                ltac1:(rewrite map_app).
                ltac1:(rewrite map_cons).
                simpl.
                ltac1:(rewrite concat_app).
                ltac1:(rewrite concat_cons).
                ltac1:(unfold Γ).
                clear.
                rewrite elem_of_app. right.
                rewrite elem_of_app. left.
                rewrite elem_of_cons. right.
                rewrite elem_of_cons. left.
                reflexivity.
            }
        

            intros cont.
            unfold downC in *.
            remember ((TermOverBoV_subst c h (t_term holeSymbol []))) as substituted.
            
            apply satisfies_TermOverBoV__impl__vars_subseteq in s as H01'.
            assert (Hvars := vars_of__TermOverBoV_subst__varless c h (t_term holeSymbol []) eq_refl).
            assert (Htmp1 : vars_of substituted ⊆ vars_of ρ1).
            {
                subst.
                rewrite vars_of__TermOverBoV_subst__varless>[|reflexivity].
                clear -H01'.
                unfold vars_of in H01'. simpl in H01'.
                unfold vars_of; simpl.
                assert (Htmp: (vars_of (c)) ∖ {[h]} ⊆ (dom (<[h:=uglify' r]> ρ1)) ∖ {[h]}).
                {
                    ltac1:(set_solver).
                }
                clear H01'.
                ltac1:(rewrite dom_insert_L in Htmp).
                ltac1:(set_solver).
            }
            remember (TermOverBoV_eval ρ1 substituted Htmp1) as ceval.

            apply satisfies_TermOverBoV__impl__vars_subseteq in s1 as H11'.
            assert (Htmp2 : vars_of substituted ⊆ vars_of ρ2).
            {
                subst.
                rewrite vars_of__TermOverBoV_subst__varless>[|reflexivity].
                clear -H11'.
                unfold vars_of in H11'. simpl in H11'.
                unfold vars_of; simpl.
                assert (Htmp: (vars_of (c)) ∖ {[h]} ⊆ (dom (<[h:=uglify' v]> ρ2)) ∖ {[h]}).
                {
                    ltac1:(set_solver).
                }
                clear H11'.
                ltac1:(rewrite dom_insert_L in Htmp).
                ltac1:(set_solver).
            }
            remember (TermOverBoV_eval ρ2 substituted Htmp2) as ceval2.

            
            assert (Hceval12: ceval = ceval2).
            {
                subst ceval ceval2.
                eapply TermOverBoV_eval__varsofindependent.
                intros x Hx.
                rewrite elem_of_subseteq in Htmp1.
                rewrite elem_of_subseteq in Htmp2.
                specialize (Htmp1 x Hx).
                specialize (Htmp2 x Hx).
                subst substituted.
                unfold TermOver in *.
                rewrite vars_of__TermOverBoV_subst__varless in Hx>[|reflexivity].
                apply e0.
                {
                    rewrite vars_of_uglify.
                    rewrite vars_of_uglify'.
                    clear -Hx.
                    ltac1:(set_solver).
                }
                {
                    ltac1:(set_solver).
                }
            }

            remember (fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))) as V1.
            remember (fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))) as V2.

            eapply frto_step with (t2 := (t_term topSymbol [(t_term cseqSymbol [r; (t_term cseqSymbol [ceval; cont])]); state1])).
            { apply Hheat. }
            { 
                unfold ctx_heat. simpl.
                unfold flattened_rewrites_to. simpl.
                exists (<[h := uglify' r]>(<[V2 := uglify' state1]>(<[V1 := uglify' cont]>ρ1))).
                unfold flattened_rewrites_in_valuation_under_to. simpl.
                (repeat split).
                {
                    constructor.
                    unfold to_PreTerm''.
                    ltac1:(
                        replace ([apply_symbol'' cseqSymbol [uglify' ctrl1; uglify' cont]; uglify' state1])
                        with (map uglify' [(t_term cseqSymbol [ctrl1; cont]);state1])
                        by reflexivity
                    ).
                    ltac1:(
                        replace ([apply_symbol'' cseqSymbol [uglify' c; term_operand (bov_variable V1)]; term_operand (bov_variable V2)])
                        with (map uglify' [t_term cseqSymbol [c; (t_over (bov_variable V1))]; (t_over (bov_variable V2))])
                        by reflexivity
                    ).
                    unfold TermOver in *.
                    apply satisfies_top_bov_cons_1.
                    { reflexivity. }
                    { reflexivity. }
                    {
                        intros i s3 l HH1 HH2.
                        destruct i; simpl in *.
                        {
                            inversion HH1; subst; clear HH1.
                            inversion HH2; subst; clear HH2.
                            constructor.
                            apply satisfies_top_bov_cons_1.
                            {
                                reflexivity.
                            }
                            {
                                reflexivity.
                            }
                            {
                                intros i s3 l HH1 HH2.
                                destruct i; simpl in *.
                                {
                                    symmetry in HH1; inversion HH1; subst; clear HH1.
                                    symmetry in HH2; inversion HH2; subst; clear HH2.
                                    eapply satisfies_TermOver_vars_of>[|apply s].
                                    intros x Hx.
                                    destruct (decide (x = h)).
                                    {
                                        subst x.
                                        ltac1:(rewrite lookup_insert).
                                        ltac1:(rewrite lookup_insert).
                                        reflexivity.
                                    }
                                    {
                                        unfold Valuation in *.
                                        ltac1:(rewrite lookup_insert_ne).
                                        { ltac1:(congruence). }
                                        ltac1:(rewrite -> lookup_insert_ne with (i := h))>[|ltac1:(congruence)].
                                        repeat (rewrite lookup_insert_ne).
                                        { reflexivity. }
                                        {
                                            (* V1 <> x *)
                                            clear -Hx HeqV1.
                                            intros HContra. subst.
                                            assert(Hx': fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                            {
                                                rewrite <- vars_of_uglify in Hx.
                                                ltac1:(set_solver).
                                            }
                                            eapply infinite_is_fresh.
                                            { apply Hx'. }
                                        }
                                        {
                                            (* V2 <> x *)
                                            (*clear -Hx HeqV2.*)
                                            intros HContra. subst.
                                            assert(Hx': fresh (h :: (fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs))) :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: (fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs))) :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                            {
                                                rewrite <- vars_of_uglify in Hx.
                                                ltac1:(set_solver).
                                            }
                                            eapply infinite_is_fresh.
                                            { apply Hx'. }
                                        }
                                    }
                                }
                                {
                                    destruct i; simpl in *.
                                    {
                                        symmetry in HH1; inversion HH1; subst; clear HH1.
                                        symmetry in HH2; inversion HH2; subst; clear HH2.
                                        apply satisfies_var.
                                        unfold Valuation in *.
                                        rewrite lookup_insert_ne.
                                        rewrite lookup_insert_ne.
                                        rewrite lookup_insert.
                                        { reflexivity. }
                                        {
                                            (*clear -HeqV2.*)
                                            intros HContra. subst.
                                            assert(Hx': fresh (h :: (fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs))) :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: (fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs))) :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                            {
                                                rewrite <- HContra at 2.
                                                ltac1:(set_solver).
                                            }
                                            eapply infinite_is_fresh.
                                            { apply Hx'. }
                                        }
                                        {
                                            clear -HeqV1.
                                            intros HContra. subst.
                                            assert(Hx': fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                            {
                                                rewrite HContra at 2.
                                                ltac1:(set_solver).
                                            }
                                            eapply infinite_is_fresh.
                                            { apply Hx'. }
                                        }
                                    }
                                    {
                                        rewrite lookup_nil in HH1.
                                        inversion HH1.
                                    }
                                }
                            }
                        }
                        {
                            destruct i; simpl in *.
                            {
                                symmetry in HH1; inversion HH1; subst; clear HH1.
                                symmetry in HH2; inversion HH2; subst; clear HH2.
                                apply satisfies_var.
                                unfold Valuation in *.
                                rewrite lookup_insert_ne.
                                rewrite lookup_insert.
                                { reflexivity. }
                                {
                                    (*clear -HeqV2.*)
                                    intros HContra. subst.
                                    assert(Hx': fresh (h :: (fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs)) ) :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: (fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs)) ) :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                    {
                                        rewrite HContra at 3.
                                        clear.
                                        ltac1:(set_solver).
                                    }
                                    eapply infinite_is_fresh.
                                    { apply Hx'. }
                                }
                            }
                            {
                                rewrite lookup_nil in HH1.
                                inversion HH1.
                            }
                        }
                    }
                }
                {
                    constructor.
                    unfold to_PreTerm''.
                    ltac1:(
                        replace ([apply_symbol'' cseqSymbol [uglify' r; apply_symbol'' cseqSymbol [uglify' ceval; uglify' cont]]; uglify' state1])
                        with (map uglify' [(t_term cseqSymbol [r; (t_term cseqSymbol [ceval; cont])]); state1])
                        by reflexivity
                    ).
                    ltac1:(
                        replace ([apply_symbol'' cseqSymbol [term_operand (ft_variable h); apply_symbol'' cseqSymbol [uglify' (TermOverBoV_to_TermOverExpr (TermOverBoV_subst c h (t_term holeSymbol []))); term_operand (ft_variable V1)]]; term_operand (ft_variable V2)])
                        with (map uglify' [(t_term cseqSymbol [t_over (ft_variable h); (t_term cseqSymbol [(TermOverBoV_to_TermOverExpr (TermOverBoV_subst c h (t_term holeSymbol []))); (t_over (ft_variable V1))])]); (t_over (ft_variable V2))])
                        by reflexivity
                    ).
                    unfold TermOver in *.
                    apply satisfies_top_bov_cons_expr_1.
                    { reflexivity. }
                    { reflexivity. }
                    {
                        intros i s3 l HH1 HH2.
                        destruct i; simpl in *.
                        {
                            injection HH1 as HH1; subst s3.
                            injection HH2 as HH2; subst l.
                            constructor.
                            apply satisfies_top_bov_cons_expr_1.
                            {
                                reflexivity.
                            }
                            {
                                reflexivity.
                            }
                            {
                                intros i s3 l HH1 HH2.
                                destruct i; simpl in *.
                                {
                                    injection HH1 as HH1; subst s3.
                                    injection HH2 as HH2; subst l.
                                    apply satisfies_var_expr.
                                    unfold Valuation in *.
                                    rewrite lookup_insert.
                                    reflexivity.
                                }
                                {
                                    destruct i; simpl in *.
                                    {
                                        injection HH1 as HH1; subst s3.
                                        injection HH2 as HH2; subst l.
                                        constructor.
                                        apply satisfies_top_bov_cons_expr_1.
                                        { reflexivity. }
                                        { reflexivity. }
                                        intros i s3 l HH1 HH2.
                                        destruct i; simpl in *.
                                        {
                                            injection HH1 as HH1; subst s3.
                                            injection HH2 as HH2; subst l.
                                            subst ceval.
                                            rewrite <- Heqsubstituted.
                                            apply satisfies_TermOverBoV_to_TermOverExpr_2.
                                            eapply satisfies_TermOver_vars_of>[|apply satisfies_TermOverBoV_eval].
                                            intros x Hx.
                                            destruct (decide (x = h)).
                                            {
                                                ltac1:(exfalso).
                                                subst x.
                                                subst substituted.
                                                clear -Hx Hvars.
                                                rewrite vars_of_uglify' in Hx.
                                                ltac1:(set_solver).
                                            }
                                            unfold Valuation in *.
                                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                            destruct (decide (x = V2)).
                                            {
                                                ltac1:(exfalso).
                                                subst x.
                                                subst substituted.
                                                rewrite vars_of_uglify' in Hx.
                                                (*rewrite <- vars_of_uglify in Hx.*)
                                                assert (Htmp: V2 ∈ vars_of c) by ltac1:(set_solver).
                                                clear -Htmp HeqV2.
                                                (*subst V2.*)
                                                assert (Htmp2: fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                                {
                                                    rewrite <- HeqV2.
                                                    assert(Htmp3 := vars_of_uglify V2 c).
                                                    rewrite vars_of_uglify' in Htmp3.
                                                    ltac1:(set_solver).
                                                }
                                                eapply infinite_is_fresh.
                                                apply Htmp2.
                                            }
                                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                            destruct (decide (x = V1)).
                                            {
                                                ltac1:(exfalso).
                                                subst x.
                                                subst substituted.
                                                rewrite vars_of_uglify' in Hx.
                                                assert (Htmp: V1 ∈ vars_of c) by ltac1:(set_solver).
                                                unfold vars_of in Htmp; simpl in Htmp.
                                                
                                                clear -Htmp HeqV1.
                                                (*subst V1. *)
                                                assert (Htmp2: fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                                {
                                                    rewrite <- HeqV1.
                                                    assert(Htmp3 := vars_of_uglify V1 c).
                                                    rewrite vars_of_uglify' in Htmp3.
                                                    ltac1:(set_solver).
                                                }
                                                eapply infinite_is_fresh.
                                                apply Htmp2.
                                            }
                                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                            reflexivity.
                                        }
                                        {
                                            destruct i; simpl in *.
                                            {
                                                injection HH1 as HH1; subst s3.
                                                injection HH2 as HH2; subst l.
                                                apply satisfies_var_expr.
                                                unfold Valuation in *.
                                                rewrite lookup_insert_ne.
                                                rewrite lookup_insert_ne.
                                                rewrite lookup_insert.
                                                { reflexivity. }
                                                {
                                                    clear -HeqV2.
                                                    intros HContra.
                                                    subst.
                                                    assert (H': fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                                    {
                                                        rewrite <- HContra at 2.
                                                        clear. ltac1:(set_solver).
                                                    }
                                                    eapply infinite_is_fresh.
                                                    apply H'.
                                                }
                                                {
                                                    clear -HeqV1.
                                                    intros HContra.
                                                    subst.
                                                    assert (H': fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                                    {
                                                        rewrite HContra at 2.
                                                        clear. ltac1:(set_solver).
                                                    }
                                                    eapply infinite_is_fresh.
                                                    apply H'.
                                                }
                                            }
                                            {
                                                rewrite lookup_nil in HH1.
                                                inversion HH1.
                                            }
                                        }
                                    }
                                    {
                                        rewrite lookup_nil in HH1.
                                        inversion HH1.
                                    }
                                }
                            }
                        }
                        {
                            destruct i; simpl in *.
                            {
                                injection HH1 as HH1; subst s3.
                                injection HH2 as HH2; subst l.
                                apply satisfies_var_expr.
                                destruct (decide (h = V2)).
                                {
                                    subst h.
                                    ltac1:(exfalso).
                                    clear -HeqV2.
                                    assert (Htmp: fresh (V2 :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (V2 :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                    {
                                        rewrite HeqV2 at 2.
                                        ltac1:(set_solver).
                                    }
                                    eapply infinite_is_fresh.
                                    apply Htmp.
                                }
                                unfold Valuation in *.
                                rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                rewrite lookup_insert.
                                reflexivity.
                            }
                            {
                                rewrite lookup_nil in HH1.
                                inversion HH1.
                            }
                        }
                    }
                }
                {
                    eapply satisfies_scs_vars_of>[|apply s0].
                    intros x Hx.
                    unfold Valuation in *.
                    repeat (rewrite lookup_insert_ne).
                    { reflexivity. }
                    {
                        clear -Hx HeqV1.
                        intros HContra. subst.
                        assert(Hx': fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                        {
                            ltac1:(set_solver).
                        }
                        eapply infinite_is_fresh.
                        { apply Hx'. }
                    }
                    {
                        clear -Hx HeqV2.
                        intros HContra. subst.
                        assert(Hx': fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                        {
                            ltac1:(set_solver).
                        }
                        eapply infinite_is_fresh.
                        { apply Hx'. }
                    }
                    {
                        intros HContra. subst.
                        simpl in *.
                        unfold MinusL_LangDef_wf in wfD.
                        simpl in wfD.
                        destruct wfD as [wf1D wf2D].
                        specialize (wf2D _ _ _ e).
                        ltac1:(naive_solver).
                    }
                }
            }
            eapply frto_step_app>[|apply IH|].
            { apply Hcool. }
            unfold flattened_rewrites_to.
            exists (<[h := uglify' v]>(<[V2 := uglify' state2]>(<[V1 := uglify' cont]>ρ2))).
            unfold flattened_rewrites_in_valuation_under_to.
            (repeat split).
            {
                constructor.
                fold (@uglify' (@symbol Σ)).
                unfold to_PreTerm''.
                apply satisfies_top_bov_cons_1.
                { reflexivity. }
                { reflexivity. }
                intros i s3 l HH1 HH2.
                destruct i; simpl in *.
                {
                    injection HH1 as HH1; subst s3.
                    injection HH2 as HH2; subst l.
                    constructor.
                    fold (@uglify' (@symbol Σ)).
                    unfold to_PreTerm''.
                    apply satisfies_top_bov_cons_1.
                    { reflexivity. }
                    { reflexivity. }
                    intros i s3 l HH1 HH2.
                    destruct i; simpl in *.
                    {
                        injection HH1 as HH1; subst s3.
                        injection HH2 as HH2; subst l.
                        apply satisfies_var.
                        unfold Valuation in *.
                        rewrite lookup_insert.
                        reflexivity.
                    }
                    {
                        destruct i; simpl in *.
                        {
                            injection HH1 as HH1; subst s3.
                            injection HH2 as HH2; subst l.
                            constructor.
                            fold (@uglify' (@symbol Σ)).
                            unfold to_PreTerm''.
                            apply satisfies_top_bov_cons_1.
                            { reflexivity. }
                            { reflexivity. }
                            {
                                intros i s3 l HH1 HH2.
                                destruct i; simpl in *.
                                {
                                    injection HH1 as HH1; subst s3.
                                    injection HH2 as HH2; subst l.
                                    rewrite Hceval12.
                                    subst ceval2.
                                    rewrite <- Heqsubstituted.
                                    eapply satisfies_TermOver_vars_of>[|apply satisfies_TermOverBoV_eval].
                                    intros x Hx.

                                    destruct (decide (x = h)).
                                    {
                                        ltac1:(exfalso).
                                        subst x.
                                        subst substituted.
                                        clear -Hx Hvars.
                                        rewrite vars_of_uglify' in Hx.
                                        ltac1:(set_solver).
                                    }
                                    unfold Valuation in *.
                                    rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                    destruct (decide (x = V2)).
                                    {
                                        ltac1:(exfalso).
                                        subst x.
                                        subst substituted.
                                        rewrite vars_of_uglify' in Hx.
                                        assert (Htmp: V2 ∈ vars_of c) by ltac1:(set_solver).
                                        clear -Htmp HeqV2.
                                        
                                        assert (Htmp2: fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                        {
                                            rewrite <- HeqV2.
                                            assert (Htmp3 := vars_of_uglify V2 c).
                                            rewrite vars_of_uglify' in Htmp3.
                                            ltac1:(set_solver).
                                        }
                                        eapply infinite_is_fresh.
                                        apply Htmp2.
                                    }
                                    rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                    destruct (decide (x = V1)).
                                    {
                                        ltac1:(exfalso).
                                        subst x.
                                        subst substituted.
                                        rewrite vars_of_uglify' in Hx.
                                        assert (Htmp: V1 ∈ vars_of c) by ltac1:(set_solver).
                                        clear -Htmp HeqV1.
                                        assert (Htmp2: fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                        {
                                            assert (Htmp3 := vars_of_uglify V1 c).
                                            rewrite vars_of_uglify' in Htmp3.
                                            rewrite <- HeqV1.
                                            ltac1:(set_solver).
                                        }
                                        eapply infinite_is_fresh.
                                        apply Htmp2.
                                    }
                                    rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                    reflexivity.
                                }
                                {
                                    destruct i; simpl in *.
                                    {
                                        injection HH1 as HH1; subst s3.
                                        injection HH2 as HH2; subst l.
                                        apply satisfies_var.
                                        destruct (decide (h = V1)).
                                        {
                                            ltac1:(exfalso).
                                            subst h.
                                            clear -HeqV1.
                                            assert (Htmp1: fresh (V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                            {
                                                rewrite HeqV1 at 2.
                                                ltac1:(set_solver).
                                            }
                                            eapply infinite_is_fresh.
                                            apply Htmp1.
                                        }
                                        unfold Valuation in *.
                                        rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                        destruct (decide (V2 = V1)) as [Heq|?].
                                        {
                                            ltac1:(exfalso).
                                            clear - HeqV2 Heq.
                                            subst V1.
                                            assert (Htmp1: fresh (h :: V2 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V2 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                            {
                                                rewrite HeqV2 at 2.
                                                ltac1:(set_solver).
                                            }
                                            eapply infinite_is_fresh.
                                            apply Htmp1.
                                        }
                                        rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                        apply lookup_insert.
                                    }
                                    {
                                        rewrite lookup_nil in HH1.
                                        inversion HH1.
                                    }
                                }
                            }
                        }
                        {
                            rewrite lookup_nil in HH1.
                            inversion HH1.
                        }
                    }
                }
                {
                    destruct i; simpl in *.
                    {
                        injection HH1 as HH1; subst s3.
                        injection HH2 as HH2; subst l.
                        apply satisfies_var.
                        destruct (decide (h = V2)) as [Heq|?].
                        {
                            ltac1:(exfalso).
                            subst h.
                            clear - HeqV2.
                            assert (Htmp1: fresh (V2 :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (V2 :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                            {
                                rewrite HeqV2 at 2. ltac1:(set_solver).
                            }
                            eapply infinite_is_fresh.
                            apply Htmp1.
                        }
                        unfold Valuation in *.
                        rewrite lookup_insert_ne>[|ltac1:(congruence)].
                        apply lookup_insert.
                    }
                    {
                        rewrite lookup_nil in HH1.
                        inversion HH1.
                    }

                }
            }
            {
                constructor.
                fold (@uglify' (@symbol Σ)).
                unfold to_PreTerm''.
                apply satisfies_top_bov_cons_expr_1.
                { reflexivity. }
                { reflexivity. }
                intros i s3 l HH1 HH2.
                destruct i; simpl in *.
                {
                    injection HH1 as HH1; subst s3.
                    injection HH2 as HH2; subst l.

                    constructor.
                    fold (@uglify' (@symbol Σ)).
                    unfold to_PreTerm''.
                    apply satisfies_top_bov_cons_expr_1.
                    { reflexivity. }
                    { reflexivity. }
                    intros i s3 l HH1 HH2.
                    destruct i; simpl in *.
                    {
                        injection HH1 as HH1; subst s3.
                        injection HH2 as HH2; subst l.
                        apply satisfies_TermOverBoV_to_TermOverExpr_2.
                        eapply satisfies_TermOver_vars_of>[|apply s1].
                        intros x Hx.
                        destruct (decide (x = h)).
                        {
                            subst x.
                            unfold Valuation in *.
                            rewrite lookup_insert.
                            rewrite lookup_insert.
                            reflexivity.
                        }
                        {
                            unfold Valuation in *.
                            rewrite lookup_insert_ne with (i := h) (j := x)>
                                [|ltac1:(congruence)].
                            rewrite lookup_insert_ne with (i := h) (j := x)>
                                [|ltac1:(congruence)].
                            destruct (decide (x = V2)).
                            {
                                ltac1:(exfalso).
                                subst x.
                                rewrite <- vars_of_uglify in Hx.
                                clear - HeqV2 Hx.
                                assert (Htmp1: fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                {
                                    ltac1:(set_solver).
                                }
                                eapply infinite_is_fresh.
                                apply Htmp1.
                            }
                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                            destruct (decide (x = V1)).
                            {
                                ltac1:(exfalso).
                                subst x.
                                rewrite <- vars_of_uglify in Hx.
                                clear - HeqV1 Hx.
                                assert (Htmp1: fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                {
                                    ltac1:(set_solver).
                                }
                                eapply infinite_is_fresh.
                                apply Htmp1.
                            }
                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                            reflexivity.
                        }
                    }
                    {
                        destruct i; simpl in *.
                        {
                            injection HH1 as HH1; subst s3.
                            injection HH2 as HH2; subst l.
                            apply satisfies_var_expr.
                            assert (V1 <> h).
                            {
                                intros HContra. subst h.
                                clear - HeqV1.
                                assert (Htmp1: fresh (V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                {
                                    rewrite HeqV1 at 2. ltac1:(set_solver).
                                }
                                eapply infinite_is_fresh.
                                apply Htmp1.
                            }
                            unfold Valuation in *.
                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                            destruct (decide (V2 = V1)) as [Heq|?].
                            {
                                ltac1:(exfalso).
                                clear - HeqV2 Heq.
                                subst V1.
                                assert (Htmp1: fresh (h :: V2 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V2 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                {
                                    rewrite HeqV2 at 2.
                                    ltac1:(set_solver).
                                }
                                eapply infinite_is_fresh.
                                apply Htmp1.
                            }
                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                            apply lookup_insert.
                        }
                        {
                            rewrite lookup_nil in HH1.
                            inversion HH1.
                        }
                    }
                }
                {
                    destruct i; simpl in *.
                    {
                        injection HH1 as HH1; subst s3.
                        injection HH2 as HH2; subst l.
                        apply satisfies_var_expr.
                        assert (V2 <> h).
                        {
                            intros HContra. subst h.
                            clear - HeqV2.
                            assert (Htmp1: fresh (V2 :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (V2 :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                            {
                                rewrite HeqV2 at 2. ltac1:(set_solver).
                            }
                            eapply infinite_is_fresh.
                            apply Htmp1.
                        }
                        unfold Valuation in *.
                        rewrite lookup_insert_ne>[|ltac1:(congruence)].
                        apply lookup_insert.
                    }
                    {
                        rewrite lookup_nil in HH1.
                        inversion HH1.
                    }
                }
            }
            {
                simpl.
                apply satisfies__MinusL_isValue__subst in s2.
                simpl in s2.
                apply satisfies_insert_MinusL_isValue; simpl.
                { 
                    intros HContra.
                    unfold MinusL_LangDef_wf in wfD.
                    revert wfD. intros wfD. simpl in wfD.
                    destruct wfD as [wf1D wf2D].
                    rewrite wf1D in HContra.
                    rewrite elem_of_singleton in HContra.
                    subst h.
                    eapply wf2D. apply e.
                    specialize (wf2D _ _ _ e).
                    ltac1:(naive_solver).
                }
                {
                    unfold Valuation in *.
                    rewrite insert_commute with (i := iV_var)(j := V2).
                    rewrite insert_commute with (i := iV_var)(j := V1).
                    eapply satisfies_scs_vars_of>[|apply s2].
                    {
                        intros x Hx.
                        unfold Valuation in *.
                        symmetry.
                        destruct (decide (x = V2)).
                        {
                            subst x.
                            ltac1:(exfalso).
                            clear -Hx HeqV2.
                            
                            assert (Htmp3: fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs)) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs))).
                            {
                                ltac1:(set_solver).
                            }
                            eapply infinite_is_fresh.
                            apply Htmp3.
                        }
                        rewrite lookup_insert_ne>[|ltac1:(congruence)].
                        destruct (decide (x = V1)).
                        {
                            subst x.
                            ltac1:(exfalso).
                            clear -Hx HeqV1.
                            
                            assert (Htmp3: fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs)) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ elements (vars_of iV_scs))).
                            {
                                ltac1:(set_solver).
                            }
                            eapply infinite_is_fresh.
                            apply Htmp3.
                        }
                        rewrite lookup_insert_ne>[|ltac1:(congruence)].
                        reflexivity.
                    }
                    {
                        intros HContra.
                        revert wfD. intros wfD.
                        unfold MinusL_LangDef_wf in wfD. simpl in wfD.
                        destruct wfD as [wf1D wf2D].
                        clear - HContra HeqV1 wf1D.
                        rewrite wf1D in HeqV1. clear wf1D.
                        rewrite elements_singleton in HeqV1.
                        rewrite HContra in HeqV1. clear HContra.
                        assert (Htmp3: fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ [V1]) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ [V1])).
                        {
                            rewrite HeqV1 at 2. ltac1:(set_solver).
                        }
                        eapply infinite_is_fresh.
                        apply Htmp3.
                    }
                    {
                        intros HContra.
                        revert wfD. intros wfD.
                        unfold MinusL_LangDef_wf in wfD. simpl in wfD.
                        destruct wfD as [wf1D wf2D].
                        clear - HContra HeqV2 wf1D.
                        rewrite wf1D in HeqV2. clear wf1D.
                        rewrite elements_singleton in HeqV2.
                        rewrite HContra in HeqV2. clear HContra.
                        assert (Htmp3: fresh (h :: V1:: vars_of_to_l2r c ++ elements (vars_of scs) ++ [V2]) ∈ (h :: V1:: vars_of_to_l2r c ++ elements (vars_of scs) ++ [V2])).
                        {
                            rewrite HeqV2 at 2. ltac1:(set_solver).
                        }
                        eapply infinite_is_fresh.
                        apply Htmp3.
                    }
                }
            }
        }
    }
Qed.
*)

Definition isDownC
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (t : TermOver builtin_value)
    : Prop
:=
    exists ctrl data cont,
    t = downC topSymbol cseqSymbol ctrl data cont
.

Fixpoint hasDepthExactly
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (depth : nat)
    (t : TermOver builtin_value)
:=
    match t with
    | t_term _ [t_term _ [ctlr; cont]; _] =>
        match depth with
        | 0 => False
        | S depth' =>
            isDownC topSymbol cseqSymbol t /\
            hasDepthExactly topSymbol cseqSymbol depth' cont
        end
    | _ => depth = 0
    end
.

Definition projTopCtrl
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    match t with
    | t_term _ [t_term _ [ctrl; _]; _] => Some ctrl
    | _ => None
    end
.

Definition projTopCont
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    match t with
    | t_term _ [t_term _ [_; cont]; _] => Some cont
    | _ => None
    end
.

Definition projTopData
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    match t with
    | t_term _ [_; data] => Some data
    | _ => None
    end
.

#[export]
Instance IsDownC_dec
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (t : TermOver builtin_value)
    : Decision (isDownC topSymbol cseqSymbol t)
.
Proof.
    unfold isDownC.
    remember (projTopCtrl t) as mctrl.
    remember (projTopCont t) as mcont.
    remember (projTopData t) as mdata.
    destruct mctrl.
    {
        destruct mcont.
        {
            destruct mdata.
            {
                unfold downC.
                unfold projTopCtrl, projTopCont,projTopData in *.
                ltac1:(repeat case_match; simplify_eq/=).
                destruct (decide (s = topSymbol)).
                {
                    destruct (decide (s0 = cseqSymbol)).
                    {
                        subst.
                        left.
                        exists t5,t4,t6.
                        reflexivity.
                    }
                    {
                        right.
                        intros HContra.
                        ltac1:(naive_solver).
                    }
                }
                {
                    right.
                    intros HContra.
                    ltac1:(naive_solver).
                }
            }
            {
                right.
                unfold projTopData in Heqmdata.
                ltac1:(repeat case_match; simplify_eq/=; naive_solver).
            }
        }
        {
            right.
            unfold projTopCont in Heqmcont.
            ltac1:(repeat case_match; simplify_eq/=; naive_solver).
        }
    }
    {
        right.
        unfold projTopCtrl in Heqmctrl.
        ltac1:(repeat case_match; simplify_eq/=; naive_solver).
    }
Defined.

Lemma flat_map_lookup_Some
    {A B : Type}
    (f : A -> list B)
    (l : list A)
    (i : nat)
    (y : B)
    :
    (flat_map f l) !! i = Some y ->
    { j : nat & { x : A & { k : nat & l !! j = Some x /\ (f x) !! k = Some y } } }
.
Proof.
    revert i.
    induction l; simpl; intros i HH.
    {
        rewrite lookup_nil in HH.
        inversion HH.
    }
    {
        destruct (decide (i < length (f a))) as [Hlt|Hgeq].
        {
            rewrite lookup_app_l in HH>[|exact Hlt].
            exists 0.
            exists a.
            exists i.
            simpl.
            split>[reflexivity|].
            exact HH.            
        }
        {
            rewrite lookup_app_r in HH.
            specialize (IHl _ HH).
            destruct IHl as [j [x [k [H1 H2]]]].
            exists (S j).
            exists x.
            exists k.
            simpl.
            split>[apply H1|].
            exact H2.
            ltac1:(lia).
        }
    }
Qed.

Lemma map_lookup_Some
    {A B : Type}
    (f : A -> B)
    (l : list A)
    (i : nat)
    (y : B)
    :
    (map f l) !! i = Some y ->
    {x : A & (l !! i = Some x /\ y = f x)}
.
Proof.
    revert i.
    induction l; simpl; intros i HH.
    {
        rewrite lookup_nil in HH. inversion HH.
    }
    {
        destruct i.
        {
            simpl in HH. inversion HH; subst; clear HH.
            exists a. split; reflexivity.
        }
        {
            simpl in HH.
            specialize (IHl _ HH).
            destruct IHl as [x [H1x H2x]].
            subst y.
            exists x.
            simpl.
            split>[assumption|reflexivity].
        }
    }
Qed.

Lemma in_compile_inv
    {Σ : StaticModel}
    (Act : Set)
    {_aD : EqDecision Act}
    (D: MinusL_LangDef Act)
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable)
    (r : RewritingRule Act)
:
  r
∈ compile invisible_act topSymbol cseqSymbol holeSymbol
  continuationVariable D ->
  (
    (
        { lc : TermOver BuiltinOrVar &
        { ld : TermOver BuiltinOrVar &
        { a : Act &
        { rc : TermOver Expression &
        { rd : TermOver Expression &
        { scs : list SideCondition &
            mld_rewrite Act lc ld a rc rd scs ∈ mlld_decls Act D /\
            r =
            {|
                fr_from :=
                apply_symbol' topSymbol
                [apply_symbol' cseqSymbol
                [uglify' lc; term_operand (bov_variable continuationVariable)];
                uglify' ld];
                fr_to :=
                apply_symbol' topSymbol
                [apply_symbol' cseqSymbol
                [uglify' rc; term_operand (ft_variable continuationVariable)];
                uglify' rd];
                fr_scs := scs;
                fr_act := a
            |}
        }}}}}}
    ) + (
        { c : _ &
        { h : variable &
        { scs : list SideCondition &
        mld_context Act c h scs ∈ mlld_decls Act D /\
        (
            r = ctx_heat invisible_act topSymbol cseqSymbol holeSymbol
                (fresh
                (h
                :: vars_of_to_l2r c ++
                elements (vars_of scs) ++
                elements (vars_of (mlld_isValue_scs Act D))))
                (fresh
                (h
                :: fresh
                (h
                :: vars_of_to_l2r c ++
                elements (vars_of scs) ++
                elements (vars_of (mlld_isValue_scs Act D)))
                :: vars_of_to_l2r c ++
                elements (vars_of scs) ++
                elements (vars_of (mlld_isValue_scs Act D))))
                (MinusL_isValue Act D) c h
                scs
            \/
            r =
            ctx_cool invisible_act topSymbol cseqSymbol holeSymbol
            (fresh
            (h
            :: vars_of_to_l2r c ++
            elements (vars_of scs) ++
            elements (vars_of (mlld_isValue_scs Act D))))
            (fresh
            (h
            :: fresh
            (h
            :: vars_of_to_l2r c ++
            elements (vars_of scs) ++
            elements (vars_of (mlld_isValue_scs Act D)))
            :: vars_of_to_l2r c ++
            elements (vars_of scs) ++
            elements (vars_of (mlld_isValue_scs Act D))))
            (MinusL_isValue Act D) c
          h
        )
        }}}
    )
  )
.
Proof.
    intros HH.
    unfold compile in HH.
    eapply list_find_elem_of_isSome with (P := (eq r)) in HH.
    {
        unfold is_true,isSome in *.
        ltac1:(case_match).
        {
            clear HH.
            ltac1:(rename H into HH).
            destruct p as [i d].
            apply list_find_Some in HH.
            destruct HH as [HH1 [? HH2]].
            subst d.
            apply flat_map_lookup_Some in HH1.
            destruct HH1 as [j [x [k [HH3 HH4]]]].
            apply map_lookup_Some in HH3.
            destruct HH3 as [y [H1y H2y]].
            subst x.
            unfold compile' in HH4.
            destruct y.
            {
                destruct k.
                {
                    left. do 6 (eexists).
                    rewrite elem_of_list_lookup.
                    split.
                    {
                        eexists. eapply H1y.
                    }
                    {
                        simpl in HH4. inversion HH4; subst; clear HH4.
                        reflexivity.
                    }
                }
                {
                    inversion HH4.
                }
            }
            {
                right.
                do 3 eexists.
                split.
                {
                    rewrite elem_of_list_lookup.
                    eexists. eapply H1y.
                }
                {
                    destruct k; inversion HH4; subst; clear HH4.
                    {
                        left. reflexivity.
                    }

                    destruct k; inversion H0; subst; clear H0.
                    {
                        right. reflexivity.
                    }
                }
            }
        }
        {
            inversion HH.
        }
    }
    {
        reflexivity.
    }
    Unshelve.
    intros ?. apply _.
Qed.

Fixpoint frto_all_nonlast_states_satisfy
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    (P : TermOver builtin_value -> Prop)
    (x y : TermOver builtin_value)
    (w : list Act)
    (r : flattened_rewrites_to_over Γ x w y)
    :
    Prop
:=
    match r with
    | frto_base _ _ => True
    | frto_step _ t1 t2 t3 _ _ d _ _ r' =>
        P t1 /\
        frto_all_nonlast_states_satisfy Γ P _ _ _ r'
    end
.

Lemma split_frto_by_state_pred
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    (P : TermOver builtin_value -> Prop)
    (_dP : forall t, Decision (P t))
    (x z : TermOver builtin_value)
    (w : list Act)
    (r : flattened_rewrites_to_over Γ x w z)
    :
    (
    { w1 : list Act &
    { w2 : list Act &
    { y : TermOver builtin_value &
    { r1 : flattened_rewrites_to_over Γ x w1 y & 
        (
        (flattened_rewrites_to_over Γ y w2 z) *
        (w1 ++ w2 = w) *
        (frto_all_nonlast_states_satisfy Γ (fun arg => ~ (P arg)) _ _ _ r1) *
        (P y)
        )%type
    }
    } } }
    ) + ( frto_all_nonlast_states_satisfy Γ (fun arg => ~ (P arg)) _ _ _ r )
.
Proof.
    ltac1:(induction r).
    {
        right. simpl. exact I.
    }
    {
        destruct (decide (P t1)) as [holds|nhold].
        {
            left.
            exists [].
            exists (a::w).
            exists t1.
            exists (frto_base _ t1).
            (repeat split).
            {
                econstructor.
                { apply e. }
                { apply f. }
                { apply r0. }
            }
            { apply holds. }
        }
        {
            destruct IHr as [IHr|IHr].
            {
                left.
                destruct IHr as [w1 [w2 [y [r1 [[[IH1 IH2] IH3] IH4]]]]].
                subst w.
                exists (a::w1).
                exists w2.
                exists y.
                exists (frto_step _ t1 t2 y (w1) a r e f r1).
                (repeat split); assumption.

            }
            {
                right. simpl. split;assumption.
            }
        }
    }
Qed.

Lemma compile_correct_2
    {Σ : StaticModel}
    {Act : Set}
    {_AD : EqDecision Act}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable) 
    (D : MinusL_LangDef Act)
    (HcvD: continuationVariable ∉ vars_of D)
    (wfD : MinusL_LangDef_wf Act D)
    :
    ~ (invisible_act ∈ actions_of_ldef Act D) ->
    let Γ := compile invisible_act topSymbol cseqSymbol holeSymbol continuationVariable D in
    forall
        (lc ld rc rd : TermOver builtin_value)
        (w : list Act),
        (
            { w' : list Act & 
            ((w = (filter (fun x => x <> invisible_act) w')) *
            (* w <> [] /\ *)
            forall cont,
            flattened_rewrites_to_over Γ
                (downC topSymbol cseqSymbol lc ld cont)
                w'
                (downC topSymbol cseqSymbol rc rd cont)
            )%type
            }
        ) ->
        MinusL_rewrites Act D lc ld w rc rd
.
Proof.
    intros H1 Γ ctrl1 data1 ctrl2 data2 w H2.
    destruct H2 as [w' [H1w' (*[H2w'*) H3w' (*]*)]].
    unfold downC in H3w'.
    unfold TermOver in *.
    specialize (H3w' (t_term cseqSymbol [])).
    remember ((t_term topSymbol [t_term cseqSymbol [ctrl1; t_term cseqSymbol []]; data1])) as from.
    remember ((t_term topSymbol [t_term cseqSymbol [ctrl2; t_term cseqSymbol []]; data2])) as to.
    assert (HfrIDC: isDownC topSymbol cseqSymbol from).
    {
        subst from. eexists. eexists. eexists. reflexivity.
    }
    assert (HtoIDC: isDownC topSymbol cseqSymbol to).
    {
        subst to. eexists. eexists. eexists. reflexivity.
    }
    assert (Hc1: projTopCtrl from = Some ctrl1).
    {
        subst from. simpl. reflexivity.
    }
    assert (Hd1: projTopData from = Some data1).
    {
        subst from. simpl. reflexivity.
    }
    assert (Hc2: projTopCtrl to = Some ctrl2).
    {
        subst to. simpl. reflexivity.
    }
    assert (Hd2: projTopData to = Some data2).
    {
        subst to. simpl. reflexivity.
    }
    remember (1) as depth in |-.
    assert (Hfrdepth: hasDepthExactly topSymbol cseqSymbol depth from).
    {
        subst from depth. simpl.
        split>[|reflexivity].
        assumption.
    }
    assert (Htodepth: hasDepthExactly topSymbol cseqSymbol depth to).
    {
        subst to depth. simpl.
        split>[|reflexivity].
        assumption.
    }
    clear Heqfrom Heqto Heqdepth.
    revert w H1w' (* H2w' *) ctrl1 data1 ctrl2 data2 Hc1 Hd1 Hc2 Hd2 HfrIDC HtoIDC depth Hfrdepth Htodepth.
    induction H3w'; intros w'' H1w' (* H2w' *) ctrl1 data1 ctrl2 data2 Hc1 Hd1 Hc2 Hd2 HfrIDC HtoIDC depth Hfrdepth Htodepth.
    {
        rewrite filter_nil in H1w'.
        unfold projTopCtrl in *.
        unfold projTopData in *.
        ltac1:(repeat case_match); ltac1:(simplify_eq/=).
        apply mlr_refl.
    }
    {
        assert (H' := e). (* just to have some backup *)
        ltac1:(unfold Γ in e).
        apply in_compile_inv in e>[|apply _].
        assert (Hsplit := @split_frto_by_state_pred Σ Act Γ).

        destruct e as [e|e].
        {
            destruct e as [lc [ld [a0 [rc [rd [scs [H1r H2r]]]]]]].
            subst r. simpl in *.
            unfold flattened_rewrites_to in f.
            destruct f as [ρ1 Hρ1].
            unfold flattened_rewrites_in_valuation_under_to in Hρ1.
            destruct Hρ1 as [[[Hρ1 Hρ2] Hρ3] Hρ4].
            simpl in *.
            subst a0.

            rewrite filter_cons in H1w'.
            destruct (decide (a = invisible_act)).
            {
                subst a.
                ltac1:(exfalso).
                clear - H1 H1r.
                apply H1. clear H1.
                unfold actions_of_ldef.
                rewrite elem_of_list_In.
                rewrite in_concat.
                eexists.
                rewrite in_map_iff.
                unfold actions_of_decl.
                split.
                {
                    exists (mld_rewrite Act lc ld invisible_act rc rd scs).
                    split>[reflexivity|].
                    rewrite <- elem_of_list_In.
                    exact H1r.
                }
                constructor. reflexivity.
            }
            rewrite decide_True in H1w'>[|assumption].
            clear H2w'. subst w''.
            assert (Hρ1':
                satisfies ρ1 t1 (t_term topSymbol [(t_term cseqSymbol [lc; t_over (bov_variable continuationVariable)]);(ld)])
            ).
            {
                apply Hρ1.
            }
            clear Hρ1.
            apply satisfies_term_bov_inv in Hρ1'.
            destruct Hρ1' as [lγ1 [[Ht1 HH1] HH2]].
            simpl in HH1.
            destruct lγ1 as [|γ1 lγ1].
            {
                simpl in HH1. inversion HH1.
            }
            destruct lγ1 as [|γ2 lγ2].
            {
                simpl in HH1. inversion HH1.
            }
            destruct lγ2>[|simpl in HH1; ltac1:(lia)].
            clear HH1.
            assert (HH20 := HH2 0 _ _ eq_refl eq_refl).
            assert (HH21 := HH2 1 _ _ eq_refl eq_refl).
            clear HH2.
            apply satisfies_term_bov_inv in HH20.
            destruct HH20 as [lγ [[Hγ1 HH4] HH5]].
            simpl in HH4.
            destruct lγ as [|γ3 lγ].
            { simpl in HH4. inversion HH4. }
            destruct lγ as [|γ4 lγ].
            { simpl in HH4. inversion HH4. }
            destruct lγ>[|simpl in HH4; ltac1:(lia)].
            clear HH4.
            assert (HH50 := HH5 0 _ _ eq_refl eq_refl).
            assert (HH51 := HH5 1 _ _ eq_refl eq_refl).
            clear HH5.
            
            subst.
            apply satisfies_var_inv in HH51.
            

            (* do the same with Hρ2, but have fresh names *)
            assert (Hρ2': satisfies ρ1 t2 (t_term topSymbol [(t_term cseqSymbol [(rc);(t_over (ft_variable continuationVariable))]);rd])).
            {
                apply Hρ2.
            }
            clear Hρ2.
            apply satisfies_term_expr_inv in Hρ2'.
            destruct Hρ2' as [lγ2 [[Ht2 HH3] HH4]].
            simpl in *.
            destruct lγ2 as [|γ4' lγ2].
            { simpl in HH21. inversion HH3. }
            destruct lγ2 as [|γ5 lγ2].
            { simpl in HH21. inversion HH3. }
            destruct lγ2>[|simpl in HH3; ltac1:(lia)].
            clear HH30.
            assert (HH40 := HH4 0 _ _ eq_refl eq_refl).
            assert (HH41 := HH4 1 _ _ eq_refl eq_refl).
            subst.
            clear HH4.
            apply satisfies_term_expr_inv in HH40.
            destruct HH40 as [lγ [[Hγ4 HH5] HH6]].
            simpl in *. subst.
            destruct lγ as [|γ6 lγ].
            { inversion HH5. }
            destruct lγ as [|γ7 lγ].
            { inversion HH5. }
            destruct lγ>[|simpl in HH5; ltac1:(lia)].
            clear HH5 HH3.
            assert (HH60 := HH6 0 _ _ eq_refl eq_refl).
            assert (HH61 := HH6 1 _ _ eq_refl eq_refl).
            clear HH6.
            apply satisfies_var_expr_inv in HH61.
            inversion Hd1; subst; clear Hd1.
            inversion Hc1; subst; clear Hc1.
            subst.
            unfold TermOver in *.
            (*
            rewrite HH6 in HH26. inversion HH26; subst; clear HH26.
            apply (f_equal prettify) in H0.
            rewrite (cancel prettify uglify') in H0.
            rewrite (cancel prettify uglify') in H0.
            subst γ7.*)

            (*destruct (decide (filter (λ x : Act, x ≠ invisible_act) w = [])) as [Hnil|Hnnil].*)
            

            ltac1:(
                replace 
                    ((a :: filter (λ x : Act, x ≠ invisible_act) (w)))
                with
                    (([a] ++ filter (λ x : Act, x ≠ invisible_act) (w)))
                by reflexivity
            ).
            eapply mlr_trans.
            {
                eapply mlr_rule with (ρ := ρ1).
                { apply H1r. }
                { assumption. }
                { assumption. }
                { apply HH60. }
                { apply HH41. }
                { assumption. }
            }
            {
                apply IHH3w' with (depth := S depth); simpl in *.
                { reflexivity. }
                { reflexivity. }
                { reflexivity. }
                { assumption. }
                { assumption. }
                {
                    unfold isDownC.
                    eexists. eexists. eexists.
                    reflexivity.
                }
                { assumption. }
                {
                    simpl.
                    admit.
                }
                admit.
            }
        }
        {
            (*
            destruct H as [c [h [Hh [scs [Hhscs [HH1 HH2]]]]]].
            destruct HH2 as [HH2|HH2].
            {
                subst r.
                unfold flattened_rewrites_to in H0.
                destruct H0 as [ρ1 Hρ1].
                unfold flattened_rewrites_in_valuation_under_to in Hρ1.
                destruct Hρ1 as [HH2 [HH3 [HH4 HH5]]].
                simpl in *.
                subst a.
                clear H'.

                assert (
                    HH2':
                    satisfies ρ1 t1 (t_term topSymbol [
                        (t_term cseqSymbol [
                            (c)
                            ;
                            (t_over ((bov_variable
                                (fresh
                                (h
                                :: vars_of_to_l2r c ++
                                elements (vars_of scs) ++
                                elements (vars_of (mlld_isValue_scs Act D)))))))
                        ])
                        ;
                        (t_over ((bov_variable
                                (fresh
                                (h
                                :: fresh
                                (h
                                :: vars_of_to_l2r c ++
                                elements (vars_of scs) ++
                                elements (vars_of (mlld_isValue_scs Act D)))
                                :: vars_of_to_l2r c ++
                                elements (vars_of scs) ++
                                elements (vars_of (mlld_isValue_scs Act D)))))))
                    ])
                ).
                {
                    apply HH2.
                }
                clear HH2.
                assert ( HH3':
                    satisfies ρ1 t2 (
                        t_term topSymbol [
                            (t_term cseqSymbol [
                                (t_over (ft_variable h))
                                ;
                                (t_term cseqSymbol [
                                    (TermOverBoV_to_TermOverExpr
  (TermOverBoV_subst c h (t_term holeSymbol [])));
                                    (
                                        t_over (
                                            (ft_variable
                                                (fresh
                                                (h
                                                :: vars_of_to_l2r c ++
                                                elements (vars_of scs) ++
                                                elements (vars_of (mlld_isValue_scs Act D)))))
                                        )
                                    )
                                ])
                            ]);
                            (
                                t_over (
                                    (ft_variable
                                        (fresh
                                        (h
                                        :: fresh
                                        (h
                                        :: vars_of_to_l2r c ++
                                        elements (vars_of scs) ++
                                        elements (vars_of (mlld_isValue_scs Act D)))
                                        :: vars_of_to_l2r c ++
                                        elements (vars_of scs) ++
                                        elements (vars_of (mlld_isValue_scs Act D)))))
                                )
                            )
                        ]
                    )
                ).
                {
                    apply HH3.
                }
                clear HH3.
                apply satisfies_term_inv in HH2'.
                destruct HH2' as [lγ [Ht1 [Hlen Hfa]]].
                simpl in *.
                destruct lγ as [|γ1 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ as [|γ2 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ>[|simpl in Hlen; ltac1:(lia)].
                unfold zip_with in Hfa.
                repeat (rewrite Forall_cons in Hfa).
                rewrite Forall_nil in Hfa.
                destruct Hfa as [HH4' [HH5' _]].
                clear Hlen.

                apply satisfies_term_inv in HH4'.
                destruct HH4' as [lγ [Hγ1 [Hlen Hfa]]].
                simpl in *.
                destruct lγ as [|γ3 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ as [|γ4 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ>[|simpl in Hlen; ltac1:(lia)].
                unfold zip_with in Hfa.
                repeat (rewrite Forall_cons in Hfa).
                rewrite Forall_nil in Hfa.
                destruct Hfa as [HH6' [HH7' _]].
                clear Hlen.
                apply satisfies_var_inv in HH7'.
                apply satisfies_var_inv in HH5'.

                apply satisfies_term_expr_inv in HH3'.
                destruct HH3' as [lγ [Hγ2 [Hlen Hfa]]].
                simpl in *.
                destruct lγ as [|γ5 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ as [|γ6 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ>[|simpl in Hlen; ltac1:(lia)].
                unfold zip_with in Hfa.
                repeat (rewrite Forall_cons in Hfa).
                rewrite Forall_nil in Hfa.
                destruct Hfa as [HH8' [HH9' _]].
                clear Hlen.

                apply satisfies_term_expr_inv in HH8'.
                destruct HH8' as [lγ [Hγ3 [Hlen Hfa]]].
                simpl in *.
                destruct lγ as [|γ7 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ as [|γ8 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ>[|simpl in Hlen; ltac1:(lia)].
                unfold zip_with in Hfa.
                repeat (rewrite Forall_cons in Hfa).
                rewrite Forall_nil in Hfa.
                destruct Hfa as [HH10' [HH11' _]].
                clear Hlen.

                apply satisfies_term_expr_inv in HH11'.
                destruct HH11' as [lγ [Hγ4 [Hlen Hfa]]].
                simpl in *.
                destruct lγ as [|γ9 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ as [|γ10 lγ] >[simpl in Hlen; inversion Hlen|].
                destruct lγ>[|simpl in Hlen; ltac1:(lia)].
                unfold zip_with in Hfa.
                repeat (rewrite Forall_cons in Hfa).
                rewrite Forall_nil in Hfa.
                destruct Hfa as [HH12' [HH13' _]].
                clear Hlen.

                apply satisfies_var_expr_inv in HH13'.
                apply satisfies_var_expr_inv in HH9'.
                subst.

                rewrite HH5' in HH9'.
                inversion HH9'; subst; clear HH9'.
                apply (f_equal prettify) in H0.
                rewrite (cancel prettify uglify') in H0.
                rewrite (cancel prettify uglify') in H0.
                subst γ6.

                rewrite filter_cons.
                destruct (decide (invisible_act <> invisible_act))>[ltac1:(congruence)|].
                clear n.

                rewrite HH7' in HH13'.
                inversion HH13'; subst; clear HH13'.
                apply (f_equal prettify) in H0.
                rewrite (cancel prettify uglify') in H0.
                rewrite (cancel prettify uglify') in H0.
                subst γ10.
                apply satisfies_var_expr_inv in HH10'.
                
                simpl in Hc1. inversion Hc1; subst; clear Hc1.
                simpl in Hd1. inversion Hd1; subst; clear Hd1.

                rewrite satisfies_TermOverBoV_to_TermOverExpr in HH12'.
                remember (fresh
                    (h
                    :: vars_of_to_l2r c ++
                    elements (vars_of scs) ++
                    elements (vars_of (mlld_isValue_scs Act D)))) as V1.
                
                remember (fresh
                    (h
                    :: V1
                    :: vars_of_to_l2r c ++
                    elements (vars_of scs) ++
                    elements (vars_of (mlld_isValue_scs Act D)))) as V2.

                apply factor_by_subst_correct_2 with (sz := TermOver_size γ9) in HH12'
                    >[()|ltac1:(lia)|(exact Hh)|(simpl; ltac1:(set_solver))].

                destruct HH12' as [Hfs1 Hfs2].

                remember ((factor_by_subst (TermOver_size γ9) ρ1 h γ9 c
  (t_term holeSymbol [])).2) as fs2.

                unfold Valuation in *.
                eapply mlr_context with (ρ1 := (<[h:=uglify' fs2]> ρ1))(r := γ7) >[apply HH1|()|(
                    unfold Valuation in *; rewrite insert_insert; rewrite insert_id>[exact HH6'|exact HH10']
                )|(
                    rewrite satisfies_scs_vars_of >[apply HH4|];
                    intros x Hx;
                    destruct (decide (x = h))>
                    [(ltac1:(exfalso); subst; apply Hhscs; apply Hx)|unfold Valuation in *; (rewrite lookup_insert_ne>[reflexivity|(ltac1:(congruence))])]
                    (*apply HH4*) 
                )|()|()|].

                
                (* Not sure since this point*)
                (* apply factor_by_subst_correct' with (sz := TermOver_size γ9) in HH12' . *)
                (*
                apply IHH3w'.
                { reflexivity. }
                {
                    simpl.
                }
                *)
            }
            {

            }
            *)
            admit.
        }
    }
Abort.

Search vars_of_to_l2r.
About vars_of_uglify.


Search sum_list_with compose.
