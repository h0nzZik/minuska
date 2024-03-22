From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    semantics_properties
    basic_matching
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

Lemma satisfies_top_bov
    {Σ : StaticModel}
    (ρ : Valuation)
    topSymbol
    (ctrl1 state1 : TermOver builtin_value) (lc ld : TermOver BuiltinOrVar)
    :
    (satisfies ρ ctrl1 lc /\ satisfies ρ state1 ld) <->
    satisfies ρ (apply_symbol' topSymbol [uglify' ctrl1; uglify' state1])
        (apply_symbol' topSymbol [uglify' lc; uglify' ld])
.
Proof.
    split.
    {
        intros [H1 H2].
        unfold apply_symbol'. simpl.
        destruct ctrl1,lc,state1,ld; simpl in *; (repeat constructor);
            inversion H1; inversion H2; subst; assumption.
    }
    {
        intros H.
        inversion H; subst; clear H.
        inversion pf; subst; clear pf;
        destruct ctrl1,lc,state1,ld;
            unfold to_PreTerm' in *;
            simpl in *;
            try (solve [inversion H1]);
            ltac1:(simplify_eq/=);
            try (inversion H; subst; clear H);
            try (inversion H2; subst; clear H2);
            try (inversion H0; subst; clear H0);
            split; unfold satisfies; simpl;
            (repeat constructor); try assumption;
            unfold apply_symbol'; simpl;
            try constructor; try assumption;
            try (solve [inversion H7]);
            try (solve [inversion H3]).
    }
Qed.

Definition analyze_list_from_end {A : Type} (l : list A)
    : {l = nil} + { (exists (l' : list A) (x : A), l = l'++[x])}
.
Proof.
    induction l.
    {
        left. reflexivity.
    }
    {
        right.
        destruct IHl as [IHl|IHl].
        {
            subst. exists []. exists a. reflexivity.
        }
        {
            destruct IHl as [l' [x Hl']].
            subst.
            exists (a::l'). exists x. simpl. reflexivity.
        }
    }
Qed.

Lemma satisfies_top_bov_cons
    {Σ : StaticModel}
    (ρ : Valuation)
    (topSymbol topSymbol' : symbol)
    (states : list (TermOver builtin_value))
    (lds : list (TermOver BuiltinOrVar))
    :
    (
        length states = length lds /\
        Forall id (zip_with (satisfies ρ) states lds)
        /\ topSymbol = topSymbol'
    ) <->
    (
        satisfies ρ (fold_left helper (map uglify' states) (pt_operator topSymbol))
        (fold_left helper (map uglify' lds) (pt_operator topSymbol'))
    )
.
Proof.
    split.
    {
        intros H.
        destruct H as [Hlens H].
        revert lds Hlens H.
        induction states using rev_ind; intros lds Hlens H; simpl in *.
        {
            destruct lds; simpl in *.
            {
                destruct H as [_ H]. subst.
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
                rewrite (zip_with_app (satisfies ρ) _ _ _ _ Hlens') in H.
                destruct H as [H ?]. subst topSymbol'.
                apply Forall_app in H.
                destruct H as [H1 H2].
                simpl in H2. rewrite Forall_cons in H2. destruct H2 as [H2 _].
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
                        split>[|reflexivity].
                        apply H1.
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst.
                        unfold satisfies in H2; simpl in H2.
                        ltac1:(
                            replace (prettify' ao)
                            with (prettify (term_preterm ao))
                            in H2
                            by reflexivity
                        ).
                        ltac1:(
                            replace (prettify' ao0)
                            with (prettify (term_preterm ao0))
                            in H2
                            by reflexivity
                        ).
                        rewrite (cancel uglify' prettify) in H2.
                        rewrite (cancel uglify' prettify) in H2.
                        unfold satisfies in H2; simpl in H2.
                        inversion H2; subst; clear H2; assumption.
                    }
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2; subst; clear H2.
                    constructor.
                    { apply IHstates; (repeat split); try assumption; try reflexivity. }
                    { apply H4. }
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2.
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2; subst; clear H2.
                    constructor.
                    { apply IHstates; (repeat split); try assumption; try reflexivity. }
                    { assumption. }
                }
            }
        }
    }
    {
        intros H.
        revert lds H.
        induction states using rev_ind; intros lds pf.
        {
            destruct lds; simpl in *.
            {
                split>[reflexivity|].
                split.
                {
                    apply Forall_nil. exact I.
                }
                {
                    inversion pf. subst. reflexivity.
                }
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
                destruct e as [l' [x0 Hlds]].
                subst lds; simpl in *.
                rewrite map_app in pf.
                rewrite map_app in pf.
                simpl in pf.
                rewrite fold_left_app in pf.
                rewrite fold_left_app in pf.
                simpl in pf.
                (*
                unfold helper in pf.
                rewrite app_length in Hlens.
                rewrite app_length in Hlens.
                simpl in Hlens.
                assert (Hlens': length states = length l') by (ltac1:(lia)).
                
                rewrite (zip_with_app (satisfies ρ) _ _ _ _ Hlens').
                *)

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
                destruct IHstates as [IHlen [IHstates ?]].
                subst topSymbol'.
                do 2 (rewrite app_length).
                simpl.
                split>[ltac1:(lia)|].
                split.
                {                
                    rewrite (zip_with_app (satisfies ρ) _ _ _ _ IHlen).
                    rewrite Forall_app.
                    split.
                    {
                        apply IHstates.
                        
                    }
                    {
                        simpl.
                        rewrite Forall_cons.
                        split>[|apply Forall_nil; exact I].
                        destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                            simpl in *; inversion pf; subst; clear pf;
                            unfold satisfies; simpl; rewrite Hux; rewrite Hux0;
                            try constructor; try assumption.
                        inversion H5.
                    }
                }
                {
                    reflexivity.
                }
            }
        }
    }
Qed.

(* The proof if the same as for satisfies_top_bov_cons*)
Lemma satisfies_top_bov_cons_expr
    {Σ : StaticModel}
    (ρ : Valuation)
    (topSymbol topSymbol' : symbol)
    (states : list (TermOver builtin_value))
    (lds : list (TermOver Expression))
    :
    (
        length states = length lds /\
        Forall id (zip_with (satisfies ρ) states lds)
        /\ topSymbol = topSymbol'
    ) <->
    (
        satisfies ρ (fold_left helper (map uglify' states) (pt_operator topSymbol))
        (fold_left helper (map uglify' lds) (pt_operator topSymbol'))
    )
.
Proof.
    split.
    {
        intros H.
        destruct H as [Hlens H].
        revert lds Hlens H.
        induction states using rev_ind; intros lds Hlens H; simpl in *.
        {
            destruct lds; simpl in *.
            {
                destruct H as [_ H]. subst.
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
                rewrite (zip_with_app (satisfies ρ) _ _ _ _ Hlens') in H.
                destruct H as [H ?]. subst topSymbol'.
                apply Forall_app in H.
                destruct H as [H1 H2].
                simpl in H2. rewrite Forall_cons in H2. destruct H2 as [H2 _].
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
                        split>[|reflexivity].
                        apply H1.
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst.
                        unfold satisfies in H2; simpl in H2.
                        ltac1:(
                            replace (prettify' ao)
                            with (prettify (term_preterm ao))
                            in H2
                            by reflexivity
                        ).
                        ltac1:(
                            replace (prettify' ao0)
                            with (prettify (term_preterm ao0))
                            in H2
                            by reflexivity
                        ).
                        rewrite (cancel uglify' prettify) in H2.
                        rewrite (cancel uglify' prettify) in H2.
                        unfold satisfies in H2; simpl in H2.
                        inversion H2; subst; clear H2; assumption.
                    }
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2; subst; clear H2.
                    constructor.
                    { apply IHstates; (repeat split); try assumption; try reflexivity. }
                    { apply H4. }
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2.
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2; subst; clear H2.
                    constructor.
                    { apply IHstates; (repeat split); try assumption; try reflexivity. }
                    { assumption. }
                }
            }
        }
    }
    {
        intros H.
        revert lds H.
        induction states using rev_ind; intros lds pf.
        {
            destruct lds; simpl in *.
            {
                split>[reflexivity|].
                split.
                {
                    apply Forall_nil. exact I.
                }
                {
                    inversion pf. subst. reflexivity.
                }
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
                destruct e as [l' [x0 Hlds]].
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
                destruct IHstates as [IHlen [IHstates ?]].
                subst topSymbol'.
                do 2 (rewrite app_length).
                simpl.
                split>[ltac1:(lia)|].
                split.
                {                
                    rewrite (zip_with_app (satisfies ρ) _ _ _ _ IHlen).
                    rewrite Forall_app.
                    split.
                    {
                        apply IHstates.
                        
                    }
                    {
                        simpl.
                        rewrite Forall_cons.
                        split>[|apply Forall_nil; exact I].
                        destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                            simpl in *; inversion pf; subst; clear pf;
                            unfold satisfies; simpl; rewrite Hux; rewrite Hux0;
                            try constructor; try assumption.
                        inversion H5.
                    }
                }
                {
                    reflexivity.
                }
            }
        }
    }
Qed.

Lemma satisfies_top_expr
    {Σ : StaticModel}
    (ρ : Valuation)
    topSymbol
    (ctrl1 state1 : TermOver builtin_value) (lc ld : TermOver Expression)
    :
    (satisfies ρ ctrl1 lc /\ satisfies ρ state1 ld) <->
    satisfies ρ (apply_symbol' topSymbol [uglify' ctrl1; uglify' state1])
        (apply_symbol' topSymbol [uglify' lc; uglify' ld])
.
Proof.
    split.
    {
        intros [H1 H2].
        unfold apply_symbol'. simpl.
        destruct ctrl1,lc,state1,ld; simpl in *; (repeat constructor);
            inversion H1; inversion H2; subst; assumption.
    }
    {
        intros H.
        inversion H; subst; clear H.
        inversion pf; subst; clear pf;
        destruct ctrl1,lc,state1,ld;
            unfold to_PreTerm' in *;
            simpl in *;
            try (solve [inversion H1]);
            ltac1:(simplify_eq/=);
            try (inversion H; subst; clear H);
            try (inversion H2; subst; clear H2);
            try (inversion H0; subst; clear H0);
            split; unfold satisfies; simpl;
            (repeat constructor); try assumption;
            unfold apply_symbol'; simpl;
            try constructor; try assumption;
            try (solve [inversion H7]);
            try (solve [inversion H3]).
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
        apply (f_equal prettify) in H0.
        rewrite (cancel prettify uglify') in H0.
        subst.
        inversion H3; subst; clear H3.
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
        apply (f_equal prettify) in H0.
        rewrite (cancel prettify uglify') in H0.
        subst.
        inversion H3; subst; clear H3.
        assumption.
    }
Qed.


Lemma subst_notin
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of_to_l2r φ ->
    TermOverBoV_subst φ h ψ = φ
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        {
            intros _. reflexivity.
        }
        {
            destruct (decide (h = x)); simpl.
            {
                subst. intros HContra. ltac1:(exfalso). apply HContra.
                constructor.
            }
            {
                intros _. reflexivity.
            }
        }
    }
    {
        intros H2.
        f_equal.
        induction l; simpl.
        {
            reflexivity.
        }
        {
            apply Forall_cons in H.
            destruct H as [HH1 HH2].
            simpl in *.
            specialize (IHl HH2).
            rewrite elem_of_app in H2.
            apply Decidable.not_or in H2.
            destruct H2 as [H21 H22].
            specialize (IHl H22). clear H22.
            specialize (HH1 H21).
            rewrite HH1.
            rewrite IHl.
            reflexivity.
        }
    }
Qed.


Lemma weird_lemma
    {Σ : StaticModel}
    l s:
(fix go (pt : PreTerm' symbol builtin_value) :
    list (TermOver builtin_value) :=
  match pt with
| pt_operator _ => []
| pt_app_operand x y => go x ++ [t_over y]
| pt_app_ao x y => go x ++ [prettify' y]
end)
  (fold_left helper (map uglify' l) (pt_operator s)) =
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
    exists (lγ : list (TermOver builtin_value)),
        γ = (t_term s lγ) /\
        length l = length lγ /\
        Forall (fun p => p) (zip_with (satisfies ρ) lγ l)
.
Proof.
    revert γ.
    induction l using rev_ind; intros γ.
    {
        intros H. exists []. inversion H; subst; clear H.
        unfold to_PreTerm' in pf. simpl in pf.
        inversion pf. subst; clear pf.
        rewrite <- (cancel prettify uglify' γ).
        rewrite <- H2.
        simpl.
        repeat constructor.
    }
    {
        intros H.
        inversion H; subst; clear H.
        unfold to_PreTerm' in pf. simpl in pf.
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
                    apply H3.
                }

                destruct IHl as [lγ [IH1 [IH2 IH3]]].
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
                simpl in IH1. unfold apply_symbol' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                split.
                {
                    unfold to_PreTerm'.
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
                simpl.
                split.
                {
                    rewrite IH2. reflexivity.
                }
                rewrite zip_with_app.
                rewrite Forall_app.
                split.
                {
                    apply IH3.
                }
                constructor.
                {
                    inversion H5.
                }
                {
                    apply Forall_nil. exact I.
                }
                {
                    symmetry. exact IH2.
                }
            }
            {
                eexists.
                split.
                {
                    simpl.
                    f_equal.
                    clear -H3.

                    revert xy1 H3.
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
                                apply IHl.
                                apply H4.
                            }
                            {
                                apply IHl.
                                apply H4.
                            }
                        }
                        {
                            apply (f_equal prettify) in H.
                            rewrite (cancel prettify uglify') in H.
                            subst x.
                            inversion H3; subst; clear H3; simpl in *.
                            {
                                apply IHl.
                                apply H4.
                            }
                            {
                                apply IHl.
                                apply H4.
                            }
                        }
                    }
                }
                simpl.
                fold (@helper Σ (@BuiltinOrVar Σ)) in H3.
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
                                unfold satisfies in H6; simpl in H6.
                                inversion H6.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { apply H4. }
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
                split.
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {
                    rewrite zip_with_app.
                    rewrite Forall_app.
                    split.
                    {
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' Σ).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm'. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            apply H3.
                        }
                        destruct IHl as [lγ [Hlγ1 [Hlγ2 Hlγ3]]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        clear -Hlγ3.
                        rewrite Forall_forall.
                        rewrite Forall_forall in Hlγ3.
                        intros x Hin.
                        rewrite elem_of_lookup_zip_with in Hin.
                        destruct Hin as [i [a [b [Hab1 [Hab2 Hab3]]]]].
                        specialize (Hlγ3 x).
                        subst x.
                        apply Hlγ3. clear Hlγ3.
                        rewrite elem_of_lookup_zip_with.
                        exists i. exists a. exists b.
                        split>[reflexivity|].
                        split>[|exact Hab3].
                        rewrite <- Hab2. clear Hab2.
                        clear.
                        assert (Htmp := @cancel_prettify_uglify Σ builtin_value).
                        unfold Cancel in Htmp. simpl in Htmp.
                        specialize (Htmp (t_term s lγ)).
                        simpl in Htmp.
                        unfold prettify' in Htmp.
                        remember ((to_PreTerm' s (map uglify' lγ))) as tpt.
                        destruct tpt; simpl in *.
                        {
                            inversion Htmp. reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                    }
                    {
                        constructor.
                        {
                            unfold satisfies.
                            simpl.
                            
                            ltac1:(
                                replace (prettify' xy2)
                                with (prettify (term_preterm xy2))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).

                            ltac1:(
                                replace (prettify' ao)
                                with (prettify (term_preterm ao))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            constructor.
                            apply H5.
                        }
                        {
                            apply Forall_nil. exact I.
                        }
                    }
                    {
                        symmetry. apply Hl.
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
                    apply H3.
                }

                destruct IHl as [lγ [IH1 [IH2 IH3]]].
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
                simpl in IH1. unfold apply_symbol' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                split.
                {
                    unfold to_PreTerm'.
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
                simpl.
                split.
                {
                    rewrite IH2. reflexivity.
                }
                rewrite zip_with_app.
                rewrite Forall_app.
                split.
                {
                    apply IH3.
                }
                constructor.
                {
                    constructor.
                    apply H5.
                }
                {
                    apply Forall_nil. exact I.
                }
                {
                    symmetry. exact IH2.
                }
            }
            {
                eexists.
                split.
                {
                    simpl.
                    f_equal.
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
                fold (@helper Σ (@BuiltinOrVar Σ)) in H3.
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
                                unfold satisfies in H6; simpl in H6.
                                inversion H6.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { apply H4. }
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
                split.
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {
                    rewrite zip_with_app.
                    rewrite Forall_app.
                    split.
                    {
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' Σ).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm'. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            apply H3.
                        }
                        destruct IHl as [lγ [Hlγ1 [Hlγ2 Hlγ3]]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        clear -Hlγ3.
                        rewrite Forall_forall.
                        rewrite Forall_forall in Hlγ3.
                        intros x Hin.
                        rewrite elem_of_lookup_zip_with in Hin.
                        destruct Hin as [i [a [b [Hab1 [Hab2 Hab3]]]]].
                        specialize (Hlγ3 x).
                        subst x.
                        apply Hlγ3. clear Hlγ3.
                        rewrite elem_of_lookup_zip_with.
                        exists i. exists a. exists b.
                        split>[reflexivity|].
                        split>[|exact Hab3].
                        rewrite <- Hab2. clear Hab2.
                        clear.
                        assert (Htmp := @cancel_prettify_uglify Σ builtin_value).
                        unfold Cancel in Htmp. simpl in Htmp.
                        specialize (Htmp (t_term s lγ)).
                        simpl in Htmp.
                        unfold prettify' in Htmp.
                        remember ((to_PreTerm' s (map uglify' lγ))) as tpt.
                        destruct tpt; simpl in *.
                        {
                            inversion Htmp. reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                    }
                    {
                        constructor.
                        {
                            unfold satisfies.
                            simpl.
                            
                            ltac1:(
                                replace (prettify' xy2)
                                with (prettify (term_preterm xy2))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            constructor.
                            apply H5.
                        }
                        {
                            apply Forall_nil. exact I.
                        }
                    }
                    {
                        symmetry. apply Hl.
                    }
                }   
            }
        }
    }
Qed.

Lemma satisfies_term_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (s : symbol)
    (l : list (TermOver BuiltinOrVar))
    :
    satisfies ρ γ (t_term s l) ->
    exists (lγ : list (TermOver builtin_value)),
        γ = (t_term s lγ) /\
        length l = length lγ /\
        Forall (fun p => p) (zip_with (satisfies ρ) lγ l)
.
Proof.
    revert γ.
    induction l using rev_ind; intros γ.
    {
        intros H. exists []. inversion H; subst; clear H.
        unfold to_PreTerm' in pf. simpl in pf.
        inversion pf. subst; clear pf.
        rewrite <- (cancel prettify uglify' γ).
        rewrite <- H2.
        simpl.
        repeat constructor.
    }
    {
        intros H.
        inversion H; subst; clear H.
        unfold to_PreTerm' in pf. simpl in pf.
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
                    apply H3.
                }

                destruct IHl as [lγ [IH1 [IH2 IH3]]].
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
                simpl in IH1. unfold apply_symbol' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                split.
                {
                    unfold to_PreTerm'.
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
                simpl.
                split.
                {
                    rewrite IH2. reflexivity.
                }
                rewrite zip_with_app.
                rewrite Forall_app.
                split.
                {
                    apply IH3.
                }
                constructor.
                {
                    inversion H5.
                }
                {
                    apply Forall_nil. exact I.
                }
                {
                    symmetry. exact IH2.
                }
            }
            {
                eexists.
                split.
                {
                    simpl.
                    f_equal.
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
                fold (@helper Σ (@BuiltinOrVar Σ)) in H3.
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
                        unfold helper at 1 in H3. simpl in H3.
                        destruct (uglify' x) eqn:Hux.
                        {
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                inversion H3; subst; clear H3.
                                unfold satisfies in H6; simpl in H6.
                                inversion H6.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { apply H4. }
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
                split.
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {
                    rewrite zip_with_app.
                    rewrite Forall_app.
                    split.
                    {
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' Σ).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm'. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            apply H3.
                        }
                        destruct IHl as [lγ [Hlγ1 [Hlγ2 Hlγ3]]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        clear -Hlγ3.
                        rewrite Forall_forall.
                        rewrite Forall_forall in Hlγ3.
                        intros x Hin.
                        rewrite elem_of_lookup_zip_with in Hin.
                        destruct Hin as [i [a [b [Hab1 [Hab2 Hab3]]]]].
                        specialize (Hlγ3 x).
                        subst x.
                        apply Hlγ3. clear Hlγ3.
                        rewrite elem_of_lookup_zip_with.
                        exists i. exists a. exists b.
                        split>[reflexivity|].
                        split>[|exact Hab3].
                        rewrite <- Hab2. clear Hab2.
                        clear.
                        assert (Htmp := @cancel_prettify_uglify Σ builtin_value).
                        unfold Cancel in Htmp. simpl in Htmp.
                        specialize (Htmp (t_term s lγ)).
                        simpl in Htmp.
                        unfold prettify' in Htmp.
                        remember ((to_PreTerm' s (map uglify' lγ))) as tpt.
                        destruct tpt; simpl in *.
                        {
                            inversion Htmp. reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                    }
                    {
                        constructor.
                        {
                            unfold satisfies.
                            simpl.
                            
                            ltac1:(
                                replace (prettify' xy2)
                                with (prettify (term_preterm xy2))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).

                            ltac1:(
                                replace (prettify' ao)
                                with (prettify (term_preterm ao))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            constructor.
                            apply H5.
                        }
                        {
                            apply Forall_nil. exact I.
                        }
                    }
                    {
                        symmetry. apply Hl.
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
                    apply H3.
                }

                destruct IHl as [lγ [IH1 [IH2 IH3]]].
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
                simpl in IH1. unfold apply_symbol' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                split.
                {
                    unfold to_PreTerm'.
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
                simpl.
                split.
                {
                    rewrite IH2. reflexivity.
                }
                rewrite zip_with_app.
                rewrite Forall_app.
                split.
                {
                    apply IH3.
                }
                constructor.
                {
                    constructor.
                    apply H5.
                }
                {
                    apply Forall_nil. exact I.
                }
                {
                    symmetry. exact IH2.
                }
            }
            {
                eexists.
                split.
                {
                    simpl.
                    f_equal.
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
                fold (@helper Σ (@BuiltinOrVar Σ)) in H3.
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
                        unfold helper at 1 in H3. simpl in H3.
                        destruct (uglify' x) eqn:Hux.
                        {
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                inversion H3; subst; clear H3.
                                unfold satisfies in H6; simpl in H6.
                                inversion H6.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { apply H4. }
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
                split.
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {
                    rewrite zip_with_app.
                    rewrite Forall_app.
                    split.
                    {
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' Σ).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm'. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            apply H3.
                        }
                        destruct IHl as [lγ [Hlγ1 [Hlγ2 Hlγ3]]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        clear -Hlγ3.
                        rewrite Forall_forall.
                        rewrite Forall_forall in Hlγ3.
                        intros x Hin.
                        rewrite elem_of_lookup_zip_with in Hin.
                        destruct Hin as [i [a [b [Hab1 [Hab2 Hab3]]]]].
                        specialize (Hlγ3 x).
                        subst x.
                        apply Hlγ3. clear Hlγ3.
                        rewrite elem_of_lookup_zip_with.
                        exists i. exists a. exists b.
                        split>[reflexivity|].
                        split>[|exact Hab3].
                        rewrite <- Hab2. clear Hab2.
                        clear.
                        assert (Htmp := @cancel_prettify_uglify Σ builtin_value).
                        unfold Cancel in Htmp. simpl in Htmp.
                        specialize (Htmp (t_term s lγ)).
                        simpl in Htmp.
                        unfold prettify' in Htmp.
                        remember ((to_PreTerm' s (map uglify' lγ))) as tpt.
                        destruct tpt; simpl in *.
                        {
                            inversion Htmp. reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                    }
                    {
                        constructor.
                        {
                            unfold satisfies.
                            simpl.
                            
                            ltac1:(
                                replace (prettify' xy2)
                                with (prettify (term_preterm xy2))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            constructor.
                            apply H5.
                        }
                        {
                            apply Forall_nil. exact I.
                        }
                    }
                    {
                        symmetry. apply Hl.
                    }
                }   
            }
        }
    }
Qed.

Lemma satisfies_PreTerm'_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : PreTerm' symbol builtin_value)
    (φ : PreTerm' symbol BuiltinOrVar)
:
    (forall (x : variable), x ∈ vars_of φ -> ρ1!!x = ρ2!!x) ->
    (
    satisfies ρ1 g φ
    <->
    satisfies ρ2 g φ
    )
.
Proof.
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ1 g φ)).
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ2 g φ)).
    revert φ.
    induction g; intros φ Hvars; destruct φ;
        unfold matchesb in *; unfold vars_of in *;
        simpl in *;
        try ltac1:(tauto).
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        destruct b0; simpl.
        {
            ltac1:(tauto).
        }
        rewrite Hvars.
        { reflexivity. }
        {
            simpl. unfold vars_of; simpl.
            ltac1:(set_solver).
        }
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        ltac1:(tauto).
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg1).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        destruct b; simpl.
        {
            ltac1:(tauto).
        }
        rewrite Hvars.
        { reflexivity. }
        {
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg1).
        { ltac1:(set_solver). }
        ltac1:(rewrite IHg2).
        { ltac1:(set_solver). }
        reflexivity.
    }
Qed.

Lemma satisfies_Term'_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : Term' symbol builtin_value)
    (φ : Term' symbol BuiltinOrVar)
:
    (forall (x : variable), x ∈ vars_of φ -> ρ1!!x = ρ2!!x) ->
    (
    satisfies ρ1 g φ
    <->
    satisfies ρ2 g φ
    )
.
Proof.
    intros Hvars.
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ1 g φ)).
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ2 g φ)).
    destruct g, φ; unfold matchesb; simpl.
    {
        rewrite <- (reflect_iff _ _ (matchesb_satisfies ρ1 ao ao0)).
        rewrite <- (reflect_iff _ _ (matchesb_satisfies ρ2 ao ao0)).
        apply satisfies_PreTerm'_vars_of.
        apply Hvars.
    }
    {
        unfold matchesb; simpl.
        destruct operand; simpl.
        { ltac1:(tauto). }
        {
            rewrite Hvars.
            { reflexivity. }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                rewrite elem_of_singleton.
                reflexivity.
            }
        }
    }
    {
        ltac1:(tauto).
    }
    {
        unfold matchesb; simpl.
        destruct operand0; simpl.
        { ltac1:(tauto). }
        {
            rewrite Hvars.
            { reflexivity. }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                rewrite elem_of_singleton.
                reflexivity.
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
        unfold to_PreTerm'; simpl.
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

Program Fixpoint pfmap
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    : list B
:=
match l with
| nil => nil
| x::xs => (f x _)::(pfmap xs (fun (x' : A) (pf' : x' ∈ xs) => f x' _))
end
.
Next Obligation.
    intros. subst. rewrite elem_of_cons. left. reflexivity.
Defined.
Next Obligation.
    intros. subst. rewrite elem_of_cons. right. exact pf'.
Defined.
Fail Next Obligation.


Program Fixpoint pflookup
    {A : Type}
    (l : list A)
    (i : nat)
    (pflt : i < length l)
    : { x : A | x ∈ l}
:=
match l with
| [] => _
| x::xs =>
    match i with
    | 0 => (exist _ x _ )
    | S i' =>
        let tmp := pflookup xs i' _ in
        let x' := proj1_sig tmp in
        let pf := proj2_sig tmp in
        (exist _ x' _)
    end
end.
Next Obligation.
    abstract(ltac1:(lia)).
Qed.
Next Obligation.
    abstract(left).
Qed.
Next Obligation.
    abstract(ltac1:(lia)).
Qed.
Next Obligation.
    abstract(right; assumption).
Defined.
Fail Next Obligation.


Lemma pflookup_spec
    {A : Type}
    (l : list A)
    (i : nat)
    (pflt : i < length l)
    :
    Some (proj1_sig (pflookup l i pflt)) = l !! i
.
Proof.
    revert i pflt.
    induction l; intros i pflt.
    {
        simpl in pflt. ltac1:(lia).
    }
    {
        destruct i;
            simpl in *.
        {
            reflexivity.
        }
        {
            apply IHl.
        }
    }
Qed.

Lemma length_pfmap
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    :
    length (pfmap l f) = length l
.
Proof.
    induction l; simpl.
    { reflexivity. }
    {
        rewrite IHl. reflexivity.
    }
Qed.

Lemma pfmap_lookup_Some_lt
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    (i : nat)
    (y : B)
    :
    pfmap l f !! i = Some y ->
    i < length l
.
Proof.
    revert i f.
    induction l; intros i f H.
    {
        simpl in H.
        rewrite lookup_nil in H.
        inversion H.
    }
    {
        simpl in *.
        destruct i.
        {
            ltac1:(lia).
        }
        {
            simpl in H.
            specialize (IHl i _ H).
            ltac1:(lia).
        }
    }
Qed.

Arguments pfmap_lookup_Some_lt {A B}%type_scope {l}%list_scope {f}%function_scope {i}%nat_scope {y} _.

Lemma pfmap_lookup_Some_1
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    (i : nat)
    (y : B)
    (pf : pfmap l f !! i = Some y)
    :
    let pflt : i < length l := pfmap_lookup_Some_lt pf in
    y = (let xpf := (pflookup l i pflt) in (f (proj1_sig xpf) (proj2_sig xpf) ))
.
Proof.
    simpl.
    revert i y f pf.
    induction l; intros i y f pf.
    {
        simpl in pf. ltac1:(exfalso). rewrite lookup_nil in pf. inversion pf.
    }
    {
        destruct i.
        {
            simpl in *. inversion pf; subst.
            f_equal.
            apply proof_irrelevance.
        }
        {
            simpl in *.
            (* specialize (IHl i y). *)
            ltac1:(unshelve(erewrite IHl at 1))>[()|()|apply pf|].
            simpl.
            assert (Htmp0: ((@pfmap_lookup_Some_lt A _ l
          (λ (x' : A) (pf' : x' ∈ l),
             f x'
               (@flip2 Prop iff (λ x y0 : Prop, impl y0 x) iff_flip_impl_subrelation 
                  (x' ∈ a :: l) (x' = a ∨ x' ∈ l) (@elem_of_cons A l x' a)
                  (@or_intror (x' = a) (x' ∈ l) pf'))) i y pf)) = ((pflookup_obligation_3 A (a :: l) (S i) (@pfmap_lookup_Some_lt A _ (a :: l) f (S i) y pf) a l
          erefl i erefl))).
            {
                apply proof_irrelevance.
            }
            rewrite Htmp0.
            apply f_equal.
            apply proof_irrelevance.
        }
    }
Qed.


Fixpoint factor_by_subst
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation)
    (h : variable)
    (γ : TermOver builtin_value)
    (φ ψ : TermOver BuiltinOrVar)
    : ((TermOver builtin_value)*(TermOver builtin_value))
:=
match sz with
| 0 => (γ, γ)
| S sz' =>
    if matchesb ρ (uglify' γ) (uglify' ψ) then (γ, γ) else
    match γ,φ with
    | t_over _, t_over _ => (* do not care*) (γ, γ)
    | t_term _ _, t_over _ => (* do not care*) (γ, γ)
    | t_over _, t_term _ _ => (* do not care*) (γ, γ)
    | t_term _ lγ, t_term s lφ =>
        match list_find (fun φi => h ∈ vars_of_to_l2r φi) lφ with
        | None => (* do not care*) (γ, γ)
        | Some (i, φi) => 
            match lγ !! i with 
            | None => (* do not care*) (γ, γ)
            | Some γi =>
                let xy := factor_by_subst sz' ρ h γi φi ψ in
                (t_term s (<[i := xy.1]>lγ), xy.2)

            end
        end
    end
end
.

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
    {Σ : StaticModel}
    {T : Type}
    (s s' : symbol)
    (l : list (Term' symbol T)):
    pt_operator s' = to_PreTerm' s l ->
    s' = s /\ l = []
.
Proof.
    revert s s'.
    destruct l using rev_ind; intros s s' H1.
    {
        inversion H1. subst. split; reflexivity.
    }
    {
        unfold to_PreTerm' in H1.
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
    induction γ; constructor.
    {
        constructor.
    }
    {
        fold (@uglify' Σ).
        fold (@TermOver_map Σ).
        unfold to_PreTerm'.
        rewrite <- satisfies_top_bov_cons.
        (repeat split).
        {
            rewrite map_length. reflexivity.
        }
        induction l; simpl.
        { apply Forall_nil. exact I. }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2).
            rewrite Forall_cons.
            split.
            {
                apply H1.
            }
            apply IHl.
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
    {Σ : StaticModel}
    {T : Type}
    (s1 s2 : symbol)
    (l1 l2 : list (Term' symbol T))
    :
    to_PreTerm' s1 l1 = to_PreTerm' s2 l2
    -> s1 = s2 /\ l1 = l2
.
Proof.
    revert l2.
    induction l1 using rev_ind; intros l2 HH; destruct l2 using rev_ind.
    {
        inversion HH. subst. repeat split.
    }
    {
        unfold to_PreTerm' in *.
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
        unfold to_PreTerm' in *.
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
        unfold to_PreTerm' in *.
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
    Forall id (zip_with (satisfies ρ) γ1 l) ->
    Forall id (zip_with (satisfies ρ) γ2 l) ->
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
        rewrite Forall_forall.
        rewrite Forall_forall in H3.
        intros H4.
        ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
        ltac1:(setoid_rewrite elem_of_lookup_zip_with in H4).
        apply list_eq.
        intros i.
        destruct
            (γ1 !! i) eqn:Hγ1i,
            (γ2 !! i) eqn:Hγ2i.
        {
            destruct (l !! i) eqn:Hli.
            {
                specialize (H3 (satisfies ρ t t1)).
                ltac1:(ospecialize (H3 _)).
                {
                    exists i,t,t1.
                    split>[reflexivity|].
                    split;assumption.
                }
                specialize (H4 (satisfies ρ t0 t1)).
                ltac1:(ospecialize (H4 _)).
                {
                    exists i,t0,t1.
                    split>[reflexivity|].
                    split;assumption.
                }
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
                unfold to_PreTerm' in H3.
                apply satisfies_builtin_inv in H3.
                inversion H3.
            }
            {
                inversion pf; subst; clear pf.
                inversion H3; subst; clear H3.
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
                unfold to_PreTerm' in H4.
                apply satisfies_builtin_inv in H4.
                inversion H4.
            }
            {
                inversion pf; subst; clear pf.
                inversion H4; subst; clear H4.
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
                apply satisfies_builtin_inv in H3.
                inversion H3.
            }
            {
                inversion H4; subst; clear H4.
                inversion H3; subst; clear H3.
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
            unfold to_PreTerm' in pf.
            unfold to_PreTerm' in pf0.
            rewrite <- satisfies_top_bov_cons in pf.
            rewrite <- satisfies_top_bov_cons in pf0.
            destruct pf as [H1 H2].
            destruct pf0 as [H3 H4].
            assert (IH1 := forall_satisfies_inv' Σ sz ρ lx ly lz).
            destruct H2 as [H21 H22].
            destruct H4 as [H41 H42].
            simpl in Hsz.
            specialize (IH1 ltac:(lia)).
            subst.
            specialize (IH1 H1 H3 H21 H41).
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
    Forall id (zip_with (satisfies ρ) γ1 l) ->
    Forall id (zip_with (satisfies ρ) γ2 l) ->
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
                apply (f_equal prettify) in H.
                rewrite (cancel prettify uglify') in H.
                subst t.
                simpl in *.
                inversion H2; subst; clear H2.
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
        apply satisfies_term_inv in Hsat.
        destruct Hsat as [lγ [H1 [H2 H3]]].
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
            rewrite Forall_forall in H3.
            ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
            destruct (lγ !! i) eqn:Hlγi.
            {
                specialize (H3 (satisfies ρ t0 t)).            
                ltac1:(ospecialize (H3 _)).
                {
                    exists i, t0, t.
                    split>[reflexivity|].
                    split;assumption.
                }
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
    ay cz lz cx lx
    :
    vars_of (uglify' (t_over ay)) = vars_of (uglify' (t_term cz lz)) ->
    satisfies ρ (t_term cx lx) (t_over ay) ->
    satisfies ρ (t_term cx lx) (t_term cz lz) ->
    False
.
Proof.
    intros Hvars H1 H2.
        inversion H1; subst; clear H1.
        inversion H2; subst; clear H2.
        unfold to_PreTerm' in pf.
        rewrite <- satisfies_top_bov_cons in pf.
        destruct pf as [pf1 [pf2 pf3]].
        subst cz.
        destruct ay.
        {
            inversion H4; subst; clear H4.
        }
        {
            
            ltac1:(exfalso).
            simpl in Hvars.
            assert (Htmp1 := satisfies_in_size ρ x).
            unfold vars_of in Hvars; simpl in Hvars.
            unfold vars_of in Hvars; simpl in Hvars.

            inversion H4; subst; clear H4.
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
                    unfold to_PreTerm' in Hvars.
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
            destruct (lz !! i) eqn:Hlzi.
            {
                inversion Hi; subst; clear Hi.
                rewrite Forall_forall in pf2.
                ltac1:(setoid_rewrite elem_of_lookup_zip_with in pf2).

                destruct (lx !! i) eqn:Hlxi.
                {
                    specialize (pf2 (satisfies ρ t0 t)).
                    ltac1:(ospecialize (pf2 _)).
                    {
                        exists i.
                        exists t0.
                        exists t.
                        split>[reflexivity|].
                        split; assumption.
                    }
                    specialize (Htmp1 t0 (t_term cx lx)).
                    specialize (Htmp1 t H2z H0 pf2).
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
    ay cz lz cx lx
    :
    vars_of_to_l2r ((t_over ay)) = vars_of_to_l2r ((t_term cz lz)) ->
    satisfies ρ (t_term cx lx) (t_over ay) ->
    satisfies ρ (t_term cx lx) (t_term cz lz) ->
    False
.
Proof.
    intros.
    eapply double_satisfies_contradiction>[|apply H0|apply H1].
    apply set_eq.
    intros x.
    rewrite <- vars_of_uglify.
    rewrite <- vars_of_uglify.
    rewrite H.
    ltac1:(tauto).
Qed.

Lemma vars_of_apply_symbol
    {Σ : StaticModel}
    (s : symbol)
    (l : list (Term' symbol BuiltinOrVar))
    :
    vars_of (apply_symbol' s l) = union_list (fmap vars_of l)
.
Proof.
    induction l using rev_ind.
    {
        simpl. reflexivity.
    }
    {
        rewrite fmap_app.
        rewrite union_list_app_L.
        unfold apply_symbol' in *; simpl in *.
        unfold vars_of in *; simpl in *.
        unfold to_PreTerm' in *.
        rewrite fold_left_app.
        simpl.
        rewrite <- IHl. clear IHl.
        unfold helper.
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
                inversion H4.
            }
            {
                inversion H1; subst; clear H1.
                inversion H4; subst; clear H4.
                simpl.
                unfold delta_in_val. simpl.
                unfold size_of_var_in_val.
                rewrite H1. simpl.
                apply f_equal.
                ltac1:(replace ((prettify' (to_PreTerm' s (map uglify' l))))
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
            apply satisfies_term_inv in H1.
            destruct H1 as [lγ [H2 [H3 H4]]].
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
                    rewrite Forall_cons in H4.
                    destruct H4 as [H4 H4'].
                    specialize (IHlγ H4').
                    simpl in *.
                    specialize (H _ H4).
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
    apply satisfies_term_inv in H2.
    destruct H2 as [lγ [h4 [H5 H6]]].
    subst γ2. simpl in *.
    rewrite sum_list_with_app. simpl.
    rewrite app_length in H5. simpl in H5.

    destruct (lγ !! (length l1)) eqn:Hγ.
    {
        apply take_drop_middle in Hγ.
        rewrite <- Hγ in H6.
        rewrite zip_with_app in H6.
        {
            rewrite Forall_app in H6.
            simpl in H6.
            rewrite Forall_cons in H6.
            destruct H6 as [H6 [H7 H8]].
            assert (t = γ1).
            {
                eapply satisfies_inv.
                {
                    apply H7.
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
                        simpl in H6.
                        rewrite Forall_cons in H6.
                        destruct H6 as [Hsat H6].
                        apply concrete_is_larger_than_symbolic in Hsat.
                        specialize (IHl1 _ H6).
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
                clear -Hlen H8.
                revert l2 Hlen H8.
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
                        rewrite Forall_cons in H8.
                        destruct H8 as [H1 H2].
                        apply concrete_is_larger_than_symbolic in H1.
                        specialize (IHlγ' l2 ltac:(lia) H2).
                        ltac1:(lia).
                    }
                }
            }
            
            ltac1:(lia).
        }
        {
            rewrite take_length.
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
        unfold apply_symbol' in HContra; simpl in HContra.
        unfold to_PreTerm' in HContra; simpl in HContra.
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

Lemma sum_list_with_compose {A B : Type} (g : A -> B) (f : B -> nat)
    :
    sum_list_with (f ∘ g) = (sum_list_with f) ∘ (fmap g)
.
Proof.
    apply functional_extensionality.
    intros l.
    induction l; simpl.
    {
        reflexivity.
    }
    {
        rewrite IHl. unfold compose. reflexivity.
    }
Qed.

Lemma sum_list_with_S (l : list nat):
    sum_list_with S l = sum_list l + length l
.
Proof.
    induction l; simpl.
    {
        reflexivity.
    }
    {
        rewrite IHl.
        ltac1:(lia).
    }
Qed.

Lemma sum_list_fmap
    {T: Type}
    (f : T -> nat)
    (l : list T)
    :
    sum_list ( f <$> l) = sum_list_with f l
.
Proof.
    induction l; simpl.
    { reflexivity. }
    {
        unfold fmap in IHl.
        rewrite IHl.
        reflexivity.
    }
Qed.

Lemma sum_list_with_sum_list_with
    {T: Type}
    (f : T -> nat)
    (l : list (list T))
    :
    sum_list_with (sum_list_with f) l = sum_list_with f (concat l)
.
Proof.
    induction l; simpl.
    { reflexivity. }
    {
        rewrite IHl.
        rewrite sum_list_with_app.
        reflexivity.
    }
Qed.

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
                    apply (f_equal prettify) in H.
                    rewrite (cancel prettify uglify') in H.
                    subst. simpl in *.
                    inversion H2; subst; clear H2.
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
        apply satisfies_term_inv in Hsat2.
        destruct Hsat2 as [lγ [H1 [H2 H3]]].
        subst. simpl in *.
        rewrite map_length in H2.

        apply satisfies_term_inv in Hsat1.
        destruct Hsat1 as [l'γ [H4 [H5 H6]]].
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
                rewrite zip_with_app in H3.
                {
                    rewrite Forall_app in H3.
                    destruct H3 as [H31 H32].
                    simpl in H32.
                    rewrite Forall_cons in H32.
                    destruct H32 as [H32 H33].
                    rewrite Forall_forall in H31.
                    ltac1:(setoid_rewrite elem_of_lookup_zip_with in H31).


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
                                    apply H31.
                                    exists i0.
                                    exists x1,x2.
                                    split>[reflexivity|].
                                    split>[assumption|].
                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                    rewrite list_lookup_fmap.
                                    rewrite lookup_take.
                                    {
                                        rewrite H'li0.
                                        simpl.
                                        rewrite subst_notin.
                                        {
                                            reflexivity.
                                        }
                                        {
                                            apply Hhx2.
                                        }
                                    }
                                    {
                                        apply lookup_lt_Some in HH1.
                                        rewrite take_length in HH1.
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
                                    rewrite Forall_forall in H33.
                                    apply H33.
                                    rewrite elem_of_lookup_zip_with.
                                    exists i0.
                                    exists x1,x2.
                                    split>[reflexivity|].
                                    split>[assumption|].
                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
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
                                        apply Hhx2.
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
                    rewrite zip_with_app in H6.
                    {
                        simpl in H6.
                        rewrite Forall_app in H6.
                        rewrite Forall_cons in H6.
                        destruct H6 as [H61 [H62 H63]].

                        specialize (IH2 t0 t).

                        remember ((sum_list_with (S ∘ TermOver_size) (take i lγ))) as Y1.
                        remember ((sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (take i l)))) as Y1'.
                        remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) lγ) ) as Y2.
                        remember ( sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (drop (S i) l)) ) as Y2'.
                        remember (sum_list_with (S ∘ TermOver_size) (take i l)) as Y3.
                        remember (sum_list_with (S ∘ TermOver_size) (take i l'γ)) as Y3'.
                        remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) l) ) as Y4.
                        remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) l'γ) ) as Y4'.

                        assert (H32' := H32).
                        assert (H62' := H62).
                        apply concrete_is_larger_than_symbolic in H32'.
                        apply concrete_is_larger_than_symbolic in H62'.

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
                        specialize (IH2 ltac:(assumption) ltac:(assumption)).


                        apply concrete_is_larger_than_symbolic in H32.
                        apply concrete_is_larger_than_symbolic in H62.
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
                        rewrite H32'.
                        remember (sum_list_with (size_of_var_in_val ρ)) as F.
                        remember ((vars_of_to_l2r (TermOverBoV_subst x0 h ψ))) as VS.


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
                        (* Search drop lγ. *)
                        clear Hlγi H0' H33.

                        assert(HeqB1': sum_list (TermOver_size <$> take i l) + sum_list_with (λ ψ0 : TermOver BuiltinOrVar, sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0)) (take i l) = sum_list (map TermOver_size (take i lγ))).
                        {
                            ltac1:(lia).
                        }
                        clear HeqB1. clear H31.
                        (* Search TermOver_size t0. *)
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
        specialize (H ltac:(lia)).
        rewrite H.
        assert (Htmp1 := TermOver_size_not_zero x0).
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

(* TODO we need a lemma like this that does not assume h ∉ ρ.
   Instead of the uses of that assumption for satisfies_ext,
   we have to use the `vars_of` lemmas about `satisfies`,
   and it should still work.
*)
Lemma factor_by_subst_correct'
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation)
    (h : variable)
    (γ : TermOver builtin_value)
    (φ ψ : TermOver BuiltinOrVar)
    : sz >= TermOver_size γ ->
    h ∉ vars_of ρ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    ~ (h ∈ vars_of_to_l2r ψ) ->
    satisfies ρ γ (TermOverBoV_subst φ h ψ) ->
    let xy := factor_by_subst sz ρ h γ φ ψ in
    satisfies ρ xy.2 ψ /\
    satisfies (<[h := (uglify' xy.2)]>ρ) xy.1 φ
.
Proof.
    revert γ φ.
    induction sz; intros γ φ Hsz.
    {
        destruct γ; simpl in Hsz; ltac1:(lia).
    }
    {
        intros Hnotinρ Hlf Hnotinψ Hsat.
        unfold factor_by_subst. fold (@factor_by_subst Σ).
        simpl.
        destruct (matchesb ρ (uglify' γ) (uglify' ψ)) eqn:Heqmb.
        {
            simpl.
            split.
            {
                apply matchesb_implies_satisfies in Heqmb.
                unfold satisfies; simpl.
                apply Heqmb.
            }
            {
                apply matchesb_implies_satisfies in Heqmb.
                assert (Heqmb': satisfies ρ γ ψ).
                {
                    unfold satisfies; simpl.
                    apply Heqmb.
                }

                assert (Htmp2 := TermOver_size_not_zero ψ).
                assert (Htmp3 := TermOver_size_not_zero φ).
                assert (Hsat' := Hsat).
                apply concrete_is_larger_than_symbolic in Hsat'.
                apply concrete_is_larger_than_symbolic in Heqmb'.

                unfold delta_in_val in Hsat'.
                assert (Hperm := vars_of_to_l2r_subst φ ψ h Hlf Hnotinψ).
                apply sum_list_with_perm with (f := (size_of_var_in_val ρ)) in Hperm.
                rewrite Hperm in Hsat'. clear Hperm.
                rewrite TermOverBoV_subst_once_size in Hsat'.
                {

                    rewrite sum_list_with_app in Hsat'.
                    unfold delta_in_val in Heqmb'.
                    assert (Hszφ: TermOver_size φ = 1) by ltac1:(lia).
                    clear Hsat.
                    destruct φ.
                    {
                        simpl in *. clear Hszφ.
                        clear Htmp3.
                        destruct a.
                        {
                            simpl in *. ltac1:(lia).
                        }
                        simpl in *. rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst.
                            clear Heqmb' Hsat' Htmp2. clear Hlf.
                            simpl.
                            apply satisfies_var.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in *. ltac1:(lia).
                        }
                    }
                    {
                        simpl in Hszφ.
                        destruct l.
                        {
                            simpl in *. clear Hszφ Htmp3 Heqmb' Hsat'.
                            ltac1:(lia).
                        }
                        {
                            simpl in *.
                            ltac1:(lia).
                        }
                    }
                }
                {
                    rewrite <- vars_of_uglify.
                    assumption.
                }
                {
                    assumption.
                }
            }
        }
        {
            destruct γ.
            {
                destruct φ.
                {
                    destruct a0; simpl in *.
                    {
                        ltac1:(lia).
                    }
                    {
                        rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst. simpl in *. clear Hlf.
                            split>[exact Hsat|]. clear IHsz.
                            apply satisfies_var.
                            simpl.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in Hlf. inversion Hlf.
                        }
                    }
                }
                {
                    simpl in *.
                    apply satisfies_term_inv in Hsat.
                    destruct Hsat as [? [HContra ?]].
                    inversion HContra.
                }
            }
            {
                simpl in *.
                destruct φ.
                {
                    simpl in *.
                    destruct a.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        simpl in *.
                        rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst. simpl in *.
                            clear Hlf.
                            split>[apply Hsat|].
                            apply satisfies_var.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in *. ltac1:(lia).
                        }
                    }
                }
                {
                    destruct (list_find (λ φi : TermOver BuiltinOrVar, h ∈ vars_of_to_l2r φi) l0) eqn:Hfind.
                    {
                        destruct p.
                        apply list_find_Some in Hfind.
                        destruct (l !! n) eqn:Hln.
                        {
                            apply satisfies_term_inv in Hsat.
                            destruct Hsat as [lγ [H1 [H2 H3]]].
                            inversion H1; subst; clear H1.
                            simpl in *.
                            fold (@TermOverBoV_subst Σ) in *.
                            rewrite map_length in H2.
                            destruct Hfind as [Hfind1 [Hfind2 Hfind3]].
                            specialize (IHsz t0 t).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                apply take_drop_middle in Hln.
                                rewrite <- Hln in Hsz. simpl in Hsz.
                                rewrite sum_list_with_app in Hsz. simpl in Hsz.
                                ltac1:(lia).
                            }
                            specialize (IHsz Hnotinρ).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                assert (Hlf' := Hlf).
                                apply take_drop_middle in Hfind1.
                                rewrite <- Hfind1 in Hlf.
                                rewrite map_app in Hlf.
                                rewrite map_cons in Hlf.
                                rewrite concat_app in Hlf.
                                rewrite concat_cons in Hlf.
                                rewrite filter_app in Hlf.
                                rewrite filter_app in Hlf.
                                rewrite list_filter_Forall_not in Hlf.
                                {
                                    clear IHsz. simpl in Hlf.
                                    rewrite app_length in Hlf.
                                    ltac1:(rewrite -> list_filter_Forall_not with (l := (concat (map vars_of_to_l2r (drop (S n) l0)))) in Hlf).
                                    {
                                        simpl in Hlf.
                                        rewrite Nat.add_0_r in Hlf.
                                        exact Hlf.
                                    }
                                    {
                                        apply not_Exists_Forall.
                                        { intros ?. apply variable_eqdec. }
                                        {
                                            intros HContra. rewrite Exists_exists in HContra.
                                            destruct HContra as [x [HContra ?]].
                                            subst x.
                                            rewrite elem_of_list_lookup in HContra.
                                            destruct HContra as [j1 HContra].
                                            apply take_drop_middle in HContra.
                                            rewrite elem_of_list_lookup in Hfind2.
                                            destruct Hfind2 as [j2 Hfind2].
                                            apply take_drop_middle in Hfind2.
                                            rewrite <- Hfind2 in Hlf.
                                            rewrite <- HContra in Hlf.
                                            clear -Hlf.
                                            rewrite filter_app in Hlf.
                                            rewrite filter_app in Hlf.
                                            rewrite filter_cons in Hlf.
                                            rewrite filter_cons in Hlf.
                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                            simpl in Hlf.
                                            rewrite app_length in Hlf.
                                            rewrite app_length in Hlf.
                                            simpl in Hlf.
                                            ltac1:(lia).
                                        }
                                    }
                                }
                                {
                                    clear -Hfind3.
                                    rewrite Forall_forall.
                                    intros x Hx.
                                    rewrite elem_of_list_In in Hx.
                                    rewrite in_concat in Hx.
                                    destruct Hx as [x0 [H1x0 H2x0]].
                                    rewrite in_map_iff in H1x0.
                                    destruct H1x0 as [x1 [H1x1 H2x1]].
                                    rewrite <- elem_of_list_In in H2x1.
                                    rewrite <- elem_of_list_In in H2x0.
                                    subst. intros HContra. subst.
                                    rewrite elem_of_take in H2x1.
                                    destruct H2x1 as [i [H1i H2i]].
                                    ltac1:(naive_solver).
                                }
                            }
                            specialize (IHsz Hnotinψ).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                clear IHsz.
                                apply take_drop_middle in Hfind1.
                                apply take_drop_middle in Hln.
                                rewrite <- Hfind1 in H3.
                                rewrite <- Hln in H3.
                                rewrite map_app in H3.
                                rewrite map_cons in H3.
                                rewrite zip_with_app in H3.
                                {
                                    rewrite Forall_app in H3.
                                    simpl in H3.
                                    rewrite Forall_cons in H3.
                                    destruct H3 as [H31 [H32 H33]].
                                    exact H32.
                                }
                                {
                                    rewrite take_length.
                                    rewrite map_length.
                                    rewrite take_length.
                                    ltac1:(lia).
                                }
                            }
                            destruct IHsz as [IH1 IH2].
                            split>[apply IH1|].
                            unfold satisfies; simpl.
                            unfold apply_symbol'.
                            unfold to_PreTerm'.
                            unfold to_Term'.
                            constructor.
                            apply satisfies_top_bov_cons.
                            (repeat split); try reflexivity.
                            {
                                rewrite insert_length. ltac1:(lia).
                            }
                            {
                                assert (Hln' := Hln).
                                assert (Hfind1' := Hfind1).
                                apply take_drop_middle in Hln.
                                apply take_drop_middle in Hfind1.
                                rewrite <- Hln.
                                rewrite <- Hfind1.
                                rewrite insert_app_r_alt.
                                {
                                    rewrite take_length.
                                    rewrite Nat.min_l.
                                    {
                                        rewrite Nat.sub_diag.
                                        simpl.
                                        rewrite zip_with_app.
                                        {
                                            simpl.
                                            rewrite Forall_app.
                                            rewrite Forall_cons.
                                            repeat split.
                                            {
                                                rewrite Forall_forall.
                                                intros x Hx.
                                                rewrite elem_of_lookup_zip_with in Hx.
                                                destruct Hx as [i [x0 [y0 [HH1 [HH2 HH3]]]]].
                                                assert (Hi_lt_n : i < n).
                                                {
                                                    apply lookup_lt_Some in HH2.
                                                    rewrite take_length in HH2.
                                                    ltac1:(lia).
                                                }
                                                subst x.
                                                rewrite Forall_forall in H3.
                                                ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
                                                eapply satisfies_ext>[|apply H3;exists i,x0,y0;(split>[reflexivity|])].
                                                {
                                                    unfold Valuation in *.
                                                    apply insert_subseteq.
                                                    clear -Hnotinρ.
                                                    unfold vars_of in Hnotinρ; simpl in Hnotinρ.
                                                    apply not_elem_of_dom_1. exact Hnotinρ.
                                                }
                                                {
                                                    rewrite lookup_take in HH2.
                                                    split>[exact HH2|].
                                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                                    rewrite list_lookup_fmap.
                                                    rewrite lookup_take in HH3.
                                                    rewrite HH3.
                                                    simpl.
                                                    rewrite subst_notin.
                                                    { reflexivity. }
                                                    {
                                                        intros HContra.
                                                        rewrite elem_of_list_lookup in HContra.
                                                        destruct HContra as [j Hj].
                                                        apply take_drop_middle in Hj.
                                                        apply take_drop_middle in HH3.
                                                        rewrite <- HH3 in Hlf.
                                                        
                                                        rewrite map_app in Hlf.
                                                        rewrite map_cons in Hlf.
                                                        rewrite concat_app in Hlf.
                                                        rewrite concat_cons in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite <- Hj in Hlf.
                                                        clear Hj.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_cons in Hlf.
                                                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                        clear e.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        simpl in Hlf.
                                                        rewrite <- Hfind1 in Hlf.
                                                        assert (Hnl0: n < length l0).
                                                        {
                                                            apply lookup_lt_Some in Hfind1'.
                                                            exact Hfind1'.
                                                        }
                                                        (* clear -Hlf Hfind2 Hnl0. *)
                                                        apply elem_of_list_lookup in Hfind2.
                                                        destruct Hfind2 as [j' Hj'].
                                                        apply take_drop_middle in Hj'.
                                                        rewrite take_app in Hlf.
                                                        rewrite drop_app in Hlf.
                                                        rewrite take_length in Hlf.
                                                        destruct ((i - n `min` length l0)) eqn:Heq1.
                                                        {
                                                            simpl in Hlf.
                                                            destruct ((S i - n `min` length l0)) eqn:Heq2.
                                                            {
                                                                simpl in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_cons in Hlf.
                                                                simpl in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_cons in Hlf.
                                                                rewrite <- Hj' in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_cons in Hlf.
                                                                destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                                repeat (rewrite app_length in Hlf).
                                                                simpl in Hlf.
                                                                ltac1:(lia).
                                                            }
                                                            {
                                                                ltac1:(lia).
                                                            }
                                                        }
                                                        {
                                                            repeat (rewrite map_app in Hlf).
                                                            repeat (rewrite concat_app in Hlf).
                                                            repeat (rewrite filter_app in Hlf).
                                                            simpl in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite <- Hj' in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_cons in Hlf.
                                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                            repeat (rewrite app_length in Hlf).
                                                            simpl in Hlf.
                                                            ltac1:(lia).
                                                        }
                                                    }
                                                    {
                                                        ltac1:(lia).
                                                    }
                                                    {
                                                        ltac1:(lia).
                                                    }
                                                }
                                            }
                                            {
                                                exact IH2.
                                            }
                                            {
                                                rewrite Forall_forall.
                                                intros x Hx.
                                                rewrite elem_of_lookup_zip_with in Hx.
                                                destruct Hx as [i [x0 [y0 [HH1 [HH2 HH3]]]]].
                                                rewrite lookup_drop in HH2.
                                                rewrite lookup_drop in HH3.
                                                assert (S n + i < length l0).
                                                {
                                                    apply lookup_lt_Some in HH3.
                                                    ltac1:(lia).
                                                }
                                                subst x.
                                                rewrite Forall_forall in H3.
                                                ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
                                                eapply satisfies_ext>[|apply H3;exists (S n + i),x0,y0;(split>[reflexivity|])].
                                                {
                                                    unfold Valuation in *.
                                                    apply insert_subseteq.
                                                    clear -Hnotinρ.
                                                    unfold vars_of in Hnotinρ; simpl in Hnotinρ.
                                                    apply not_elem_of_dom_1. exact Hnotinρ.
                                                }
                                                {
                                                    split>[exact HH2|].
                                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                                    rewrite list_lookup_fmap.
                                                    rewrite HH3.
                                                    simpl.
                                                    rewrite subst_notin.
                                                    { reflexivity. }
                                                    {
                                                        intros HContra.
                                                        rewrite elem_of_list_lookup in HContra.
                                                        destruct HContra as [j Hj].
                                                        apply take_drop_middle in Hj.
                                                        apply take_drop_middle in HH3.
                                                        rewrite <- HH3 in Hlf.
                                                        
                                                        rewrite map_app in Hlf.
                                                        rewrite map_cons in Hlf.
                                                        rewrite concat_app in Hlf.
                                                        rewrite concat_cons in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite <- Hj in Hlf.
                                                        clear Hj.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_cons in Hlf.
                                                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                        clear e.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        simpl in Hlf.
                                                        rewrite <- Hfind1 in Hlf.
                                                        assert (Hnl0: n < length l0).
                                                        {
                                                            apply lookup_lt_Some in Hfind1'.
                                                            exact Hfind1'.
                                                        }
                                                        (* clear -Hlf Hfind2 Hnl0. *)
                                                        apply elem_of_list_lookup in Hfind2.
                                                        destruct Hfind2 as [j' Hj'].
                                                        apply take_drop_middle in Hj'.
                                                        rewrite take_app in Hlf.
                                                        rewrite drop_app in Hlf.
                                                        rewrite take_length in Hlf.
                                                        destruct (((S (n + i)) - n `min` length l0)) eqn:Heq1.
                                                        {
                                                            simpl in Hlf.
                                                            destruct ((S (S (n + i)) - n `min` length l0)) eqn:Heq2.
                                                            {
                                                                simpl in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_cons in Hlf.
                                                                simpl in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_cons in Hlf.
                                                                rewrite <- Hj' in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_cons in Hlf.
                                                                destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                                repeat (rewrite app_length in Hlf).
                                                                simpl in Hlf.
                                                                ltac1:(lia).
                                                            }
                                                            {
                                                                ltac1:(lia).
                                                            }
                                                        }
                                                        {
                                                            repeat (rewrite map_app in Hlf).
                                                            repeat (rewrite concat_app in Hlf).
                                                            repeat (rewrite filter_app in Hlf).
                                                            simpl in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite <- Hj' in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_cons in Hlf.
                                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                            repeat (rewrite app_length in Hlf).
                                                            simpl in Hlf.
                                                            ltac1:(lia).
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        {
                                            rewrite take_length.
                                            rewrite take_length.
                                            ltac1:(lia).
                                        }
                                    }
                                    {
                                        apply lookup_lt_Some in Hln'.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    rewrite take_length. ltac1:(lia).
                                }
                            }
                        }
                        {
                            simpl in *.
                            apply satisfies_term_inv in Hsat.
                            destruct Hsat as [lγ [H1 [H2 H3]]].
                            inversion H1; subst; clear H1.
                            simpl in *.
                            rewrite map_length in H2.
                            destruct Hfind as [HContra ?].
                            apply lookup_lt_Some in HContra.
                            apply lookup_ge_None in Hln.
                            ltac1:(lia).
                        }
                    }
                    {
                        apply list_find_None in Hfind.
                        simpl in *.
                        apply satisfies_term_inv in Hsat.
                        destruct Hsat as [lγ [H1 [H2 H3]]].
                        inversion H1; subst; clear H1.
                        rewrite map_length in H2.
                        clear Heqmb.
                        ltac1:(exfalso).
                        clear -Hlf Hfind.
                        rewrite list_filter_Forall_not in Hlf.
                        {
                            simpl in Hlf. inversion Hlf.
                        }
                        {
                            clear -Hfind.
                            rewrite Forall_forall.
                            rewrite Forall_forall in Hfind.
                            intros x Hx.
                            rewrite elem_of_list_In in Hx.
                            rewrite in_concat in Hx.
                            destruct Hx as [x0 [H1x0 H2x0]].
                            rewrite in_map_iff in H1x0.
                            destruct H1x0 as [x1 [H1x2 H2x1]].
                            subst x0.
                            specialize (Hfind x1).
                            rewrite <- elem_of_list_In in H2x1.
                            specialize (Hfind H2x1).
                            intros HContra. subst x.
                            apply Hfind.
                            rewrite <- elem_of_list_In in H2x0.
                            apply H2x0.
                        }
                    }
                }
            }
        }
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
        eapply frto_step>[|apply H6|].
        { assumption. }
        {
            eapply IHw1.
            { apply X. }
            { apply H1. }
        }
    }
Qed.

Lemma satisfies_TermOver_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    (∀ x : variable, x ∈ vars_of (uglify' φ) → ρ1 !! x = ρ2 !! x) →
    satisfies ρ1 g φ ↔ satisfies ρ2 g φ
.
Proof.
    intros H.
    assert (Htmp := satisfies_Term'_vars_of ρ1 ρ2 (uglify' g) (uglify' φ) H).
    apply Htmp.
Qed.


Lemma satisfies_PreTerm'Expression_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : PreTerm' symbol builtin_value)
    (φ : PreTerm' symbol Expression)
:
    (forall (x : variable), x ∈ vars_of φ -> ρ1!!x = ρ2!!x) ->
    (
    satisfies ρ1 g φ
    <->
    satisfies ρ2 g φ
    )
.
Proof.
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ1 g φ)).
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ2 g φ)).
    revert φ.
    induction g; intros φ Hvars; destruct φ;
        unfold matchesb in *; unfold vars_of in *;
        simpl in *;
        try ltac1:(tauto).
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        destruct
            (decide (Expression_evaluate ρ1 b0 = Some (term_operand b))) as [Hsome1|Hnone1],
            (decide (Expression_evaluate ρ2 b0 = Some (term_operand b))) as [Hsome2|Hnone2].
        {
            rewrite Hsome1. rewrite Hsome2.
            reflexivity.
        }
        {
            ltac1:(exfalso).
            apply Hnone2. clear Hnone2.
            assert (Hsome1' := Hsome1).
            apply expression_evaluate_some_valuation in Hsome1'.
            erewrite Expression_evaluate_val_restrict.
            { apply Hsome1. }
            unfold valuation_restrict.
            rewrite map_filter_strong_ext.
            intros i x.
            simpl.
            clear IHg.
            specialize (Hvars i).
            split; intros [HH1 HH2]; specialize (Hvars ltac:(set_solver));
                split; try assumption.
            {
                ltac1:(rewrite Hvars). assumption.
            }
            {
                ltac1:(rewrite -Hvars). assumption.
            }
        }
        {
            ltac1:(exfalso).
            apply Hnone1. clear Hnone1.
            assert (Hsome2' := Hsome2).
            apply expression_evaluate_some_valuation in Hsome2'.
            erewrite Expression_evaluate_val_restrict.
            { apply Hsome2. }
            unfold valuation_restrict.
            rewrite map_filter_strong_ext.
            intros i x.
            simpl.
            clear IHg.
            specialize (Hvars i).
            split; intros [HH1 HH2]; specialize (Hvars ltac:(set_solver));
                split; try assumption.
            {
                ltac1:(rewrite -Hvars). assumption.
            }
            {
                ltac1:(rewrite Hvars). assumption.
            }
        }
        {
            clear IHg Hvars.
            rewrite bool_decide_eq_true.
            rewrite bool_decide_eq_true.
            ltac1:(tauto).
        }
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        ltac1:(tauto).
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg1).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        destruct
            (decide (Expression_evaluate ρ1 b = Some (term_preterm g2))) as [Hsome1|Hnone1],
            (decide (Expression_evaluate ρ2 b = Some (term_preterm g2))) as [Hsome2|Hnone2].
        {
            rewrite Hsome1. rewrite Hsome2.
            reflexivity.
        }
        {
            ltac1:(exfalso).
            apply Hnone2. clear Hnone2.
            assert (Hsome1' := Hsome1).
            apply expression_evaluate_some_valuation in Hsome1'.
            erewrite Expression_evaluate_val_restrict.
            { apply Hsome1. }
            unfold valuation_restrict.
            rewrite map_filter_strong_ext.
            intros i x.
            simpl.
            clear IHg.
            specialize (Hvars i).
            split; intros [HH1 HH2]; specialize (Hvars ltac:(set_solver));
                split; try assumption.
            {
                ltac1:(rewrite Hvars). assumption.
            }
            {
                ltac1:(rewrite -Hvars). assumption.
            }
        }
        {
            ltac1:(exfalso).
            apply Hnone1. clear Hnone1.
            assert (Hsome2' := Hsome2).
            apply expression_evaluate_some_valuation in Hsome2'.
            erewrite Expression_evaluate_val_restrict.
            { apply Hsome2. }
            unfold valuation_restrict.
            rewrite map_filter_strong_ext.
            intros i x.
            simpl.
            clear IHg.
            specialize (Hvars i).
            split; intros [HH1 HH2]; specialize (Hvars ltac:(set_solver));
                split; try assumption.
            {
                ltac1:(rewrite -Hvars). assumption.
            }
            {
                ltac1:(rewrite Hvars). assumption.
            }
        }
        {
            clear IHg Hvars.
            rewrite bool_decide_eq_true.
            rewrite bool_decide_eq_true.
            ltac1:(tauto).
        }
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg1).
        { ltac1:(set_solver). }
        ltac1:(rewrite IHg2).
        { ltac1:(set_solver). }
        reflexivity.
    }
Qed.

Lemma satisfies_Term'Expression_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : Term' symbol builtin_value)
    (φ : Term' symbol Expression)
:
    (forall (x : variable), x ∈ vars_of φ -> ρ1!!x = ρ2!!x) ->
    (
    satisfies ρ1 g φ
    <->
    satisfies ρ2 g φ
    )
.
Proof.
    intros Hvars.
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ1 g φ)).
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ2 g φ)).
    destruct g, φ; unfold matchesb; simpl.
    {
        rewrite <- (reflect_iff _ _ (matchesb_satisfies ρ1 ao ao0)).
        rewrite <- (reflect_iff _ _ (matchesb_satisfies ρ2 ao ao0)).
        apply satisfies_PreTerm'Expression_vars_of.
        apply Hvars.
    }
    {
        unfold matchesb; simpl.

        destruct
            (decide (Expression_evaluate ρ1 operand = Some (term_preterm ao))) as [Hsome1|Hnone1],
            (decide (Expression_evaluate ρ2 operand = Some (term_preterm ao))) as [Hsome2|Hnone2].
        {
            rewrite Hsome1. rewrite Hsome2.
            reflexivity.
        }
        {
            ltac1:(exfalso).
            apply Hnone2. clear Hnone2.
            assert (Hsome1' := Hsome1).
            apply expression_evaluate_some_valuation in Hsome1'.
            erewrite Expression_evaluate_val_restrict.
            { apply Hsome1. }
            unfold valuation_restrict.
            rewrite map_filter_strong_ext.
            intros i x.
            simpl.
            clear IHg.
            specialize (Hvars i).
            split; intros [HH1 HH2]; specialize (Hvars ltac:(set_solver));
                split; try assumption.
            {
                ltac1:(rewrite Hvars). assumption.
            }
            {
                ltac1:(rewrite -Hvars). assumption.
            }
        }
        {
            ltac1:(exfalso).
            apply Hnone1. clear Hnone1.
            assert (Hsome2' := Hsome2).
            apply expression_evaluate_some_valuation in Hsome2'.
            erewrite Expression_evaluate_val_restrict.
            { apply Hsome2. }
            unfold valuation_restrict.
            rewrite map_filter_strong_ext.
            intros i x.
            simpl.
            clear IHg.
            specialize (Hvars i).
            split; intros [HH1 HH2]; specialize (Hvars ltac:(set_solver));
                split; try assumption.
            {
                ltac1:(rewrite -Hvars). assumption.
            }
            {
                ltac1:(rewrite Hvars). assumption.
            }
        }
        {
            clear IHg Hvars.
            rewrite bool_decide_eq_true.
            rewrite bool_decide_eq_true.
            ltac1:(tauto).
        }
    }
    {
        ltac1:(tauto).
    }
    {
        unfold matchesb; simpl.


        destruct
            (decide (Expression_evaluate ρ1 operand0 = Some (term_operand operand))) as [Hsome1|Hnone1],
            (decide (Expression_evaluate ρ2 operand0 = Some (term_operand operand))) as [Hsome2|Hnone2].
        {
            rewrite Hsome1. rewrite Hsome2.
            reflexivity.
        }
        {
            ltac1:(exfalso).
            apply Hnone2. clear Hnone2.
            assert (Hsome1' := Hsome1).
            apply expression_evaluate_some_valuation in Hsome1'.
            erewrite Expression_evaluate_val_restrict.
            { apply Hsome1. }
            unfold valuation_restrict.
            rewrite map_filter_strong_ext.
            intros i x.
            simpl.
            clear IHg.
            specialize (Hvars i).
            split; intros [HH1 HH2]; specialize (Hvars ltac:(set_solver));
                split; try assumption.
            {
                ltac1:(rewrite Hvars). assumption.
            }
            {
                ltac1:(rewrite -Hvars). assumption.
            }
        }
        {
            ltac1:(exfalso).
            apply Hnone1. clear Hnone1.
            assert (Hsome2' := Hsome2).
            apply expression_evaluate_some_valuation in Hsome2'.
            erewrite Expression_evaluate_val_restrict.
            { apply Hsome2. }
            unfold valuation_restrict.
            rewrite map_filter_strong_ext.
            intros i x.
            simpl.
            clear IHg.
            specialize (Hvars i).
            split; intros [HH1 HH2]; specialize (Hvars ltac:(set_solver));
                split; try assumption.
            {
                ltac1:(rewrite -Hvars). assumption.
            }
            {
                ltac1:(rewrite Hvars). assumption.
            }
        }
        {
            clear IHg Hvars.
            rewrite bool_decide_eq_true.
            rewrite bool_decide_eq_true.
            ltac1:(tauto).
        }
    }
Qed.

Lemma satisfies_TermOverExpression_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : TermOver builtin_value)
    (φ : TermOver Expression)
    :
    (∀ x : variable, x ∈ vars_of (uglify' φ) → ρ1 !! x = ρ2 !! x) →
    satisfies ρ1 g φ ↔ satisfies ρ2 g φ
.
Proof.
    intros H.
    assert (Htmp := satisfies_Term'Expression_vars_of ρ1 ρ2 (uglify' g) (uglify' φ) H).
    apply Htmp.
Qed.

Lemma valaution_restrict_subseteq
    {Σ : StaticModel}
    (e : Expression)
    (ρ1 ρ2 : Valuation)
    :
    (∀ x : variable, x ∈ vars_of e → ρ1 !! x = ρ2 !! x) ->
    vars_of e ⊆ vars_of ρ1 ->
    vars_of e ⊆ vars_of ρ2 -> 
    valuation_restrict ρ1 (vars_of e) = valuation_restrict ρ2 (vars_of e)
.
Proof.
    intros HH H1 H2.
    unfold valuation_restrict.
    rewrite map_filter_strong_ext.
    intros i x. simpl.
    rewrite elem_of_subseteq in H1.
    rewrite elem_of_subseteq in H2.
    specialize (H1 i).
    specialize (H2 i).
    unfold vars_of in H1; simpl in H1.
    unfold vars_of in H2; simpl in H2.
    rewrite elem_of_dom in H1.
    rewrite elem_of_dom in H2.
    split; intros [H3 H4]; specialize (H1 H3); specialize (H2 H3);
        split; try assumption.
    {
        destruct H1 as [x1 Hx1].
        destruct H2 as [x2 Hx2].
        specialize (HH i H3).
        ltac1:(rewrite HH in H4).
        exact H4.
    }
    {
        destruct H1 as [x1 Hx1].
        destruct H2 as [x2 Hx2].
        specialize (HH i H3).
        ltac1:(rewrite HH).
        exact H4.
    }
Qed.

Lemma satisfies_scs_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (scs : list SideCondition)
    :
    (∀ x : variable, x ∈ vars_of scs → ρ1 !! x = ρ2 !! x) →
    satisfies ρ1 () scs ↔ satisfies ρ2 () scs
.
Proof.
    intros H.
    unfold satisfies; simpl.
    induction scs.
    {
        split; intros _; apply Forall_nil; exact I.
    }
    {
        split; intros HH; apply Forall_cons;
            rewrite Forall_cons_iff in HH;
            destruct HH as [HH1 HH2];
            specialize (IHscs ltac:(set_solver));
            split; try ltac1:(naive_solver).
        (* satisfies ρ2 () a *)
        {
            clear IHscs HH2.
            assert (H': ∀ x : variable, x ∈ vars_of (a) → ρ1 !! x = ρ2 !! x).
            {
                unfold vars_of in H. simpl in H.
                ltac1:(set_solver).
            }
            clear H scs.
            destruct a; simpl in *.
            destruct c; simpl in *.
            unfold satisfies in HH1; simpl in HH1.
            unfold satisfies in HH1; simpl in HH1.
            unfold satisfies; simpl.
            unfold satisfies; simpl.
            destruct HH1 as [HH1 HH2].
            unfold is_Some in HH2.
            destruct HH2 as [x11 Hx11].
            assert (Hx12 : Expression_evaluate ρ1 e2 = Some x11).
            {
                ltac1:(congruence).
            }
            apply expression_evaluate_some_valuation in Hx11 as Hx11'.
            apply expression_evaluate_some_valuation in Hx12 as Hx12'.
            unfold is_Some.
            rewrite Expression_evalute_total_iff.
            unfold vars_of in H'; simpl in H'.
            unfold vars_of in H'; simpl in H'.
            assert (H2: vars_of e1 ⊆ vars_of ρ2).
            {
                rewrite elem_of_subseteq in Hx11'.
                rewrite elem_of_subseteq.
                intros x Hx.
                specialize (Hx11' x Hx).
                specialize (H' x ltac:(set_solver)).
                unfold vars_of in *; simpl in *.
                rewrite elem_of_dom.
                rewrite elem_of_dom in Hx11'.
                unfold is_Some in *.
                destruct Hx11' as [y Hy].
                exists y.
                ltac1:(rewrite - H').
                exact Hy.
            }
            assert (H3: vars_of e2 ⊆ vars_of ρ2).
            {
                rewrite elem_of_subseteq in Hx12'.
                rewrite elem_of_subseteq.
                intros x Hx.
                specialize (Hx12' x Hx).
                specialize (H' x ltac:(set_solver)).
                unfold vars_of in *; simpl in *.
                rewrite elem_of_dom.
                rewrite elem_of_dom in Hx12'.
                unfold is_Some in *.
                destruct Hx12' as [y Hy].
                exists y.
                ltac1:(rewrite - H').
                exact Hy.
            }
            split.
            {
                rewrite Expression_evaluate_val_restrict with (t := e1)(ρ2 := ρ1).
                {
                    rewrite HH1.
                    rewrite Expression_evaluate_val_restrict with (t := e2)(ρ2 := ρ2).
                    { reflexivity. }
                    {
                        apply valaution_restrict_subseteq; try assumption.
                        { ltac1:(set_solver). }
                    }
                }
                {
                    apply valaution_restrict_subseteq; try assumption.
                    { ltac1:(set_solver). }
                }
            }
            {
                exact H2.
            }
        }
        (* satisfies ρ1 () a *)
        {
            clear IHscs HH2.
            assert (H': ∀ x : variable, x ∈ vars_of (a) → ρ1 !! x = ρ2 !! x).
            {
                unfold vars_of in H. simpl in H.
                ltac1:(set_solver).
            }
            clear H scs.
            destruct a; simpl in *.
            destruct c; simpl in *.
            unfold satisfies in HH1; simpl in HH1.
            unfold satisfies in HH1; simpl in HH1.
            unfold satisfies; simpl.
            unfold satisfies; simpl.
            destruct HH1 as [HH1 HH2].
            unfold is_Some in HH2.
            destruct HH2 as [x11 Hx11].
            assert (Hx12 : Expression_evaluate ρ2 e2 = Some x11).
            {
                ltac1:(congruence).
            }
            apply expression_evaluate_some_valuation in Hx11 as Hx11'.
            apply expression_evaluate_some_valuation in Hx12 as Hx12'.
            unfold is_Some.
            rewrite Expression_evalute_total_iff.
            unfold vars_of in H'; simpl in H'.
            unfold vars_of in H'; simpl in H'.
            assert (H2: vars_of e1 ⊆ vars_of ρ1).
            {
                rewrite elem_of_subseteq in Hx11'.
                rewrite elem_of_subseteq.
                intros x Hx.
                specialize (Hx11' x Hx).
                specialize (H' x ltac:(set_solver)).
                unfold vars_of in *; simpl in *.
                rewrite elem_of_dom.
                rewrite elem_of_dom in Hx11'.
                unfold is_Some in *.
                destruct Hx11' as [y Hy].
                exists y.
                ltac1:(rewrite H').
                exact Hy.
            }
            assert (H3: vars_of e2 ⊆ vars_of ρ1).
            {
                rewrite elem_of_subseteq in Hx12'.
                rewrite elem_of_subseteq.
                intros x Hx.
                specialize (Hx12' x Hx).
                specialize (H' x ltac:(set_solver)).
                unfold vars_of in *; simpl in *.
                rewrite elem_of_dom.
                rewrite elem_of_dom in Hx12'.
                unfold is_Some in *.
                destruct Hx12' as [y Hy].
                exists y.
                ltac1:(rewrite H').
                exact Hy.
            }
            split.
            {
                rewrite Expression_evaluate_val_restrict with (t := e1)(ρ2 := ρ2).
                {
                    rewrite HH1.
                    rewrite Expression_evaluate_val_restrict with (t := e2)(ρ2 := ρ1).
                    { reflexivity. }
                    {
                        apply valaution_restrict_subseteq; try assumption.
                        { ltac1:(set_solver). }
                    }
                }
                {
                    apply valaution_restrict_subseteq; try assumption.
                    { ltac1:(set_solver). }
                }
            }
            {
                exact H2.
            }
        }
    }
Qed.

Lemma uglify'_prettify'
    {Σ : StaticModel}
    {T : Type}
    (t : PreTerm' symbol T)
    :
    uglify' (prettify' t) = term_preterm t
.
Proof.
    rewrite <- (cancel uglify' prettify (term_preterm t)).
    apply f_equal.
    simpl. reflexivity.
Qed.

Lemma satisfies_TermOverBoV_to_TermOverExpr
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    satisfies ρ γ (TermOverBoV_to_TermOverExpr φ)
    <->
    satisfies ρ γ φ
.
Proof.
    revert γ.
    induction φ; intros γ.
    {
        unfold TermOverBoV_to_TermOverExpr.
        simpl.
        split; intros H.
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
                    apply (f_equal prettify) in H0.
                    rewrite (cancel prettify uglify') in H0.
                    subst γ.
                    inversion H3.
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
                    apply (f_equal prettify) in H0.
                    rewrite (cancel prettify uglify') in H0.
                    subst γ.
                    inversion H3; subst; clear H3.
                    simpl.
                    apply satisfies_var.
                    rewrite uglify'_prettify'.
                    assumption.
                }
            }
        }
        {
            destruct a.
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    simpl.
                    constructor.
                    inversion pf; subst; clear pf.
                    constructor.
                }
                {

                    apply (f_equal prettify) in H0.
                    rewrite (cancel prettify uglify') in H0.
                    subst γ.
                    simpl.
                    inversion H3.
                }
            }
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    simpl.
                    inversion pf; subst; clear pf.
                    constructor.
                    unfold satisfies; simpl.
                    assumption.
                }
                {
                    apply (f_equal prettify) in H0.
                    rewrite (cancel prettify uglify') in H0.
                    subst γ.
                    simpl.
                    inversion H3; subst; clear H3.
                    unfold satisfies; simpl.
                    rewrite uglify'_prettify'.
                    constructor.
                    assumption.
                }
            }
        }
    }
    {
        split; intros HH.
        {
            unfold TermOverBoV_to_TermOverExpr in HH.
            simpl in HH.
            apply satisfies_term_expr_inv in HH.
            destruct HH as [lγ [H1 [H2 H3]]].
            subst γ.
            unfold satisfies; simpl.
            unfold apply_symbol'; simpl.
            constructor.
            unfold to_PreTerm'; simpl.
            apply satisfies_top_bov_cons.
            split.
            {
                rewrite map_length in H2. ltac1:(lia).
            }
            {
                split>[|reflexivity].
                rewrite Forall_forall in H.
                rewrite Forall_forall in H3.
                rewrite Forall_forall.
                intros P.
                rewrite elem_of_lookup_zip_with.
                intros HH.
                ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
                destruct HH as [i [x [y [HH1 [HH2 HH3]]]]].
                subst P.
                rewrite <- H.
                {
                    apply H3.
                    exists i,x.
                    exists (TermOverBoV_to_TermOverExpr y).
                    split>[reflexivity|].
                    split>[assumption|].
                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                    rewrite list_lookup_fmap.
                    rewrite HH3. simpl. reflexivity.
                }
                {
                    rewrite elem_of_list_lookup. exists i. assumption.
                }
            }
        }
        {
            unfold TermOverBoV_to_TermOverExpr. simpl.
            apply satisfies_term_inv in HH.
            destruct HH as [lγ [HH1 [HH2 HH3]]].
            subst γ.
            unfold satisfies; simpl.
            unfold apply_symbol'; simpl.
            constructor.
            unfold to_PreTerm'; simpl.
            apply satisfies_top_bov_cons_expr.
            split.
            {
                rewrite map_length. ltac1:(lia).
            }
            split>[|reflexivity].
            rewrite Forall_forall in H.
            rewrite Forall_forall in HH3.
            rewrite Forall_forall.
            intros P HP.
            rewrite elem_of_lookup_zip_with in HP.
            destruct HP as [i [x [y [HH4 [HH5 HH6]]]]].
            subst P.
            ltac1:(replace map with (@fmap _ list_fmap) in HH6 by reflexivity).
            rewrite list_lookup_fmap in HH6.
            destruct (l !! i) eqn:Hli.
            {
                simpl in HH6. inversion HH6. subst. clear HH6.
                apply H.
                {
                    rewrite elem_of_list_lookup. exists i. assumption.
                }
                apply HH3.
                rewrite elem_of_lookup_zip_with.
                exists i,x,t.
                repeat split; assumption.
            }
            {
                apply lookup_ge_None in Hli.
                apply lookup_lt_Some in HH5.
                ltac1:(lia).
            }
        }
    }
Qed.


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
        unfold apply_symbol' in *.
        unfold to_Term' in *.
        unfold vars_of in *; simpl in *.
        unfold to_PreTerm' in *.
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
                inversion H2; subst; clear H2.
                rewrite elem_of_subseteq.
                intros x' Hx'.
                rewrite elem_of_singleton in Hx'.
                subst x'.
                rewrite elem_of_dom.
                exists (term_preterm axy).
                exact H1.
            }
        }
    }
    {
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
        apply satisfies_term_inv in HH.
        destruct HH as [lγ [H4 [H5 H6]]].
        subst c.
        rewrite <- (firstn_skipn (length l1) lγ) in H6.
        rewrite zip_with_app in H6.
        {
            rewrite Forall_app in H6.
            destruct H6 as [H6 H7].
            destruct (drop (length l1) lγ) eqn:Hed.
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
            simpl in H7.
            rewrite Forall_cons in H7.
            destruct H7 as [H7 H8].
            specialize (H2 ρ t H7).
            clear -H2 Hx.
            ltac1:(set_solver).
        }
        {
            rewrite take_length.
            rewrite app_length in H5.
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
            unfold vars_of at 2; simpl.
            unfold vars_of at 2; simpl.
            destruct (decide (x = x0)).
            {
                unfold vars_of at 2; simpl.
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
        fold (@uglify' Σ).
        unfold to_PreTerm'.
        apply satisfies_top_bov_cons.
        repeat split.
        {
            rewrite length_pfmap. reflexivity.
        }
        {
            rewrite Forall_forall.
            intros P HP.
            rewrite elem_of_lookup_zip_with in HP.
            destruct HP as [i [x [y [HP1 [HP2 HP3]]]]].
            assert (HP4 := @pfmap_lookup_Some_1 (TermOver BuiltinOrVar)).
            specialize (HP4 (TermOver builtin_value) l).
            specialize (HP4 _ i x HP2).
            simpl in HP4.
            subst P.
            rewrite HP4.
            assert (Htmp1: Some (proj1_sig ((pflookup l i (pfmap_lookup_Some_lt HP2)))) = Some y).
            {
                rewrite <- HP3.
                apply pflookup_spec.
            }
            apply (inj Some) in Htmp1.
            rewrite <- Htmp1.
            ltac1:(unshelve(eapply H0))>[()|()|reflexivity|()].
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
    ltac1:(funelim (TermOverBoV_eval ρ1 φ pf1)).
    {
        intros HH.
        rewrite <- Heqcall.
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
        specialize (IHe _ _ _ H1).
        exists x.
        split; assumption.
    }
    {
        rewrite bind_Some in HH.
        destruct HH as [x1 [Hx1 HH]].
        rewrite bind_Some in HH.
        destruct HH as [x2 [Hx2 HH]].
        inversion HH; subst; clear HH.
        specialize (IHe1 _ _ _ Hx1).
        specialize (IHe2 _ _ _ Hx2).
        rewrite bind_Some.
        exists x1.
        split>[assumption|].
                rewrite bind_Some.
        exists x2.
        split>[assumption|].
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
        specialize (IHe1 _ _ _ Hx1).
        specialize (IHe2 _ _ _ Hx2).
        specialize (IHe3 _ _ _ Hx3).
        rewrite bind_Some.
        exists x1.
        split>[assumption|].
        rewrite bind_Some.
        exists x2.
        split>[assumption|].
        rewrite bind_Some.
        exists x3.
        split>[assumption|].
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
    rewrite Forall_forall in HH.
    rewrite Forall_forall.
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
    destruct HH2 as [g' HH2].
    assert(Htmp1 := Expression_evaluate_subst ρ e1 g g' (mlld_isValue_var Act D)).
    specialize (Htmp1 ltac:(congruence)).
    rewrite Htmp1.
    assert(Htmp2 := Expression_evaluate_subst ρ e2 g g' (mlld_isValue_var Act D)).
    specialize (Htmp2 ltac:(congruence)).
    rewrite Htmp2.
    split>[reflexivity|].
    unfold is_Some. exists g'. reflexivity.
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
    rewrite Forall_forall in HH.
    rewrite Forall_forall.
    intros sc1. intros H1.
    unfold MinusL_isValue in *.
    rewrite elem_of_list_fmap in H1.
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


Lemma factor_by_subst_correct_2
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation)
    (h : variable)
    (γ : TermOver builtin_value)
    (φ ψ : TermOver BuiltinOrVar)
    : sz >= TermOver_size γ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    ~ (h ∈ vars_of_to_l2r ψ) ->
    satisfies ρ γ (TermOverBoV_subst φ h ψ) ->
    let xy := factor_by_subst sz ρ h γ φ ψ in
    satisfies ρ xy.2 ψ /\
    satisfies (<[h := (uglify' xy.2)]>ρ) xy.1 φ
.
Proof.
    revert γ φ.
    induction sz; intros γ φ Hsz.
    {
        destruct γ; simpl in Hsz; ltac1:(lia).
    }
    {
        intros Hlf Hnotinψ Hsat.
        unfold factor_by_subst. fold (@factor_by_subst Σ).
        simpl.
        destruct (matchesb ρ (uglify' γ) (uglify' ψ)) eqn:Heqmb.
        {
            simpl.
            split.
            {
                apply matchesb_implies_satisfies in Heqmb.
                unfold satisfies; simpl.
                apply Heqmb.
            }
            {
                apply matchesb_implies_satisfies in Heqmb.
                assert (Heqmb': satisfies ρ γ ψ).
                {
                    unfold satisfies; simpl.
                    apply Heqmb.
                }

                assert (Htmp2 := TermOver_size_not_zero ψ).
                assert (Htmp3 := TermOver_size_not_zero φ).
                assert (Hsat' := Hsat).
                apply concrete_is_larger_than_symbolic in Hsat'.
                apply concrete_is_larger_than_symbolic in Heqmb'.

                unfold delta_in_val in Hsat'.
                assert (Hperm := vars_of_to_l2r_subst φ ψ h Hlf Hnotinψ).
                apply sum_list_with_perm with (f := (size_of_var_in_val ρ)) in Hperm.
                rewrite Hperm in Hsat'. clear Hperm.
                rewrite TermOverBoV_subst_once_size in Hsat'.
                {

                    rewrite sum_list_with_app in Hsat'.
                    unfold delta_in_val in Heqmb'.
                    assert (Hszφ: TermOver_size φ = 1) by ltac1:(lia).
                    clear Hsat.
                    destruct φ.
                    {
                        simpl in *. clear Hszφ.
                        clear Htmp3.
                        destruct a.
                        {
                            simpl in *. ltac1:(lia).
                        }
                        simpl in *. rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst.
                            clear Heqmb' Hsat' Htmp2. clear Hlf.
                            simpl.
                            apply satisfies_var.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in *. ltac1:(lia).
                        }
                    }
                    {
                        simpl in Hszφ.
                        destruct l.
                        {
                            simpl in *. clear Hszφ Htmp3 Heqmb' Hsat'.
                            ltac1:(lia).
                        }
                        {
                            simpl in *.
                            ltac1:(lia).
                        }
                    }
                }
                {
                    rewrite <- vars_of_uglify.
                    assumption.
                }
                {
                    assumption.
                }
            }
        }
        {
            destruct γ.
            {
                destruct φ.
                {
                    destruct a0; simpl in *.
                    {
                        ltac1:(lia).
                    }
                    {
                        rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst. simpl in *. clear Hlf.
                            split>[exact Hsat|]. clear IHsz.
                            apply satisfies_var.
                            simpl.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in Hlf. inversion Hlf.
                        }
                    }
                }
                {
                    simpl in *.
                    apply satisfies_term_inv in Hsat.
                    destruct Hsat as [? [HContra ?]].
                    inversion HContra.
                }
            }
            {
                simpl in *.
                destruct φ.
                {
                    simpl in *.
                    destruct a.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        simpl in *.
                        rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst. simpl in *.
                            clear Hlf.
                            split>[apply Hsat|].
                            apply satisfies_var.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in *. ltac1:(lia).
                        }
                    }
                }
                {
                    destruct (list_find (λ φi : TermOver BuiltinOrVar, h ∈ vars_of_to_l2r φi) l0) eqn:Hfind.
                    {
                        destruct p.
                        apply list_find_Some in Hfind.
                        destruct (l !! n) eqn:Hln.
                        {
                            apply satisfies_term_inv in Hsat.
                            destruct Hsat as [lγ [H1 [H2 H3]]].
                            inversion H1; subst; clear H1.
                            simpl in *.
                            fold (@TermOverBoV_subst Σ) in *.
                            rewrite map_length in H2.
                            destruct Hfind as [Hfind1 [Hfind2 Hfind3]].
                            specialize (IHsz t0 t).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                apply take_drop_middle in Hln.
                                rewrite <- Hln in Hsz. simpl in Hsz.
                                rewrite sum_list_with_app in Hsz. simpl in Hsz.
                                ltac1:(lia).
                            }
                            
                            ltac1:(ospecialize (IHsz _)).
                            {
                                assert (Hlf' := Hlf).
                                apply take_drop_middle in Hfind1.
                                rewrite <- Hfind1 in Hlf.
                                rewrite map_app in Hlf.
                                rewrite map_cons in Hlf.
                                rewrite concat_app in Hlf.
                                rewrite concat_cons in Hlf.
                                rewrite filter_app in Hlf.
                                rewrite filter_app in Hlf.
                                rewrite list_filter_Forall_not in Hlf.
                                {
                                    clear IHsz. simpl in Hlf.
                                    rewrite app_length in Hlf.
                                    ltac1:(rewrite -> list_filter_Forall_not with (l := (concat (map vars_of_to_l2r (drop (S n) l0)))) in Hlf).
                                    {
                                        simpl in Hlf.
                                        rewrite Nat.add_0_r in Hlf.
                                        exact Hlf.
                                    }
                                    {
                                        apply not_Exists_Forall.
                                        { intros ?. apply variable_eqdec. }
                                        {
                                            intros HContra. rewrite Exists_exists in HContra.
                                            destruct HContra as [x [HContra ?]].
                                            subst x.
                                            rewrite elem_of_list_lookup in HContra.
                                            destruct HContra as [j1 HContra].
                                            apply take_drop_middle in HContra.
                                            rewrite elem_of_list_lookup in Hfind2.
                                            destruct Hfind2 as [j2 Hfind2].
                                            apply take_drop_middle in Hfind2.
                                            rewrite <- Hfind2 in Hlf.
                                            rewrite <- HContra in Hlf.
                                            clear -Hlf.
                                            rewrite filter_app in Hlf.
                                            rewrite filter_app in Hlf.
                                            rewrite filter_cons in Hlf.
                                            rewrite filter_cons in Hlf.
                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                            simpl in Hlf.
                                            rewrite app_length in Hlf.
                                            rewrite app_length in Hlf.
                                            simpl in Hlf.
                                            ltac1:(lia).
                                        }
                                    }
                                }
                                {
                                    clear -Hfind3.
                                    rewrite Forall_forall.
                                    intros x Hx.
                                    rewrite elem_of_list_In in Hx.
                                    rewrite in_concat in Hx.
                                    destruct Hx as [x0 [H1x0 H2x0]].
                                    rewrite in_map_iff in H1x0.
                                    destruct H1x0 as [x1 [H1x1 H2x1]].
                                    rewrite <- elem_of_list_In in H2x1.
                                    rewrite <- elem_of_list_In in H2x0.
                                    subst. intros HContra. subst.
                                    rewrite elem_of_take in H2x1.
                                    destruct H2x1 as [i [H1i H2i]].
                                    ltac1:(naive_solver).
                                }
                            }
                            specialize (IHsz Hnotinψ).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                clear IHsz.
                                apply take_drop_middle in Hfind1.
                                apply take_drop_middle in Hln.
                                rewrite <- Hfind1 in H3.
                                rewrite <- Hln in H3.
                                rewrite map_app in H3.
                                rewrite map_cons in H3.
                                rewrite zip_with_app in H3.
                                {
                                    rewrite Forall_app in H3.
                                    simpl in H3.
                                    rewrite Forall_cons in H3.
                                    destruct H3 as [H31 [H32 H33]].
                                    exact H32.
                                }
                                {
                                    rewrite take_length.
                                    rewrite map_length.
                                    rewrite take_length.
                                    ltac1:(lia).
                                }
                            }
                            destruct IHsz as [IH1 IH2].
                            split>[apply IH1|].
                            unfold satisfies; simpl.
                            unfold apply_symbol'.
                            unfold to_PreTerm'.
                            unfold to_Term'.
                            constructor.
                            apply satisfies_top_bov_cons.
                            (repeat split); try reflexivity.
                            {
                                rewrite insert_length. ltac1:(lia).
                            }
                            {
                                assert (Hln' := Hln).
                                assert (Hfind1' := Hfind1).
                                apply take_drop_middle in Hln.
                                apply take_drop_middle in Hfind1.
                                rewrite <- Hln.
                                rewrite <- Hfind1.
                                rewrite insert_app_r_alt.
                                {
                                    rewrite take_length.
                                    rewrite Nat.min_l.
                                    {
                                        rewrite Nat.sub_diag.
                                        simpl.
                                        rewrite zip_with_app.
                                        {
                                            simpl.
                                            rewrite Forall_app.
                                            rewrite Forall_cons.
                                            repeat split.
                                            {
                                                rewrite Forall_forall.
                                                intros x Hx.
                                                rewrite elem_of_lookup_zip_with in Hx.
                                                destruct Hx as [i [x0 [y0 [HH1 [HH2 HH3]]]]].
                                                assert (Hi_lt_n : i < n).
                                                {
                                                    apply lookup_lt_Some in HH2.
                                                    rewrite take_length in HH2.
                                                    ltac1:(lia).
                                                }
                                                subst x.
                                                rewrite Forall_forall in H3.
                                                ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
                                                Search satisfies vars_of.
                                                erewrite satisfies_TermOver_vars_of.
                                                { 
                                                    apply H3.
                                                    exists i,x0,y0.
                                                    split>[reflexivity|].
                                                    {
                                                        rewrite lookup_take in HH2.
                                                        split>[exact HH2|].
                                                        ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                                        rewrite list_lookup_fmap.
                                                        rewrite lookup_take in HH3.
                                                        rewrite HH3.
                                                        simpl.
                                                        rewrite subst_notin.
                                                        { reflexivity. }
                                                        {
                                                            intros HContra.
                                                            rewrite elem_of_list_lookup in HContra.
                                                            destruct HContra as [j Hj].
                                                            apply take_drop_middle in Hj.
                                                            apply take_drop_middle in HH3.
                                                            rewrite <- HH3 in Hlf.
                                                            
                                                            rewrite map_app in Hlf.
                                                            rewrite map_cons in Hlf.
                                                            rewrite concat_app in Hlf.
                                                            rewrite concat_cons in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite <- Hj in Hlf.
                                                            clear Hj.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_cons in Hlf.
                                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                            clear e.
                                                            rewrite app_length in Hlf.
                                                            rewrite app_length in Hlf.
                                                            rewrite app_length in Hlf.
                                                            simpl in Hlf.
                                                            rewrite <- Hfind1 in Hlf.
                                                            assert (Hnl0: n < length l0).
                                                            {
                                                                apply lookup_lt_Some in Hfind1'.
                                                                exact Hfind1'.
                                                            }
                                                            (* clear -Hlf Hfind2 Hnl0. *)
                                                            apply elem_of_list_lookup in Hfind2.
                                                            destruct Hfind2 as [j' Hj'].
                                                            apply take_drop_middle in Hj'.
                                                            rewrite take_app in Hlf.
                                                            rewrite drop_app in Hlf.
                                                            rewrite take_length in Hlf.
                                                            destruct ((i - n `min` length l0)) eqn:Heq1.
                                                            {
                                                                simpl in Hlf.
                                                                destruct ((S i - n `min` length l0)) eqn:Heq2.
                                                                {
                                                                    simpl in Hlf.
                                                                    rewrite map_app in Hlf.
                                                                    rewrite map_app in Hlf.
                                                                    rewrite map_cons in Hlf.
                                                                    simpl in Hlf.
                                                                    rewrite concat_app in Hlf.
                                                                    rewrite concat_app in Hlf.
                                                                    rewrite concat_cons in Hlf.
                                                                    rewrite <- Hj' in Hlf.
                                                                    rewrite filter_app in Hlf.
                                                                    rewrite filter_app in Hlf.
                                                                    rewrite filter_app in Hlf.
                                                                    rewrite filter_app in Hlf.
                                                                    rewrite filter_cons in Hlf.
                                                                    destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                                    repeat (rewrite app_length in Hlf).
                                                                    simpl in Hlf.
                                                                    ltac1:(lia).
                                                                }
                                                                {
                                                                    ltac1:(lia).
                                                                }
                                                            }
                                                            {
                                                                repeat (rewrite map_app in Hlf).
                                                                repeat (rewrite concat_app in Hlf).
                                                                repeat (rewrite filter_app in Hlf).
                                                                simpl in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite <- Hj' in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_cons in Hlf.
                                                                destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                                repeat (rewrite app_length in Hlf).
                                                                simpl in Hlf.
                                                                ltac1:(lia).
                                                            }
                                                        }
                                                        {
                                                            ltac1:(lia).
                                                        }
                                                        {
                                                            ltac1:(lia).
                                                        }
                                                    }
                                                }
                                                {
                                                    intros x Hx.
                                                    destruct (decide (x = h)).
                                                    {
                                                        subst x.
                                                        ltac1:(exfalso).
                                                        apply take_drop_middle in HH3.
                                                        rewrite <- Hfind1 in Hlf.
                                                        rewrite <- HH3 in Hlf.
                                                        clear Hfind1 HH3 IH1 IH2.
                                                        clear - Hlf Hfind2 Hx.
                                                        rewrite map_app in Hlf.
                                                        rewrite map_app in Hlf.
                                                        simpl in Hlf.
                                                        rewrite concat_app in Hlf.
                                                        rewrite concat_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        simpl in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite elem_of_list_lookup in Hfind2.
                                                        rewrite <- vars_of_uglify in Hx.
                                                        rewrite elem_of_list_lookup in Hx.
                                                        destruct Hfind2 as [i1 Hi1].
                                                        destruct Hx as [i2 Hi2].
                                                        apply take_drop_middle in Hi1.
                                                        apply take_drop_middle in Hi2.
                                                        rewrite <- Hi1 in Hlf.
                                                        rewrite <- Hi2 in Hlf.
                                                        clear Hi1 Hi2.
                                                        simpl in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_cons in Hlf.
                                                        rewrite filter_cons in Hlf.
                                                        destruct (decide (h=h))>[|ltac1:(congruence)].
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        simpl in Hlf.
                                                        ltac1:(lia).
                                                    }
                                                    {
                                                        unfold Valuation in *.
                                                        rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                                        reflexivity.
                                                    }
                                                }
                                            }
                                            {
                                                exact IH2.
                                            }
                                            {
                                                rewrite Forall_forall.
                                                intros x Hx.
                                                rewrite elem_of_lookup_zip_with in Hx.
                                                destruct Hx as [i [x0 [y0 [HH1 [HH2 HH3]]]]].
                                                rewrite lookup_drop in HH2.
                                                rewrite lookup_drop in HH3.
                                                assert (S n + i < length l0).
                                                {
                                                    apply lookup_lt_Some in HH3.
                                                    ltac1:(lia).
                                                }
                                                subst x.
                                                rewrite Forall_forall in H3.
                                                ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
                                                erewrite satisfies_TermOver_vars_of.
                                                {
                                                    apply H3.
                                                    exists (S n + i),x0,y0;(split>[reflexivity|]).

                                                    split>[exact HH2|].
                                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                                    rewrite list_lookup_fmap.
                                                    rewrite HH3.
                                                    simpl.
                                                    rewrite subst_notin.
                                                    { reflexivity. }
                                                    {
                                                        intros HContra.
                                                        rewrite elem_of_list_lookup in HContra.
                                                        destruct HContra as [j Hj].
                                                        apply take_drop_middle in Hj.
                                                        apply take_drop_middle in HH3.
                                                        rewrite <- HH3 in Hlf.
                                                        
                                                        rewrite map_app in Hlf.
                                                        rewrite map_cons in Hlf.
                                                        rewrite concat_app in Hlf.
                                                        rewrite concat_cons in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite <- Hj in Hlf.
                                                        clear Hj.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_cons in Hlf.
                                                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                        clear e.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        simpl in Hlf.
                                                        rewrite <- Hfind1 in Hlf.
                                                        assert (Hnl0: n < length l0).
                                                        {
                                                            apply lookup_lt_Some in Hfind1'.
                                                            exact Hfind1'.
                                                        }
                                                        (* clear -Hlf Hfind2 Hnl0. *)
                                                        apply elem_of_list_lookup in Hfind2.
                                                        destruct Hfind2 as [j' Hj'].
                                                        apply take_drop_middle in Hj'.
                                                        rewrite take_app in Hlf.
                                                        rewrite drop_app in Hlf.
                                                        rewrite take_length in Hlf.
                                                        destruct (((S (n + i)) - n `min` length l0)) eqn:Heq1.
                                                        {
                                                            simpl in Hlf.
                                                            destruct ((S (S (n + i)) - n `min` length l0)) eqn:Heq2.
                                                            {
                                                                simpl in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_cons in Hlf.
                                                                simpl in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_cons in Hlf.
                                                                rewrite <- Hj' in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_cons in Hlf.
                                                                destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                                repeat (rewrite app_length in Hlf).
                                                                simpl in Hlf.
                                                                ltac1:(lia).
                                                            }
                                                            {
                                                                ltac1:(lia).
                                                            }
                                                        }
                                                        {
                                                            repeat (rewrite map_app in Hlf).
                                                            repeat (rewrite concat_app in Hlf).
                                                            repeat (rewrite filter_app in Hlf).
                                                            simpl in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite <- Hj' in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_cons in Hlf.
                                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                            repeat (rewrite app_length in Hlf).
                                                            simpl in Hlf.
                                                            ltac1:(lia).
                                                        }
                                                    }
                                                }
                                                {
                                                    intros x Hx.
                                                    destruct (decide (x = h)).
                                                    {
                                                        subst x.
                                                        ltac1:(exfalso).
                                                        apply take_drop_middle in HH3.
                                                        rewrite <- Hfind1 in Hlf.
                                                        rewrite <- HH3 in Hlf.

                                                        rewrite map_app in Hlf.
                                                        simpl in Hlf.
                                                        
                                                        simpl in Hlf.
                                                        rewrite concat_app in Hlf.

                                                        rewrite filter_app in Hlf.
                                                        simpl in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite elem_of_list_lookup in Hfind2.
                                                        rewrite <- vars_of_uglify in Hx.
                                                        rewrite elem_of_list_lookup in Hx.
                                                        destruct Hfind2 as [i1 Hi1].
                                                        destruct Hx as [i2 Hi2].
                                                        apply take_drop_middle in Hi1.
                                                        apply take_drop_middle in Hi2.
                                                        rewrite <- Hi1 in Hlf.
                                                        ltac1:(rewrite take_app_le in Hlf).
                                                        {
                                                            rewrite take_length.
                                                            ltac1:(lia).
                                                        }
                                                        rewrite filter_app in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite drop_app in Hlf.
                                                        rewrite map_app in Hlf.
                                                        rewrite concat_app in Hlf.
                                                        destruct (decide ((S n - length (take (S (n + i)) l0)) = 0)) as [Hz | Hnz].
                                                        {
                                                            rewrite Hz in Hlf.
                                                            simpl in Hlf.
                                                            rewrite <- Hi2 in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_cons in Hlf.
                                                            rewrite filter_cons in Hlf.
                                                            destruct (decide (h=h))>[|ltac1:(congruence)].
                                                            simpl in Hlf.
                                                            rewrite app_length in Hlf.
                                                            rewrite app_length in Hlf.
                                                            rewrite app_length in Hlf.
                                                            simpl in Hlf.
                                                            ltac1:(lia).
                                                        }
                                                        {
                                                            rewrite take_length in Hnz.
                                                            ltac1:(lia).
                                                        }
                                                    }
                                                    {
                                                        unfold Valuation in *.
                                                        rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                                        reflexivity.
                                                    }
                                                }
                                            }
                                        }
                                        {
                                            rewrite take_length.
                                            rewrite take_length.
                                            ltac1:(lia).
                                        }
                                    }
                                    {
                                        apply lookup_lt_Some in Hln'.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    rewrite take_length. ltac1:(lia).
                                }
                            }
                        }
                        {
                            simpl in *.
                            apply satisfies_term_inv in Hsat.
                            destruct Hsat as [lγ [H1 [H2 H3]]].
                            inversion H1; subst; clear H1.
                            simpl in *.
                            rewrite map_length in H2.
                            destruct Hfind as [HContra ?].
                            apply lookup_lt_Some in HContra.
                            apply lookup_ge_None in Hln.
                            ltac1:(lia).
                        }
                    }
                    {
                        apply list_find_None in Hfind.
                        simpl in *.
                        apply satisfies_term_inv in Hsat.
                        destruct Hsat as [lγ [H1 [H2 H3]]].
                        inversion H1; subst; clear H1.
                        rewrite map_length in H2.
                        clear Heqmb.
                        ltac1:(exfalso).
                        clear -Hlf Hfind.
                        rewrite list_filter_Forall_not in Hlf.
                        {
                            simpl in Hlf. inversion Hlf.
                        }
                        {
                            clear -Hfind.
                            rewrite Forall_forall.
                            rewrite Forall_forall in Hfind.
                            intros x Hx.
                            rewrite elem_of_list_In in Hx.
                            rewrite in_concat in Hx.
                            destruct Hx as [x0 [H1x0 H2x0]].
                            rewrite in_map_iff in H1x0.
                            destruct H1x0 as [x1 [H1x2 H2x1]].
                            subst x0.
                            specialize (Hfind x1).
                            rewrite <- elem_of_list_In in H2x1.
                            specialize (Hfind H2x1).
                            intros HContra. subst x.
                            apply Hfind.
                            rewrite <- elem_of_list_In in H2x0.
                            apply H2x0.
                        }
                    }
                }
            }
        }
    }
Qed.

Lemma list_find_elem_of_isSome
    {A : Type}
    (P : A -> Prop)
    {_dP : forall x, Decision (P x)}
    (l : list A)
    (x : A)
    :
    x ∈ l -> P x -> isSome (list_find P l).
Proof.
    ltac1:(induction 1 as [|x y l ? IH]; intros; simplify_option_eq; eauto).
    specialize (IH ltac:(assumption)).
    Set Printing Coercions.
    unfold is_true, isSome in *.
    destruct (list_find P l) eqn:Hfound; simpl.
    { reflexivity. }
    { inversion IH. }
Qed.

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
                        apply satisfies_top_bov_cons.
                        (repeat split).
                        {
                            apply Forall_cons.
                            split.
                            {
                                apply satisfies_top_bov.
                                split.
                                {
                                    erewrite satisfies_TermOver_vars_of.
                                    { apply s. }
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
                                {
                                    apply satisfies_var.
                                    ltac1:(rewrite lookup_insert).
                                    reflexivity.
                                }
                            }
                            {
                                apply Forall_cons.
                                split.
                                {
                                    erewrite satisfies_TermOver_vars_of.
                                    { apply s0. }
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
                                {
                                    apply Forall_nil. exact I.
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
                        apply satisfies_top_bov_cons_expr.
                        (repeat split).
                        {
                            apply Forall_cons.
                            split.
                            {
                                apply satisfies_top_expr.
                                split.
                                {
                                    erewrite satisfies_TermOverExpression_vars_of.
                                    { apply s1. }
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
                                {
                                    apply satisfies_var_expr.
                                    ltac1:(rewrite lookup_insert).
                                    reflexivity.
                                }
                            }
                            {
                                apply Forall_cons.
                                split.
                                {
                                    erewrite satisfies_TermOverExpression_vars_of.
                                    { apply s2. }
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
                                {
                                    apply Forall_nil. exact I.
                                }
                            }
                        }
                    }
                    {
                        simpl.
                        erewrite satisfies_scs_vars_of.
                        { apply s3. }
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
                assert (Htmp: (vars_of (uglify' c)) ∖ {[h]} ⊆ (dom (<[h:=uglify' r]> ρ1)) ∖ {[h]}).
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
                assert (Htmp: (vars_of (uglify' c)) ∖ {[h]} ⊆ (dom (<[h:=uglify' v]> ρ2)) ∖ {[h]}).
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
                rewrite vars_of__TermOverBoV_subst__varless in Hx>[|reflexivity].
                apply e0.
                {
                    rewrite vars_of_uglify.
                    unfold vars_of in Hx; simpl in Hx.
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
                    unfold to_PreTerm'.
                    ltac1:(
                        replace ([apply_symbol' cseqSymbol [uglify' ctrl1; uglify' cont]; uglify' state1])
                        with (map uglify' [(t_term cseqSymbol [ctrl1; cont]);state1])
                        by reflexivity
                    ).
                    ltac1:(
                        replace ([apply_symbol' cseqSymbol [uglify' c; term_operand (bov_variable V1)]; term_operand (bov_variable V2)])
                        with (map uglify' [t_term cseqSymbol [c; (t_over (bov_variable V1))]; (t_over (bov_variable V2))])
                        by reflexivity
                    ).
                    apply satisfies_top_bov_cons.
                    (repeat split).
                    simpl.
                    repeat (rewrite Forall_cons).
                    (repeat split).
                    {
                        constructor.
                        fold (@uglify' Σ).
                        apply satisfies_top_bov_cons.
                        (repeat split).
                        simpl.
                        repeat (rewrite Forall_cons).
                        (repeat split).
                        {
                            erewrite satisfies_TermOver_vars_of.
                            { apply s. }
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
                                    clear -Hx HeqV2.
                                    intros HContra. subst.
                                    assert(Hx': fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
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
                            apply satisfies_var.
                            unfold Valuation in *.
                            rewrite lookup_insert_ne.
                            rewrite lookup_insert_ne.
                            rewrite lookup_insert.
                            { reflexivity. }
                            {
                                clear -HeqV2.
                                intros HContra. subst.
                                assert(Hx': fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
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
                            apply Forall_nil. exact I.
                        }
                    }
                    {
                        apply satisfies_var.
                        unfold Valuation in *.
                        rewrite lookup_insert_ne.
                        rewrite lookup_insert.
                        { reflexivity. }
                        {
                            clear -HeqV2.
                            intros HContra. subst.
                            assert(Hx': fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                            {
                                rewrite HContra at 2.
                                ltac1:(set_solver).
                            }
                            eapply infinite_is_fresh.
                            { apply Hx'. }
                        }
                    }
                    {
                        apply Forall_nil. exact I.
                    }
                }
                {
                    constructor.
                    unfold to_PreTerm'.
                    ltac1:(
                        replace ([apply_symbol' cseqSymbol [uglify' r; apply_symbol' cseqSymbol [uglify' ceval; uglify' cont]]; uglify' state1])
                        with (map uglify' [(t_term cseqSymbol [r; (t_term cseqSymbol [ceval; cont])]); state1])
                        by reflexivity
                    ).
                    ltac1:(
                        replace ([apply_symbol' cseqSymbol [term_operand (ft_variable h); apply_symbol' cseqSymbol [uglify' (TermOverBoV_to_TermOverExpr (TermOverBoV_subst c h (t_term holeSymbol []))); term_operand (ft_variable V1)]]; term_operand (ft_variable V2)])
                        with (map uglify' [(t_term cseqSymbol [t_over (ft_variable h); (t_term cseqSymbol [(TermOverBoV_to_TermOverExpr (TermOverBoV_subst c h (t_term holeSymbol []))); (t_over (ft_variable V1))])]); (t_over (ft_variable V2))])
                        by reflexivity
                    ).
                    apply satisfies_top_bov_cons_expr.
                    (repeat split).
                    simpl.
                    repeat (rewrite Forall_cons).
                    rewrite Forall_nil.
                    (repeat split).
                    {
                        constructor.
                        fold (@uglify' Σ).
                        apply satisfies_top_bov_cons_expr.
                        (repeat split).
                        simpl.
                        repeat (rewrite Forall_cons).
                        rewrite Forall_nil.
                        (repeat split).
                        {
                            apply satisfies_var_expr.
                            unfold Valuation in *.
                            rewrite lookup_insert.
                            reflexivity.
                        }
                        {
                            constructor.
                            fold (@uglify' Σ).
                            apply satisfies_top_bov_cons_expr.
                            (repeat split).
                            simpl.
                            (repeat (rewrite Forall_cons)).
                            rewrite Forall_nil.
                            (repeat split).
                            {
                                subst ceval.
                                rewrite <- Heqsubstituted.
                                rewrite satisfies_TermOverBoV_to_TermOverExpr.
                                erewrite satisfies_TermOver_vars_of.
                                { apply satisfies_TermOverBoV_eval. }
                                intros x Hx.
                                destruct (decide (x = h)).
                                {
                                    ltac1:(exfalso).
                                    subst x.
                                    subst substituted.
                                    clear -Hx Hvars.
                                    ltac1:(set_solver).
                                }
                                unfold Valuation in *.
                                rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                destruct (decide (x = V2)).
                                {
                                    ltac1:(exfalso).
                                    subst x.
                                    subst substituted.
                                    assert (Htmp: V2 ∈ vars_of c) by ltac1:(set_solver).
                                    unfold vars_of in Htmp; simpl in Htmp.
                                    rewrite <- vars_of_uglify in Htmp.
                                    clear -Htmp HeqV2.
                                    subst V2.
                                    assert (Htmp2: fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                    {
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
                                    assert (Htmp: V1 ∈ vars_of c) by ltac1:(set_solver).
                                    unfold vars_of in Htmp; simpl in Htmp.
                                    rewrite <- vars_of_uglify in Htmp.
                                    clear -Htmp HeqV1.
                                    subst V1.
                                    assert (Htmp2: fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                    {
                                        ltac1:(set_solver).
                                    }
                                    eapply infinite_is_fresh.
                                    apply Htmp2.
                                }
                                rewrite lookup_insert_ne>[|ltac1:(congruence)].
                                reflexivity.
                            }
                            {
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
                        }
                    }
                    {
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
                }
                {
                    rewrite satisfies_scs_vars_of.
                    { apply s0. }
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
                fold (@uglify' Σ).
                unfold to_PreTerm'.
                apply satisfies_top_bov_cons.
                (repeat split).
                unfold zip_with.
                repeat (rewrite Forall_cons).
                rewrite Forall_nil.
                (repeat split).
                {
                    constructor.
                    fold (@uglify' Σ).
                    unfold to_PreTerm'.
                    apply satisfies_top_bov_cons.
                    (repeat split).
                    unfold zip_with.
                    repeat (rewrite Forall_cons).
                    rewrite Forall_nil.
                    (repeat split).
                    {
                        apply satisfies_var.
                        unfold Valuation in *.
                        rewrite lookup_insert.
                        reflexivity.
                    }
                    {
                        constructor.
                        fold (@uglify' Σ).
                        unfold to_PreTerm'.
                        apply satisfies_top_bov_cons.
                        (repeat split).
                        unfold zip_with.
                        repeat (rewrite Forall_cons).
                        rewrite Forall_nil.
                        (repeat split).
                        {
                            rewrite Hceval12.
                            subst ceval2.
                            rewrite <- Heqsubstituted.
                            erewrite satisfies_TermOver_vars_of.
                            { apply satisfies_TermOverBoV_eval. }
                            intros x Hx.

                            destruct (decide (x = h)).
                            {
                                ltac1:(exfalso).
                                subst x.
                                subst substituted.
                                clear -Hx Hvars.
                                ltac1:(set_solver).
                            }
                            unfold Valuation in *.
                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                            destruct (decide (x = V2)).
                            {
                                ltac1:(exfalso).
                                subst x.
                                subst substituted.
                                assert (Htmp: V2 ∈ vars_of c) by ltac1:(set_solver).
                                unfold vars_of in Htmp; simpl in Htmp.
                                rewrite <- vars_of_uglify in Htmp.
                                clear -Htmp HeqV2.
                                subst V2.
                                assert (Htmp2: fresh (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: V1 :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                {
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
                                assert (Htmp: V1 ∈ vars_of c) by ltac1:(set_solver).
                                unfold vars_of in Htmp; simpl in Htmp.
                                rewrite <- vars_of_uglify in Htmp.
                                clear -Htmp HeqV1.
                                subst V1.
                                assert (Htmp2: fresh (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs))) ∈ (h :: vars_of_to_l2r c ++ elements (vars_of scs) ++ (elements (vars_of iV_scs)))).
                                {
                                    ltac1:(set_solver).
                                }
                                eapply infinite_is_fresh.
                                apply Htmp2.
                            }
                            rewrite lookup_insert_ne>[|ltac1:(congruence)].
                            reflexivity.
                        }
                        {
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
                    }
                }
                {
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
            }
            {
                constructor.
                fold (@uglify' Σ).
                unfold to_PreTerm'.
                apply satisfies_top_bov_cons_expr.
                (repeat split).
                unfold zip_with.
                repeat (rewrite Forall_cons).
                rewrite Forall_nil.
                (repeat split).
                {
                    constructor.
                    fold (@uglify' Σ).
                    unfold to_PreTerm'.
                    apply satisfies_top_bov_cons_expr.
                    (repeat split).
                    unfold zip_with.
                    repeat (rewrite Forall_cons).
                    rewrite Forall_nil.
                    (repeat split).
                    {
                        rewrite satisfies_TermOverBoV_to_TermOverExpr.
                        erewrite satisfies_TermOver_vars_of.
                        { apply s1. }
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
                }
                {
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
                    erewrite satisfies_scs_vars_of.
                    { apply s2. }
                    {
                        intros x Hx.
                        unfold Valuation in *.
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


Definition isDownC
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (t : TermOver builtin_value)
    : Prop
:=
    exists ctrl data cont,
    t = downC topSymbol cseqSymbol ctrl data cont
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
        exists lc ld a rc rd scs,
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
    ) + (
        exists c h scs,
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
    clear Heqfrom Heqto.
    revert w H1w' (* H2w' *) ctrl1 data1 ctrl2 data2 Hc1 Hd1 Hc2 Hd2 HfrIDC HtoIDC.
    induction H3w'; intros w'' H1w' (* H2w' *) ctrl1 data1 ctrl2 data2 Hc1 Hd1 Hc2 Hd2 HfrIDC HtoIDC.
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
        Check split_frto_by_state_pred.
        (*
        destruct e as [e|e].
        {
            destruct H as [lc [ld [a0 [rc [rd [scs [H1r H2r]]]]]]].
            subst r. simpl in *.
            unfold flattened_rewrites_to in H0.
            destruct H0 as [ρ1 Hρ1].
            unfold flattened_rewrites_in_valuation_under_to in Hρ1.
            destruct Hρ1 as [Hρ1 [Hρ2 [Hρ3 Hρ4]]].
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
            apply satisfies_term_inv in Hρ1'.
            destruct Hρ1' as [lγ1 [Ht1 [HH1 HH2]]].
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
            unfold zip_with in HH2.
            repeat (rewrite Forall_cons in HH2).
            destruct HH2 as [HH2 [HH3 _]].
            apply satisfies_term_inv in HH2.
            destruct HH2 as [lγ [Hγ1 [HH4 HH5]]].
            simpl in HH4.
            destruct lγ as [|γ3 lγ].
            { simpl in HH4. inversion HH4. }
            destruct lγ as [|γ4 lγ].
            { simpl in HH4. inversion HH4. }
            destruct lγ>[|simpl in HH4; ltac1:(lia)].
            clear HH4.
            unfold zip_with in HH5.
            repeat (rewrite Forall_cons in HH5).
            destruct HH5 as [HH5 [HH6 _]].
            
            subst.
            apply satisfies_var_inv in HH6.
            

            (* do the same with Hρ2, but have fresh names *)
            assert (Hρ2': satisfies ρ1 t2 (t_term topSymbol [(t_term cseqSymbol [(rc);(t_over (ft_variable continuationVariable))]);rd])).
            {
                apply Hρ2.
            }
            clear Hρ2.
            apply satisfies_term_expr_inv in Hρ2'.
            destruct Hρ2' as [lγ2 [Ht2 [HH21 HH22]]].
            simpl in HH21.
            destruct lγ2 as [|γ4' lγ2].
            { simpl in HH21. inversion HH21. }
            destruct lγ2 as [|γ5 lγ2].
            { simpl in HH21. inversion HH21. }
            destruct lγ2>[|simpl in HH21; ltac1:(lia)].
            clear HH21.
            unfold zip_with in HH22.
            repeat (rewrite Forall_cons in HH22).
            destruct HH22 as [HH22 [HH23 _]].
            subst.
            apply satisfies_term_expr_inv in HH22.
            destruct HH22 as [lγ [Hγ4 [HH24 HH25]]].
            simpl in HH24. subst.
            destruct lγ as [|γ6 lγ].
            { simpl in HH24. inversion HH24. }
            destruct lγ as [|γ7 lγ].
            { simpl in HH24. inversion HH24. }
            destruct lγ>[|simpl in HH24; ltac1:(lia)].
            clear HH24.
            unfold zip_with in HH25.
            repeat (rewrite Forall_cons in HH25).
            destruct HH25 as [HH25 [HH26 _]].
            apply satisfies_var_expr_inv in HH26.
            inversion Hd1; subst; clear Hd1.
            inversion Hc1; subst; clear Hc1.

            rewrite HH6 in HH26. inversion HH26; subst; clear HH26.
            apply (f_equal prettify) in H0.
            rewrite (cancel prettify uglify') in H0.
            rewrite (cancel prettify uglify') in H0.
            subst γ7.

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
                { apply HH25. }
                { apply HH23. }
                { assumption. }
            }
            {
                apply IHH3w'; simpl in *.
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
            }
        }
        {
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
                    Search ctrl1.
                }
                *)
            }
            {

            }
        }
        *)
        admit.
        admit.
    }
Abort.
