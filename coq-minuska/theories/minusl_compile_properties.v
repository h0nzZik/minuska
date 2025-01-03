From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
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
            rewrite length_app in HH. simpl in HH.
            rewrite length_app in HH. simpl in HH.
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
            rewrite length_fmap in H'inφ.
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
            rewrite length_app in H'inφ.
            rewrite length_app in H'inφ.
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

(*
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
*)
(*
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
*)


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

Equations? TermOverBoV_eval
    {Σ : StaticModel}
    (ρ : Valuation2)
    (φ : TermOver BuiltinOrVar)
    (pf : vars_of φ ⊆ vars_of ρ)
    : TermOver builtin_value
    by wf (TermOver_size φ) lt
:=

    TermOverBoV_eval ρ (t_over (bov_builtin b)) pf := t_over b
    ;

    TermOverBoV_eval ρ (t_over (bov_variable x)) pf with (inspect (ρ !! x)) => {
        | (@exist _ _ (Some t) pf') := t;
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
            unfold Valuation2 in *;
            rewrite elem_of_dom in pf;
            ltac1:(rewrite pf' in pf);
            eapply is_Some_None;
            apply pf
        ).
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
    (ρ : Valuation2)
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
        unfold satisfies in HH; simpl in HH.
        ltac1:(simp sat2B in HH).
        destruct a; simpl in HH; subst.
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        rewrite elem_of_subseteq.
        intros x' Hx'.
        rewrite elem_of_singleton in Hx'.
        subst x'.
        unfold Valuation2 in *.
        rewrite elem_of_dom.
        exists (c).
        exact HH.
    }
    {
        unfold satisfies in HH; simpl in HH.
        destruct c; ltac1:(simp sat2B in HH).
        { destruct HH. }
        destruct HH as [HH1 [HH2 HH3]].
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
        
        subst s0.
        destruct (l0 !! length l1) eqn:Heq.
        {
            specialize (HH3 (length l1) t y).
            rewrite lookup_app_r in HH3>[|unfold TermOver in *; ltac1:(lia)].
            rewrite Nat.sub_diag in HH3. simpl in HH3.
            specialize (HH3 erefl Heq).
            specialize (H2 _ _ HH3).
            clear -H2 Hx.
            ltac1:(set_solver).
        }
        {
            apply lookup_ge_None in Heq.
            rewrite length_app in HH2. simpl in HH2.
            unfold TermOver in *.
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
            unfold vars_of; simpl.
            unfold vars_of; simpl.
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


Lemma in_compile_inv
    {Σ : StaticModel}
    (Act : Set)
    {_aD : EqDecision Act}
    (D: MinusL_LangDef Act)
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable)
    (r : RewritingRule2 Act)
:
  r
∈ compile invisible_act topSymbol cseqSymbol holeSymbol
  continuationVariable D ->
  (
    (
        { lc : TermOver BuiltinOrVar &
        { ld : TermOver BuiltinOrVar &
        { a : Act &
        { rc : TermOver Expression2 &
        { rd : TermOver Expression2 &
        { scs : list SideCondition2 &
            mld_rewrite Act lc ld a rc rd scs ∈ mlld_decls Act D /\
            r =
            {|
                r_from :=
                t_term topSymbol
                [t_term cseqSymbol
                [lc; t_over (bov_variable continuationVariable)];
                ld];
                r_to :=
                t_term topSymbol
                [t_term cseqSymbol
                [rc; t_over (e_variable continuationVariable)];
                rd];
                r_scs := scs;
                r_act := a
            |}
        }}}}}}
    ) + (
        { c : _ &
        { h : variable &
        { scs : list SideCondition2 &
        mld_context Act c h scs ∈ mlld_decls Act D /\
        (
            r = ctx_heat invisible_act topSymbol cseqSymbol holeSymbol
                (fresh
                (h
                :: vars_of_to_l2r c ++
                elements (vars_of scs) ++
                elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D)))))
                (fresh
                (h
                :: fresh
                (h
                :: vars_of_to_l2r c ++
                elements (vars_of scs) ++
                elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D))))
                :: vars_of_to_l2r c ++
                elements (vars_of scs) ++
                elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D)))))
                (MinusL_isValue Act D)
                (MinusL_isNonValue Act D)
                c h
                scs
            \/
            r =
            ctx_cool invisible_act topSymbol cseqSymbol holeSymbol
            (fresh
            (h
            :: vars_of_to_l2r c ++
            elements (vars_of scs) ++
            elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D)))))
            (fresh
            (h
            :: fresh
            (h
            :: vars_of_to_l2r c ++
            elements (vars_of scs) ++
            elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D))))
            :: vars_of_to_l2r c ++
            elements (vars_of scs) ++
            elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D)))))
            (MinusL_isValue Act D)
            (MinusL_isNonValue Act D)
            c
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

(*
Fixpoint frto_all_nonlast_states_satisfy
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory2 Act)
    (P : TermOver builtin_value -> Prop)
    (x y : TermOver builtin_value)
    (w : list Act)
    (r : rewrites_to_thy Γ x w y)
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
Abort.

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
Abort.

*)
            