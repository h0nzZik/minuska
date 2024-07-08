From Minuska Require Import
    prelude
    spec
    basic_properties
    lowlang
.


From Coq Require Import Logic.PropExtensionality.

Lemma vars_of_to_l2r_of_tob
    {Σ : StaticModel}
    (r : TermOver builtin_value)
    :
    vars_of_to_l2r (TermOverBuiltin_to_TermOverBoV r) = []
.
Proof.
    induction r; simpl.
    { reflexivity. }
    {
        revert H.
        induction l; intros H; simpl.
        { reflexivity. }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            rewrite IHl.
            unfold TermOverBuiltin_to_TermOverBoV  in *.
            rewrite H1.
            reflexivity.
        }
    }
Qed.


Lemma Expression2_evaluate_extensive_Some
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (t : Expression2)
    (gt : NondetValue -> TermOver builtin_value)
    :
    ρ1 ⊆ ρ2 ->
    Expression2_evaluate ρ1 t = Some gt ->
    Expression2_evaluate ρ2 t = Some gt.
Proof.
    intros Hρ1ρ2.
    revert gt.
    induction t; simpl; intros gt.
    { ltac1:(tauto). }
    {
        unfold vars_of in Hρ1ρ2.
        simpl in Hρ1ρ2.
        intros H.
        destruct (ρ1 !! x) eqn:Heq1, (ρ2 !! x) eqn:Heq2.
        {
            rewrite <- H.
            ltac1:(simplify_eq/=).
            f_equal.
            apply functional_extensionality.
            intros _.
            apply (lookup_weaken ρ1 ρ2 x) in Heq1.
            unfold Valuation2 in *.
            ltac1:(simplify_eq/=; congruence).
            { assumption. }
        }
        {
            ltac1:(exfalso).
            apply (lookup_weaken ρ1 ρ2 x) in Heq1.
            unfold Valuation2 in *.
            ltac1:(simplify_eq/=; congruence).
            { assumption. }
        }
        {
            inversion H.
        }
        {
            inversion H.
        }
    }
    {
        auto with nocore.
    }
    {
        do 2 (rewrite bind_Some).
        intros [x [Hx1 Hx2]].
        exists x.
        split>[|assumption].
        apply (IHt _ Hx1).
    }
    {
        do 2 (rewrite bind_Some).
        intros [x [Hx1 Hx2]].
        exists x.
        rewrite (IHt1 _ Hx1).
        split>[reflexivity|].
        rewrite bind_Some in Hx2.
        rewrite bind_Some.
        destruct Hx2 as [x' [Hx'1 Hx'2]].
        exists x'.
        rewrite (IHt2 _ Hx'1).
        split>[reflexivity|].
        exact Hx'2.
    }
    {
        do 2 (rewrite bind_Some).
        intros [x [Hx1 Hx2]].
        exists x.
        rewrite (IHt1 _ Hx1).
        simpl.
        split>[reflexivity|].

        rewrite bind_Some in Hx2.
        destruct Hx2 as [x' [Hx'1 Hx'2]].
        rewrite bind_Some.

        rewrite bind_Some in Hx'2.
        destruct Hx'2 as [x'' [Hx''1 Hx''2]].
        exists x'.
        rewrite (IHt2 _ Hx'1).
        simpl.
        split>[reflexivity|].

        rewrite bind_Some.
        exists x''.
        rewrite (IHt3 _ Hx''1).
        simpl.
        split>[reflexivity|].
        assumption.
    }
Qed.

Lemma Expression2_evaluate_Some_enough
    {Σ : StaticModel}
    (e : Expression2)
    (ρ : Valuation2)
    (g : NondetValue -> TermOver builtin_value)
:
    Expression2_evaluate ρ e = Some g ->
    vars_of e ⊆ vars_of ρ
.
Proof.
    revert ρ g.
    induction e; intros ρ g He; simpl in *;
        repeat (unfold vars_of in *; simpl in *; ());
        ltac1:(simplify_eq/=; simplify_option_eq; try set_solver).
    {
        unfold Valuation2 in *.
        rewrite singleton_subseteq_l.
        ltac1:(case_match;[|congruence]; simplify_eq/=).
        rewrite elem_of_dom. exists t. assumption.
    }
Qed.


Lemma Expression2_evaluate_Some_enough_inv
    {Σ : StaticModel}
    (e : Expression2)
    (ρ : Valuation2)
:
    vars_of e ⊆ vars_of ρ ->
    { g : _ & Expression2_evaluate ρ e = Some g }
.
Proof.
    revert ρ.
    induction e; intros ρ He; simpl in *;
        repeat (unfold vars_of in *; simpl in *; ());
        ltac1:(simplify_eq/=; simplify_option_eq; try set_solver).
    {
        exists (fun _ => e). reflexivity.
    }
    {
        rewrite singleton_subseteq_l in He.
        unfold Valuation2 in *.
        rewrite elem_of_dom in He.
        unfold is_Some in He.
        destruct (ρ !! x) eqn:Heqρx.
        {
            exists (fun _ => t). reflexivity.
        }
        {
            ltac1:(exfalso).
            destruct He as [x0 HContra].
            inversion HContra.
        }
    }
    {
        eexists. reflexivity.
    }
    {
        specialize (IHe ρ He).
        destruct IHe as [g Hg].
        exists (fun nv => builtin_unary_function_interp f (g nv) nv).
        rewrite bind_Some.
        exists g.
        split.
        { assumption. }
        { reflexivity. }
    }
    {
        rewrite union_subseteq in He.
        destruct He as [He1 He2].
        specialize (IHe1 ρ He1).
        specialize (IHe2 ρ He2).
        destruct IHe1 as [g1 Hg1].
        destruct IHe2 as [g2 Hg2].
        eexists.
        ltac1:(simp Expression2_evaluate).
        rewrite Hg1.
        rewrite bind_Some.
        eexists.
        split>[reflexivity|].
        rewrite Hg2.
        simpl. reflexivity.
    }

    {
        rewrite union_subseteq in He.
        rewrite union_subseteq in He.
        destruct He as [[He1 He2] He3].
        specialize (IHe1 ρ He1).
        specialize (IHe2 ρ He2).
        specialize (IHe3 ρ He3).
        destruct IHe1 as [g1 Hg1].
        destruct IHe2 as [g2 Hg2].
        destruct IHe3 as [g3 Hg3].
        eexists.
        ltac1:(simp Expression2_evaluate).
        rewrite Hg1.
        rewrite bind_Some.
        eexists.
        split>[reflexivity|].
        rewrite Hg2.
        simpl.
        rewrite bind_Some.
        eexists.
        rewrite Hg3.
        split; reflexivity.
    }
Qed.



Lemma Expression2Term_matches_enough
    {Σ : StaticModel}
    (t : TermOver Expression2)
    (ρ : Valuation2)
    (g : TermOver builtin_value)
    (nv : NondetValue)
:
    satisfies ρ (nv,g) t ->
    vars_of t ⊆ vars_of ρ
.
Proof.
    unfold satisfies; simpl.

    revert ρ g.
    induction t; intros ρ g HH; destruct g; simpl in *;
        ltac1:(simp sat2E in HH).
    {
        ltac1:(case_match;[|contradiction]).
        apply Expression2_evaluate_Some_enough in H.
        unfold vars_of; simpl.
        exact H.
    }
    {
        ltac1:(case_match;[|contradiction]).
        apply Expression2_evaluate_Some_enough in H.
        unfold vars_of; simpl.
        exact H.
    }
    {
        inversion HH.
    }
    {
        destruct HH as [Hs0s [Hl0l HH]].
        subst s0.
        rewrite Forall_forall in H.
        unfold Valuation2 in *.
        unfold TermOver in *.
        rewrite vars_of_t_term_e.
        rewrite elem_of_subseteq.
        intros x Hx.
        rewrite elem_of_union_list in Hx.
        destruct Hx as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [t [HX Ht]].
        subst X.
        specialize (H _ Ht).
        rewrite elem_of_list_lookup in Ht.
        destruct Ht as [i Hi].
        specialize (HH i).
        remember (l0 !! i) as Hl0i.
        destruct Hl0i.
        {
            specialize (HH t0 t ltac:(assumption) ltac:(reflexivity)).
            specialize (H _ _ HH).
            clear -H2X H.
            ltac1:(set_solver).
        }
        {
            symmetry in HeqHl0i.
            rewrite lookup_ge_None in HeqHl0i.
            apply lookup_lt_Some in Hi.
            unfold TermOver in *.
            ltac1:(lia).
        }
    }
Qed.



Lemma Expression2_evalute_total_1
    {Σ : StaticModel}
    (t : Expression2)
    (ρ : Valuation2)
    (e : NondetValue -> TermOver builtin_value)
:
    Expression2_evaluate ρ t = Some e ->
    ( vars_of t ⊆ vars_of ρ )
.
Proof.
    revert e.
    induction t; intros b H; cbn.
    {
        apply empty_subseteq.
    }
    {
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        unfold vars_of in Hx0; simpl in Hx0.
        rewrite elem_of_singleton in Hx0.
        subst x0.
        ltac1:(rewrite elem_of_dom).
        unfold is_Some.
        simpl in H.
        ltac1:(case_match;simplify_eq/=).
        exists t. assumption.
    }
    {
        ltac1:(set_solver).
    }
    {
        ltac1:(simplify_eq/=).
        rewrite bind_Some in H.
        destruct H as [x [H1x H2x]].
        ltac1:(simplify_eq/=).
        unfold vars_of; simpl.
        eapply IHt.
        apply H1x.
    }
    {
        unfold vars_of; simpl.
        rewrite union_subseteq.
        unfold vars_of in *; simpl in *.
        rewrite bind_Some in H.
        destruct H as[x [H1x H2x]].
        rewrite bind_Some in H2x.
        destruct H2x as [y [H1y H2y]].
        ltac1:(simplify_eq/=).
        ltac1:(naive_solver).
    }
    {
        unfold vars_of; simpl.
        rewrite union_subseteq.
        rewrite union_subseteq.
        simpl in H.
        rewrite bind_Some in H.
        destruct H as[x [H1x H2x]].
        rewrite bind_Some in H2x.
        destruct H2x as [y [H1y H2y]].
        rewrite bind_Some in H2y.
        destruct H2y as [z [H1z H2z]].
        ltac1:(simplify_eq/=).
        ltac1:(naive_solver).
    }
Qed.

Lemma TermOverExpression2_evalute_total_2
    {Σ : StaticModel}
    (t : TermOver Expression2)
    (ρ : Valuation2)
    (nv : NondetValue)
    :
    ( vars_of t ⊆ vars_of ρ ) ->
    {e : TermOver builtin_value & sat2E ρ e t nv}
.
Proof.
    revert ρ.
    ltac1:(induction t using TermOver_rect; intros ρ Hρ).
    {
        unfold vars_of in Hρ; simpl in Hρ.
        apply Expression2_evaluate_Some_enough_inv in Hρ.
        destruct Hρ as [g Hg].
        exists (g nv).
        ltac1:(simp sat2E).
        rewrite Hg.
        reflexivity.
    }
    {
        unfold Valuation2,TermOver in *.
        rewrite vars_of_t_term_e in Hρ.
        assert(X' : forall ρ0 x, x ∈ l -> vars_of x ⊆ vars_of ρ0 -> {e : TermOver' builtin_value & sat2E ρ0 e x nv}).
        {
            ltac1:(naive_solver).
        }
        clear X.
        specialize (X' ρ).
        assert(X'' : forall x, x ∈ l -> {e : TermOver' builtin_value & sat2E ρ e x nv}).
        {
            intros. apply X'. assumption.
            rewrite elem_of_subseteq in Hρ.
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            specialize (Hρ x0).
            apply Hρ.
            rewrite elem_of_union_list.
            exists (vars_of x).
            rewrite elem_of_list_fmap.
            split>[|assumption].
            exists x.
            split>[reflexivity|].
            exact H.
        }
        clear X'.
        remember (pfmap l (fun x pf => projT1 (X'' x pf))) as l'.
        exists (t_term b l').
        ltac1:(simp sat2E).
        split>[reflexivity|].
        subst l'.
        split.
        {
            rewrite length_pfmap. reflexivity.
        }
        {
            intros i t' φ' Hli Hpf.
            apply lookup_lt_Some in Hli as Hli'.
            unfold TermOver in *.
            rewrite <- (pflookup_spec l i Hli') in Hli.
            injection Hli as Hli.
            rewrite <- Hli.
            lazy_match! goal with
            | [|- sat2E _ _ (` ?p) _] => pose(p := $p)
            end.
            assert (HH2 := pfmap_lookup_Some_1 l (λ (x : TermOver' Expression2) (pf : x ∈ l), projT1 (X'' x pf)) i  t' Hpf).
            simpl in HH2.
            pose (Hp := proj2_sig p).
            pose (Xp := X'' (proj1_sig p) Hp).
            ltac1:(unfold Hp in Xp). clear Hp.
            ltac1:(fold p).
            assert (HH := projT2 Xp). simpl in HH.
            rewrite HH2.
            ltac1:(unfold Xp in HH).
            ltac1:(unfold p in HH).
            ltac1:(unfold p).
            ltac1:(replace (pfmap_lookup_Some_lt Hpf) with (Hli')).
            {
                exact HH.
            }
            {
                apply proof_irrelevance.
            }
        }
    }
Qed.


Lemma TermOverExpression2_satisfies_extensive
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (t : TermOver Expression2)
    (gt : TermOver builtin_value)
    (nv : NondetValue)
    :
    ρ1 ⊆ ρ2 ->
    satisfies ρ1 (nv,gt) t ->
    satisfies ρ2 (nv,gt) t
.
Proof.
    revert gt ρ1 ρ2.
    unfold TermOver in *.
    unfold Valuation2 in *.
    ltac1:(induction t using TermOver_rect; intros gt ρ1 ρ2 Hρ1ρ2).
    {
        unfold satisfies; simpl.
        destruct gt; ltac1:(simp sat2E).
        {
            intros HH.
            ltac1:(case_match;[|contradiction]).
            eapply Expression2_evaluate_extensive_Some in H.
            rewrite H.
            exact HH.
            exact Hρ1ρ2.
        }
        {
            intros HH.
            ltac1:(case_match;[|contradiction]).
            eapply Expression2_evaluate_extensive_Some in H.
            rewrite H.
            exact HH.
            exact Hρ1ρ2.
        }
    }
    {
        unfold satisfies; simpl.
        destruct gt; ltac1:(simp sat2E).
        intros [HH1 [HH2 HH3]].
        (repeat split); try assumption.
        intros i t' φ' H1 H2.
        specialize (HH3 i t' φ' H1 H2).
        eapply X.
        {
            rewrite elem_of_list_lookup. exists i. apply H1.
        }
        { apply Hρ1ρ2. }
        apply HH3.
    }
Qed.

Lemma TermOverExpression2_satisfies_injective
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver Expression2)
    (nv : NondetValue)
    (g1 g2 : TermOver builtin_value)
:
    satisfies ρ (nv,g1) t ->
    satisfies ρ (nv,g2) t ->
    g1 = g2
.
Proof.
    revert g1 g2.
    induction t; intros g1 g2 Hg1 Hg2; simpl in *.
    {
        unfold satisfies in *; simpl in *.
        ltac1:(simp sat2E in Hg1).
        ltac1:(simp sat2E in Hg2).
        ltac1:(repeat case_match; try contradiction).
        ltac1:(simplify_eq/=).
        reflexivity.
    }
    {
        unfold satisfies in *; simpl in *.
        rewrite Forall_forall in H.
        destruct g1,g2;
            ltac1:(simp sat2E in Hg1);
            ltac1:(simp sat2E in Hg2).
        { inversion Hg1. }
        { inversion Hg1. }
        { inversion Hg2. }
        ltac1:(destruct_and!; simplify_eq/=; f_equal).
        apply list_eq.
        intros i.
        destruct (l0!!i) eqn:Heql0i,(l1!!i) eqn:Heql1i, (l!!i) eqn:Heqli.
        {
            specialize (H3 i t0 t1 Heqli Heql1i).
            specialize (H6 i t t1 Heqli Heql0i).
            apply f_equal.
            eapply H.
            {
                rewrite elem_of_list_lookup. exists i. exact Heqli.
            }
            { assumption. }
            { assumption. }
        }
        {
            apply lookup_lt_Some in Heql0i.
            apply lookup_lt_Some in Heql1i.
            apply lookup_ge_None in Heqli.
            ltac1:(lia).
        }
        {
            apply lookup_lt_Some in Heql0i.
            apply lookup_lt_Some in Heqli.
            apply lookup_ge_None in Heql1i.
            ltac1:(lia).
        }
        {
            apply lookup_lt_Some in Heql0i.
            apply lookup_ge_None in Heql1i.
            apply lookup_ge_None in Heqli.
            ltac1:(lia).
        }
        {
            apply lookup_lt_Some in Heql1i.
            apply lookup_ge_None in Heql0i.
            ltac1:(lia).
        }
        {
            apply lookup_ge_None in Heql0i.
            apply lookup_lt_Some in Heql1i.
            apply lookup_ge_None in Heqli.
            ltac1:(lia).
        }
        {
            reflexivity.
        }
        {
            reflexivity.
        }
    }
Qed.

Lemma set_filter_pred_impl
    {A B : Type}
    {_EA : EqDecision A}
    {_Elo : ElemOf A B}
    {_Els : Elements A B}
    {_Em : Empty B}
    {_Sg : Singleton A B}
    {_IB : Intersection B}
    {_DB : Difference B}
    {_U : Union B}
    {_FS : @FinSet A B _Elo _Em _Sg _U _IB _DB _Els _EA}
    (P1 P2 : A -> Prop)
    {_DP1 : ∀ (x : A), Decision (P1 x)}
    {_DP2 : ∀ (x : A), Decision (P2 x)}
    (thing : B)
    :
    (forall (x : A), P1 x -> P2 x) ->
    @filter A B (set_filter) P1 _ thing ⊆ @filter A B (set_filter) P2 _ thing
.
Proof.
    intros Himpl.
    unfold subseteq.
    ltac1:(apply (proj2 (@elem_of_subseteq A B _ (@filter A B _ P1 _DP1 thing) (@filter A B _ P2 _DP2 thing)))).
    intros x.
    intros Hx.
    ltac1:(apply (proj1 (elem_of_filter P1 thing x)) in Hx).
    ltac1:(apply (proj2 (elem_of_filter P2 thing x))).
    ltac1:(naive_solver).
Qed.

(*
Lemma map_filter_pred_impl
    {K : Type}
    {M : Type → Type}
    {H0 : ∀ A : Type, Lookup K A (M A)}
    {A : Type} 
    {_PA : PartialAlter K A (M A)}
    {_ME : Empty (M A) }
    {_EA : EqDecision K}
    (P1 P2 : (K*A) -> Prop)
    {_DP1 : ∀ (x : K*A), Decision (P1 x)}
    {_DP2 : ∀ (x : K*A), Decision (P2 x)}
    (thing : M A)
    :
    (forall x, P1 x -> P2 x) ->
    (filter  P1 thing) ⊆ filter P2 thing
.
Proof.

    About map_filter.
    intros Himpl.
    ltac1:(rewrite map_subseteq_spec).
    intros i x Hx.
    Set Typeclasses Debug.
    Set Printing All.
    ltac1:(rewrite -> map_lookup_filter in Hx).
    Search filter lookup.
    Check (proj2 (@elem_of_subseteq _ _ _ (@filter _ _ _ P1 _DP1 thing) (@filter _ _ _ P2 _DP2 thing))).
    ltac1:(apply (proj2 (@elem_of_subseteq _ _ _ (@filter _ _ _ P1 _DP1 thing) (@filter _ _ _ P2 _DP2 thing)))).
    intros x.
    intros Hx.
    Locate elem_of_filter.
    Set Printing All.
    Check @elem_of_filter.
    ltac1:(apply (proj1 (elem_of_filter P1 thing x)) in Hx).
    ltac1:(apply (proj2 (elem_of_filter P2 thing x))).
    ltac1:(naive_solver).
Qed.
*)
Lemma Expression2_evalute_strip
    {Σ : StaticModel}
    (e : Expression2)
    (g : NondetValue -> TermOver builtin_value)
    (ρ : Valuation2)
:
    Expression2_evaluate ρ e = Some g ->
    Expression2_evaluate (filter (fun kv => kv.1 ∈ vars_of e) ρ) e = Some g
.
Proof.
    intros HH.
    apply Expression2_evaluate_Some_enough in HH as HH1.
    assert (HH2 : vars_of e ⊆ vars_of (filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ vars_of e) ρ)).
    {
        unfold Valuation2 in *.
        unfold vars_of; simpl.
        rewrite elem_of_subseteq.
        intros x Hx.
        ltac1:(rewrite elem_of_dom).
        unfold vars_of in HH1, Hx; simpl in HH1,Hx.
        rewrite elem_of_subseteq in HH1.
        specialize (HH1 _ Hx).
        ltac1:(rewrite elem_of_dom in HH1).
        destruct HH1 as [y Hy].
        exists y.
        unfold Valuation2 in *.
        apply map_lookup_filter_Some_2.
        exact Hy.
        simpl.
        apply Hx.
    }
    apply Expression2_evaluate_Some_enough_inv in HH2 as HH3.
    destruct HH3 as [g0 Hg0].
    eapply Expression2_evaluate_extensive_Some with (ρ2 := ρ) in Hg0 as H1g0.
    {
        assert (g = g0) by ltac1:(congruence).
        subst g0.
        apply Hg0.
    }
    {
        unfold Valuation2 in *.
        apply map_filter_subseteq.
    }
Qed.

Lemma vars_of_t_over_expr
    {Σ : StaticModel}
    (e : Expression2)
    :
    (vars_of ((t_over e):(TermOver Expression2))) = vars_of e
.
Proof.
    reflexivity.
Qed.

Lemma TermOverExpression2_satisfies_strip
    {Σ : StaticModel}
    (t : TermOver Expression2)
    (g : TermOver builtin_value)
    (ρ : Valuation2)
    (nv : NondetValue)
:
    satisfies ρ (nv,g) t ->
    satisfies (filter (fun kv => kv.1 ∈ vars_of t) ρ) (nv,g) t
.
Proof.
    revert ρ g.
    ltac1:(induction t using TermOver_rect; intros ρ g HH).
    {
        unfold satisfies in *; simpl in *.
        ltac1:(simp sat2E in HH).
        ltac1:(simp sat2E).
        ltac1:(repeat case_match; try contradiction).
        {
            apply Expression2_evalute_strip in H.
            rewrite vars_of_t_over_expr in H0.
            ltac1:(simplify_eq/=).
            reflexivity.
        }
        {
            apply Expression2_evalute_strip in H.
            rewrite vars_of_t_over_expr in H0.
            ltac1:(simplify_eq/=).
        }
    }
    {
        unfold satisfies in *; simpl in *.
        destruct g;
            ltac1:(simp sat2E in HH).
        { destruct HH. }
        ltac1:(simp sat2E).
        ltac1:(destruct_and!; (repeat split); simplify_eq/=; try congruence).
        intros.
        eapply TermOverExpression2_satisfies_extensive>[|eapply X].
        {
            unfold TermOver, Valuation2 in *.
            ltac1:(rewrite map_subseteq_spec).
            intros i0 x Hx.
            rewrite map_lookup_filter in Hx.
            rewrite map_lookup_filter.
            ltac1:(simplify_option_eq).
            reflexivity.
            ltac1:(exfalso).
            rewrite vars_of_t_term_e in H3.
            rewrite elem_of_union_list in H3.
            apply H3. clear H3.
            exists (vars_of φ').
            split>[|assumption].
            rewrite elem_of_list_fmap.
            exists φ'.
            split>[reflexivity|].
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        {
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        {
            eapply H2.
            apply pf1.
            apply pf2.
        }
    }
Qed.

Lemma TermOverBoV_satisfies_extensive
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (t : TermOver BuiltinOrVar)
    (gt : TermOver builtin_value)
    :
    ρ1 ⊆ ρ2 ->
    satisfies ρ1 gt t ->
    satisfies ρ2 gt t
.
Proof.
    revert gt ρ1 ρ2.
    unfold TermOver in *.
    unfold Valuation2 in *.
    ltac1:(induction t using TermOver_rect; intros gt ρ1 ρ2 Hρ1ρ2).
    {
        unfold satisfies; simpl.
        destruct gt,a ; ltac1:(simp sat2B); simpl.
        {
            intros HH.
            unfold TermOver in *.
            ltac1:(rewrite map_subseteq_spec in Hρ1ρ2).
            ltac1:(naive_solver).
        }
        {
            intros HH.
            ltac1:(rewrite map_subseteq_spec in Hρ1ρ2).
            ltac1:(naive_solver).
        }
    }
    {
        unfold satisfies; simpl.
        destruct gt; ltac1:(simp sat2B).
        intros [HH1 [HH2 HH3]].
        (repeat split); try assumption.
        intros i t' φ' H1 H2.
        specialize (HH3 i t' φ' H1 H2).
        eapply X.
        {
            rewrite elem_of_list_lookup. exists i. apply H1.
        }
        { apply Hρ1ρ2. }
        apply HH3.
    }
Qed.


Lemma TermOverBoV_satisfies_strip
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    (g : TermOver builtin_value)
    (ρ : Valuation2)
:
    satisfies ρ g t ->
    satisfies (filter (fun kv => kv.1 ∈ vars_of t) ρ) g t
.
Proof.
    revert ρ g.
    ltac1:(induction t using TermOver_rect; intros ρ g HH).
    {
        unfold satisfies in *; simpl in *.
        ltac1:(simp sat2B in HH).
        ltac1:(simp sat2B).
        unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar in *.
        ltac1:(repeat case_match; try congruence).
        unfold Valuation2 in *.
        rewrite map_lookup_filter.
        rewrite HH.
        simpl.
        ltac1:(simplify_option_eq).
        reflexivity.
        ltac1:(exfalso).
        apply H. clear H.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        rewrite elem_of_singleton.
        reflexivity.
    }
    {
        unfold satisfies in *; simpl in *.
        destruct g;
            ltac1:(simp sat2B in HH).
        { destruct HH. }
        ltac1:(simp sat2B).
        ltac1:(destruct_and!; (repeat split); simplify_eq/=; try congruence).
        intros.
        eapply TermOverBoV_satisfies_extensive>[|eapply X].
        {
            unfold TermOver, Valuation2 in *.
            ltac1:(rewrite map_subseteq_spec).
            intros i0 x Hx.
            rewrite map_lookup_filter in Hx.
            rewrite map_lookup_filter.
            ltac1:(simplify_option_eq).
            reflexivity.
            ltac1:(exfalso).
            rewrite vars_of_t_term in H3.
            rewrite elem_of_union_list in H3.
            apply H3. clear H3.
            exists (vars_of φ').
            split>[|assumption].
            rewrite elem_of_list_fmap.
            exists φ'.
            split>[reflexivity|].
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        {
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        {
            eapply H2.
            apply pf1.
            apply pf2.
        }
    }
Qed.

Lemma SideCondition_satisfies_strip
    {Σ : StaticModel}
    (c : SideCondition2)
    (ρ : Valuation2)
    (nv : NondetValue)
:
    satisfies ρ nv c ->
    satisfies (filter (fun kv => kv.1 ∈ vars_of c) ρ) nv c
.
Proof.
    unfold satisfies; simpl.
    intros HH.
    destruct (Expression2_evaluate ρ (sc_left c)) eqn:HH1>[|ltac1:(contradiction)].
    destruct (Expression2_evaluate ρ (sc_right c)) eqn:HH2>[|ltac1:(contradiction)].
    unfold is_true in *.
    unfold isSome in *.
    (destruct (Expression2_evaluate ρ (sc_left c)) as [g1|] eqn:Heq1)>[|ltac1:(congruence)].
    symmetry in HH1.
    eapply Expression2_evalute_strip in Heq1 as HH1'.
    eapply Expression2_evalute_strip in HH2 as HH2'.
    clear HH2.
    eapply Expression2_evaluate_extensive_Some in HH1' as HH1''.
    rewrite HH1''. clear HH1''.
    eapply Expression2_evaluate_extensive_Some in HH2' as HH2''.
    rewrite HH2''. clear HH2''.
    (repeat split).
    {
        ltac1:(simplify_eq/=).
        assumption.
    }
    {
        ltac1:(rewrite map_subseteq_spec).
        intros i x Hix.
        ltac1:(rewrite map_lookup_filter in Hix).
        rewrite bind_Some in Hix.
        destruct Hix as [x0 [H1x0 H2x0]].
        ltac1:(simplify_option_eq).
        ltac1:(rewrite map_lookup_filter bind_Some).
        exists x.
        split>[assumption|].
        ltac1:(simplify_option_eq).
        reflexivity.
        ltac1:(contradiction H1). clear H1.
        unfold vars_of; simpl.
        ltac1:(set_solver).
    }
    {
        ltac1:(rewrite map_subseteq_spec).
        intros i x Hix.
        ltac1:(rewrite map_lookup_filter in Hix).
        rewrite bind_Some in Hix.
        destruct Hix as [x0 [H1x0 H2x0]].
        ltac1:(simplify_option_eq).
        ltac1:(rewrite map_lookup_filter bind_Some).
        exists x.
        split>[assumption|].
        ltac1:(simplify_option_eq).
        reflexivity.
        ltac1:(contradiction H1). clear H1.
        unfold vars_of; simpl.
        ltac1:(set_solver).
    }
Qed.

Lemma SideCondition_satisfies_extensive
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (c : SideCondition2)
    (nv : NondetValue)
    :
    ρ1 ⊆ ρ2 ->
    satisfies ρ1 nv c ->
    satisfies ρ2 nv c
.
Proof.
    intros Hrhos.
    unfold satisfies; simpl.
    intros HH.
    destruct (Expression2_evaluate ρ1 (sc_left c) ) eqn:HH1>[|ltac1:(contradiction)].
    destruct (Expression2_evaluate ρ1 (sc_right c) ) eqn:HH2>[|ltac1:(contradiction)].
    
    unfold is_true in *.
    unfold isSome in *.
    (destruct (Expression2_evaluate ρ1 (sc_left c)) as [g1|] eqn:Heq1)>[|ltac1:(congruence)].
    symmetry in HH1.
    eapply Expression2_evaluate_extensive_Some in Heq1 as Heq1'.
    rewrite Heq1'.
    eapply Expression2_evaluate_extensive_Some in HH2 as HH2'.
    rewrite HH2'.
    ltac1:(simplify_eq/=).
    assumption.
    assumption.
    assumption.
Qed.


Lemma satisfies_term_bov_inv
    {Σ : StaticModel}
    (ρ : Valuation2)
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
        intros H. exists [].
        unfold satisfies in H; simpl in H.
        destruct γ;
            ltac1:(simp sat2B in H).
        { destruct H. }
        {
            destruct H as [H1 [H2 H3]].
            destruct l.
            {
                subst s0.
                (repeat split).
                intros.
                rewrite lookup_nil in H.
                inversion H.
            }
            {
                simpl in H2. inversion H2.
            }
        }
    }
    {
        intros H.
        unfold satisfies in H; simpl in H.
        destruct γ; ltac1:(simp sat2B in H).
        { destruct H. }
        destruct H as [H1 [H2 H3]].
        destruct (analyze_list_from_end l0) as [He|He].
        {
            subst l0.
            rewrite app_length in H2.
            simpl in H2.
            ltac1:(lia).
        }
        destruct He as [l' [x' Hl0]].
        subst l0.
        do 2 (rewrite app_length in H2).
        simpl in H2.
        assert (length l' = length l) by ltac1:(lia).
        clear H2.
        specialize (H3 (length l) x' x) as H3'.
        unfold TermOver in *; simpl in *.
        rewrite lookup_app_r in H3'>[|ltac1:(lia)].
        rewrite lookup_app_r in H3'>[|ltac1:(lia)].
        rewrite Nat.sub_diag in H3'.
        rewrite H in H3'.
        rewrite Nat.sub_diag in H3'.
        specialize (H3' erefl erefl).
        unfold satisfies in IHl; simpl in IHl.
        specialize (IHl (t_term s l')).
        ltac1:(ospecialize (IHl _)).
        {
            ltac1:(simp sat2B).
            split>[reflexivity|].
            split>[ltac1:(lia)|].
            intros.
            apply H3 with (i := i).
            {
                rewrite lookup_app_l.
                assumption.
                apply lookup_lt_Some in pf1.
                assumption.
            }
            {
                rewrite lookup_app_l.
                assumption.
                apply lookup_lt_Some in pf2.
                assumption.
            }
        }
        destruct IHl as [lγ Hlγ].
        destruct Hlγ as [[HH1 HH2] HH3].
        inversion HH1; subst; clear HH1.
        exists (lγ ++ [x']).
        (repeat split).
        {
            do 2 (rewrite app_length).
            simpl.
            ltac1:(lia).
        }
        {
            intros.
            destruct (decide (i < length l)).
            {
                rewrite lookup_app_l in H0>[|ltac1:(lia)].
                rewrite lookup_app_l in H1>[|ltac1:(lia)].
                eapply HH3.
                apply H0.
                apply H1.
            }
            {
                unfold satisfies; simpl.
                eapply H3.
                apply H1.
                apply H0.   
            }
        }
    }
Qed.


Lemma satisfies_term_expr_inv
    {Σ : StaticModel}
    (ρ : Valuation2)
    (nv : NondetValue)
    (γ : TermOver builtin_value)
    (s : symbol)
    (l : list (TermOver Expression2))
    :
    satisfies ρ (nv,γ) (t_term s l) ->
    { lγ : list (TermOver builtin_value) &
        ((γ = (t_term s lγ)) *
        (length l = length lγ) *
        ( forall (i : nat) γ e,
            lγ !! i = Some γ ->
            l !! i = Some e ->
            satisfies ρ (nv,γ) e
        )
        )%type
    }
.
Proof.
    revert γ.
    induction l using rev_ind_T; intros γ.
    {
        intros H. exists [].
        unfold satisfies in H; simpl in H.
        destruct γ;
            ltac1:(simp sat2E in H).
        { destruct H. }
        {
            destruct H as [H1 [H2 H3]].
            destruct l.
            {
                subst s0.
                (repeat split).
                intros.
                rewrite lookup_nil in H.
                inversion H.
            }
            {
                simpl in H2. inversion H2.
            }
        }
    }
    {
        intros H.
        unfold satisfies in H; simpl in H.
        destruct γ; ltac1:(simp sat2E in H).
        { destruct H. }
        destruct H as [H1 [H2 H3]].
        destruct (analyze_list_from_end l0) as [He|He].
        {
            subst l0.
            rewrite app_length in H2.
            simpl in H2.
            ltac1:(lia).
        }
        destruct He as [l' [x' Hl0]].
        subst l0.
        do 2 (rewrite app_length in H2).
        simpl in H2.
        assert (length l' = length l) by ltac1:(lia).
        clear H2.
        specialize (H3 (length l) x' x) as H3'.
        unfold TermOver in *; simpl in *.
        rewrite lookup_app_r in H3'>[|ltac1:(lia)].
        rewrite lookup_app_r in H3'>[|ltac1:(lia)].
        rewrite Nat.sub_diag in H3'.
        rewrite H in H3'.
        rewrite Nat.sub_diag in H3'.
        specialize (H3' erefl erefl).
        unfold satisfies in IHl; simpl in IHl.
        specialize (IHl (t_term s l')).
        ltac1:(ospecialize (IHl _)).
        {
            ltac1:(simp sat2E).
            split>[reflexivity|].
            split>[ltac1:(lia)|].
            intros.
            apply H3 with (i := i).
            {
                rewrite lookup_app_l.
                assumption.
                apply lookup_lt_Some in pf1.
                assumption.
            }
            {
                rewrite lookup_app_l.
                assumption.
                apply lookup_lt_Some in pf2.
                assumption.
            }
        }
        destruct IHl as [lγ Hlγ].
        destruct Hlγ as [[HH1 HH2] HH3].
        inversion HH1; subst; clear HH1.
        exists (lγ ++ [x']).
        (repeat split).
        {
            do 2 (rewrite app_length).
            simpl.
            ltac1:(lia).
        }
        {
            intros.
            destruct (decide (i < length l)).
            {
                rewrite lookup_app_l in H0>[|ltac1:(lia)].
                rewrite lookup_app_l in H1>[|ltac1:(lia)].
                eapply HH3.
                apply H0.
                apply H1.
            }
            {
                unfold satisfies; simpl.
                eapply H3.
                apply H1.
                apply H0.   
            }
        }
    }
Qed.
