
From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    spec_interpreter
    valuation_merge
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Logic.FunctionalExtensionality.

Fixpoint try_match_new
    {Σ : StaticModel}
    (g : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    : option Valuation2
:=
    match φ with
    | t_over (bov_variable x) => Some (<[x := g]>∅)
    | t_over (bov_builtin b) =>
        match g with
        | t_over b' =>
            match (decide (b = b')) with
            | left _ => Some ∅
            | right _ => None
            end
        | t_term _ _ => None
        end
    | t_term s l =>
        match g with
        | t_over _ => None
        | t_term s' l' =>
            match (decide (s = s')) with
            | left _ =>
                match (decide (length l = length l')) with
                | left _ =>
                    let tmp := zip_with try_match_new l' l in
                    Valuation2_merge_olist tmp
                | right _ => None
                end
            | right _ => None
            end
        end
    end
.

(* TODO move *)
Fixpoint TermOver_collect
    {Σ : StaticModel}
    {A : Type}
    (t : TermOver (option A))
    : option (TermOver A)
:=
    match t with
    | t_over None => None
    | t_over (Some x) => Some (t_over x)
    | t_term s l =>
        l' ← list_collect (TermOver_collect <$> l);
        Some (t_term s l')
    end
.

Fixpoint TermOver'_join
    {T A : Type}
    (t : @TermOver' T (@TermOver' T A))
    : @TermOver' T A
:=
    match t with
    | t_over x => x
    | t_term s l =>
        t_term s (TermOver'_join <$> l)
    end
.

Definition Expression2_evaluate_nv
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (nv : NondetValue)
    (t : Expression2)
:=
    gt ← Expression2_evaluate program ρ t;
    Some (gt nv)
.

Definition eval_et
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (nv : NondetValue)
    (et : TermOver Expression2)
    : option (TermOver builtin_value)
:=
    x ← TermOver'_option_map (Expression2_evaluate_nv program ρ nv) et;
    Some (TermOver'_join x)
.

Lemma eval_et_Some_val
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (nv : NondetValue)
    (et : TermOver Expression2)
    (t : TermOver builtin_value)
:
    eval_et program ρ nv et = Some t ->
    vars_of et ⊆ vars_of ρ 
.
Proof.
    revert t.
    unfold eval_et, Expression2_evaluate_nv.
    induction et; intros t Ht; simpl in *.
    {
        rewrite bind_Some in Ht.
        destruct Ht as [x [H1x H2x]].
        rewrite fmap_Some in H1x.
        destruct H1x as [y [H1y H2y]].
        rewrite bind_Some in H1y.
        destruct H1y as [z [H1z H2z]].
        subst x.
        apply (inj Some) in H2z.
        subst y.
        apply (inj Some) in H2x.
        subst t.
        apply Expression2_evaluate_total_1 in H1z.
        apply H1z.
    }
    {
        rewrite bind_Some in Ht.
        destruct Ht as [x [H1x H2x]].
        apply (inj Some) in H2x.
        subst t.
        rewrite fmap_Some in H1x.
        destruct H1x as [y [H1y H2y]].
        subst x.
        rewrite vars_of_t_term_e.
        clear s.
        revert y H1y H.
        induction l; intros y H1y H.
        {
            simpl in *.
            ltac1:(clear; set_solver).
        }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            simpl in *.
            rewrite bind_Some in H1y.
            destruct H1y as [z [H1z H2z]].
            rewrite bind_Some in H2z.
            destruct H2z as [u [H1u H2u]].
            apply (inj Some) in H2u.
            subst y.
            simpl in *.
            specialize (IHl _ H1u H2).
            rewrite union_subseteq.
            split>[|clear -IHl; ltac1:(set_solver)].
            specialize (H1 (TermOver'_join z)).
            apply H1.
            rewrite bind_Some.
            exists z.
            split>[|reflexivity].
            exact H1z.
        }
    }
Qed.

Definition try_match_lhs_with_sc
    {Σ : StaticModel}
    {Act : Set}
    (program : ProgramT)
    (g : TermOver builtin_value)
    (nv : NondetValue)
    (r : RewritingRule2 Act)
    : option (Valuation2*(TermOver builtin_value))
:=
    ρ ← try_match_new g (r_from r);
    if SideCondition_evaluate program ρ nv (r_scs r)
    then (
        match (eval_et program ρ nv (r_to r)) with
        | None => None
        | Some g' => Some (ρ, g')
        end
    )
    else None
.

Definition thy_lhs_match_one
    {Σ : StaticModel}
    {Act : Set}
    (e : TermOver builtin_value)
    (nv : NondetValue)
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    : option (RewritingRule2 Act * Valuation2 * (TermOver builtin_value) * nat)%type
:=
    let froms : list (TermOver BuiltinOrVar)
        := r_from <$> Γ
    in
    let vs : list (option (Valuation2 * (TermOver builtin_value)))
        := (try_match_lhs_with_sc program e nv) <$> Γ
    in
    let found : option (nat * option (Valuation2*(TermOver builtin_value)))
        := list_find isSome vs
    in
    nov ← found;
    let idx : nat := nov.1 in
    let ov : option (Valuation2 * (TermOver builtin_value)) := nov.2 in
    v ← ov;
    r ← Γ !! idx;
    Some (r, v.1, v.2, idx)
.


Definition naive_interpreter_ext
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    (nv : NondetValue)
    (e : TermOver builtin_value)
    : option ((TermOver builtin_value)*nat)
:=
    let oρ : option ((RewritingRule2 Act)*Valuation2*(TermOver builtin_value)*nat)
        := thy_lhs_match_one e nv Γ program in
    match oρ with
    | None => None
    | Some (r,ρ,g',idx) =>
        Some (g',idx)
    end
.

Definition naive_interpreter
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    (nv : NondetValue)
    (e : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    ei ← naive_interpreter_ext Γ program nv e;
    Some (ei.1)
.



Lemma try_match_new_complete
    {Σ : StaticModel}
    :
    ∀ (a : (TermOver builtin_value)) (b : TermOver BuiltinOrVar) (ρ : Valuation2),
        satisfies ρ a b ->
        { ρ' : Valuation2 &
            vars_of ρ' = vars_of b /\
            ρ' ⊆ ρ /\
            try_match_new a b = Some ρ' 
        }
.
Proof.
    intros a.
    ltac1:(induction a using TermOver_rect); intros b' ρ Hb'; destruct b'.
    {
        simpl in *.
        unfold satisfies in Hb'; simpl in Hb'.
        ltac1:(simp sat2B in Hb').
        destruct a0; simpl in *.
        {
            unfold Valuation2 in *.
            inversion Hb'; subst; clear Hb'.
            exists ∅.
            (repeat split).
            { apply map_empty_subseteq. }
            {
                destruct (decide (b = b)); ltac1:(congruence).
            }
        }
        {
            exists (<[x:=t_over a]> ∅).
            (repeat split).
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold Valuation2 in *.
                rewrite dom_insert_L.
                ltac1:(set_solver).
            }
            {
                unfold Valuation2 in *.
                apply insert_subseteq_l.
                { assumption. }
                { apply map_empty_subseteq. }
            }
        }
    }
    {
        simpl in *.
        unfold satisfies in Hb'; simpl in Hb'.
        ltac1:(simp sat2B in Hb').
        destruct Hb'.
    }
    {
        simpl in *.
        unfold satisfies in Hb'; simpl in Hb'.
        ltac1:(simp sat2B in Hb').
        destruct a.
        {
            simpl in *.
            inversion Hb'.
        }
        {
            simpl in *.
            exists (<[x:=t_term b l]> ∅).
            (repeat split).
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold Valuation2 in *.
                rewrite dom_insert_L.
                ltac1:(clear; set_solver).
            }
            {
                unfold Valuation2 in *.
                apply insert_subseteq_l.
                { assumption. }
                { apply map_empty_subseteq. }
            }
        }
    }
    {
        unfold satisfies in Hb'; simpl in Hb'.
        ltac1:(simp sat2B in Hb').
        destruct Hb' as [H1 [H2 H3]].
        subst b.
        unfold try_match_new. fold (@try_match_new Σ).

        revert l0 H2 H3 X.
        induction l; intros l0 H2 H3 X.
        {
            destruct l0.
            {
                simpl in *.
                exists ∅.
                unfold Valuation2 in *.
                (repeat split).
                { apply map_empty_subseteq. }
                {
                    destruct (decide (s = s)); ltac1:(congruence).
                }
            }
            {
                simpl in *. inversion H2.
            }
        }
        {
            destruct l0; simpl in *.
            {
                ltac1:(lia).
            }
            {
                specialize (IHl l0 ltac:(lia)).
                ltac1:(ospecialize (IHl _ _)).
                {
                    intros. apply H3 with (i := S i); simpl in *; assumption.
                }
                {
                    intros.
                    apply X.
                    { rewrite elem_of_cons. right. assumption. }
                    { assumption. }
                }
                destruct IHl as [ρ'1 [HH1 [HH2 HH3]]].
                destruct (decide (s = s))>[|ltac1:(congruence)].
                destruct (decide (length l0 = length l))>[|ltac1:(lia)].
                clear e0.
                apply Valuation2_merge_olist_vars_of in HH3 as HH3'.
                rewrite HH3.
                clear HH3.
                
                specialize (X a ltac:(set_solver)).
                specialize (H3 0 a t erefl erefl).
                specialize (X _ _ H3).
                destruct X as [ρ' [H4 [H5 H6]]].
                rewrite H6. simpl. clear H6. simpl.
                unfold Valuation2_merge_with.
                assert (Hcompat: Valuation2_compatible_with ρ' ρ'1 = true).
                {
                    eapply Valuation2_compatible_with_bound.
                    { apply H5. }
                    { apply HH2. }
                }
                rewrite Hcompat.
                simpl.
                exists ((merge Valuation2_use_left ρ' ρ'1)).
                (repeat split).
                {
                    unfold Valuation2 in *.
                    ltac1:(rewrite vars_of_t_term).
                    rewrite fmap_cons.
                    rewrite union_list_cons.
                    unfold TermOver,Valuation2 in *.
                    unfold vars_of; simpl.
                    ltac1:(rewrite dom_merge_use_left).
                    unfold vars_of in HH1; simpl in HH1.
                    rewrite HH1.
                    (*fold ((@vars_of (@TermOver' (@symbol Σ) (@BuiltinOrVar Σ)) (@variable Σ) _ (@variable_countable variable variables )) <$> l0).*)                    Check vars_of_t_term.
                    (*ltac1:(rewrite vars_of_t_term).*)
                    unfold vars_of in H4; simpl in H4.
                    rewrite H4.
                    clear.
                    ltac1:(set_solver).
                }
                {
                    apply merge_use_left_below.
                    { assumption. }
                    { assumption. }
                }
                {
                    ltac1:(repeat case_match).
                    { reflexivity. }
                    { ltac1:(lia). }
                }
            }
        }
    }
Qed.

Lemma try_match_new_correct {Σ : StaticModel} :
    ∀ (a : TermOver builtin_value) (b : TermOver BuiltinOrVar) (ρ : Valuation2),
        try_match_new a b = Some ρ ->
        satisfies ρ a b
.
Proof.
    intros a b.
    revert a.
    ltac1:(induction b using TermOver_rect); intros g ρ HH;
        destruct g.
    {
        simpl in *.
        ltac1:(repeat case_match; simpl in *; simplify_eq/=).
        { unfold satisfies; simpl. ltac1:(simp sat2B). simpl. reflexivity. }
        {
            unfold satisfies; simpl.
            ltac1:(simp sat2B).
            simpl.
            unfold Valuation2 in *.
            apply lookup_insert.
        }
    }
    {
        simpl in *.
        destruct a; simpl in *.
        { inversion HH. }
        {
            ltac1:(simplify_eq/=).
            unfold satisfies; simpl.
            ltac1:(simp sat2B).
            simpl.
            unfold Valuation2 in *.
            apply lookup_insert.
        }
    }
    {
        simpl in *. inversion HH.
    }
    {
        simpl in *.
        ltac1:(repeat case_match); subst.
        {
            unfold satisfies; simpl in *.
            ltac1:(simp sat2B).
            split>[reflexivity|].
            split>[ltac1:(lia)|].
            intros i t' φ' HHφ' HHt'.
            clear H0.
            apply take_drop_middle in HHφ' as tdm1.
            apply take_drop_middle in HHt' as tdm2.
            rewrite <- tdm1 in HH.
            rewrite <- tdm2 in HH.
            rewrite zip_with_app in HH.
            {

                rewrite <- zip_with_take in HH.
                simpl in HH.
                apply Valuation2_merge_olist_inv with (i := i) in HH as HH''.
                destruct HH'' as [ρ' HHρ'].
                eapply TermOverBoV_satisfies_extensive>[|apply X].
                { 
                    eapply Valuation2_merge_olist_correct in HH as HH'.
                    apply HH'.
                    apply HHρ'.
                }
                { rewrite elem_of_list_lookup. exists i. assumption. }
                
                simpl in HHρ'.
                rewrite lookup_app_r in HHρ'.
                rewrite length_take in HHρ'.
                rewrite length_zip_with in HHρ'.
                unfold Valuation2,TermOver in *.
                rewrite e0 in HHρ'.
                unfold Valuation2,TermOver in *.
                rewrite Nat.min_id in HHρ'.
                assert (Hm : i `min` length l0 = i).
                {
                    apply lookup_lt_Some in HHφ'.
                    ltac1:(lia).
                }
                rewrite Hm in HHρ'.
                rewrite Nat.sub_diag in HHρ'.
                simpl in HHρ'.
                ltac1:(simplify_eq/=).
                assumption.
                {
                    rewrite length_take.
                    rewrite length_zip_with.
                    ltac1:(lia).
                }
                rewrite length_app.
                rewrite length_take.
                simpl.
                rewrite length_zip_with.
                rewrite length_zip_with.
                rewrite length_drop.
                rewrite length_drop.
                unfold Valuation2,TermOver in *.
                apply lookup_lt_Some in HHφ'.
                ltac1:(lia).
            }
            {
                unfold Valuation2,TermOver in *.
                rewrite length_take.
                rewrite length_take.
                ltac1:(lia).
            }
        }
        {
            inversion HH.
        }
        {
            inversion HH.
        }
    }
Qed.


Definition Valuation2_restrict
    {Σ : StaticModel}
    (ρ : Valuation2)
    (r : gset variable)
    : Valuation2
:=
    filter
        (λ x : variable * (TermOver builtin_value), x.1 ∈ r)
        ρ
.


Lemma Valuation2_restrict_eq_subseteq
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (r r' : gset variable)
:
    r ⊆ r' ->
    Valuation2_restrict ρ1 r' = Valuation2_restrict ρ2 r' ->
    Valuation2_restrict ρ1 r = Valuation2_restrict ρ2 r
.
Proof.
    intros H1 H2.
    unfold Valuation2 in *.
    unfold Valuation2_restrict in *.
    rewrite map_eq_iff.
    rewrite map_eq_iff in H2.
    intros x.
    specialize (H2 x).
    do 2 ltac1:(rewrite map_lookup_filter in H2).
    do 2 ltac1:(rewrite map_lookup_filter).
    simpl in *.
    rewrite elem_of_subseteq in H1.
    specialize (H1 x).
    simpl in *.
    ltac1:(case_guard as Hcg1; case_guard as Hcg2); simpl in *; try ltac1:(auto with nocore).
    {
        destruct (ρ1 !! x) eqn:Hρ1x, (ρ2 !! x) eqn:Hρ2x; simpl in *;
            reflexivity.
    }
    {
        ltac1:(exfalso).
        ltac1:(auto with nocore).
    }
Qed.


Lemma sc_satisfies_insensitive
    {Σ : StaticModel}
    (program : ProgramT)
    (nv : NondetValue)
    :
    ∀ (v1 v2 : Valuation2) (b : SideCondition),
            Valuation2_restrict v1 (vars_of b) = Valuation2_restrict v2 (vars_of b) ->
            SideCondition_evaluate program v1 nv b -> SideCondition_evaluate program v2 nv b
.
Proof.
    intros v1 v2 b H X.
    unfold Valuation2_restrict in H.
    eapply SideCondition_satisfies_strip in X.
    rewrite H in X.
    eapply SideCondition_satisfies_extensive>[|apply X].
    unfold Valuation2 in *.
    apply map_filter_subseteq.
Qed.

Lemma eval_et_strip_helper
    {Σ : StaticModel}
    {_Cbv : Countable builtin_value}
    (program : ProgramT)
    (ρ : Valuation2)
    (et : TermOver Expression2)
    (nv : NondetValue)
    (gg : TermOver (TermOver builtin_value))
:
    TermOver'_option_map (Expression2_evaluate_nv program ρ nv) et = Some gg ->
    TermOver'_option_map (Expression2_evaluate_nv program (filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ vars_of et) ρ) nv) et = Some gg
.
Proof.
    revert gg.
    induction et; intros gg HH; simpl in *.
    {
        rewrite fmap_Some in HH.
        destruct HH as [x [H1x H2x]].
        rewrite fmap_Some.
        subst gg.
        exists x.
        split>[|reflexivity].
        unfold Expression2_evaluate_nv in *.
        rewrite bind_Some in H1x.
        destruct H1x as [y [H1y H2y]].
        apply (inj Some) in H2y.
        subst x.
        rewrite bind_Some.
        exists y.
        split>[|reflexivity].
        apply Expression2_evalute_strip in H1y.
        apply H1y.
    }
    {
        rewrite fmap_Some in HH.
        destruct HH as [x [H1x H2x]].
        subst gg.
        rewrite fmap_Some.
        
        rewrite vars_of_t_term_e.
        (* apply list_collect_inv in H1x as H1x'. *)
        exists x.
        split>[|reflexivity].

        revert x H1x H.
        induction l;
            intros x H1x H;
            simpl in *.
        {
            apply H1x.
        }
        {
            rewrite bind_Some.
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            rewrite bind_Some in H1x.
            destruct H1x as [y [H1y H2y]].
            rewrite bind_Some in H2y.
            destruct H2y as [z [H1z H2z]].
            apply (inj Some) in H2z.
            subst x.
            simpl in *.
            exists y.
            rewrite bind_Some.
            split.
            {
                erewrite TermOver'_option_map__extension>[|()|apply H1].
                { reflexivity. }
                {
                    intros a0 H1a0 H2a0.

                    unfold isSome in *.
                    ltac1:(case_match)>[|inversion H2a0].
                    clear H2a.
                    clear H1x'.
                    unfold Expression2_evaluate_nv in *.
                    rewrite bind_Some.
                    rewrite bind_Some in H.
                    destruct H as [x0 [H1x0 H2x0]].
                    apply (inj Some) in H2x0.
                    subst t.
                    exists x0.
                    split>[|reflexivity].
                    eapply Expression2_evaluate_extensive_Some>[|apply H1x0].
                    unfold Valuation2 in *.
                    ltac1:(rewrite map_filter_subseteq_ext).
                    intros i x1 H1ix1 H2ix2.
                    simpl in *.
                    rewrite elem_of_union.
                    left.
                    apply H2ix2.
                }
                {
                    apply H1y.
                }
            }
            {
                exists z.
                split>[|reflexivity].
                specialize (H1 _ H1y).
                specialize (IHl z H1z H2).
                clear H1z H2.
                fold (@fmap _ list_fmap).
                (* unfold Valuation2 in *. *)
                assert(Hfilter: 
                    (filter
                        (λ kv : variable * TermOver builtin_value,
                      kv.1 ∈ ⋃ (vars_of <$> l))
                    ρ)
                    ⊆
                    (filter
                        (λ kv : variable * TermOver builtin_value,
                        kv.1 ∈ (vars_of a ∪ (⋃ (vars_of <$> l))))
                    ρ)
                ).
                {
                    unfold Valuation2 in *.
                    apply map_filter_strong_subseteq_ext.
                    intros i x.
                    simpl.
                    intros [HH1 HH2].
                    split>[|exact HH2].
                    rewrite elem_of_union.
                    right.
                    exact HH1.
                }
                (* unfold Expression2_evaluate_nv in *. *)
                apply list_collect_inv in IHl as IHl'.
                rewrite <- IHl.
                apply f_equal.
                apply list_fmap_ext.
                intros i x Hix.
                match! goal with
                | [|- (TermOver'_option_map ?f _ = _)] =>
                    remember $f as myf
                end.
                assert(Htmp := @TermOver'_option_map__Some_1 (symbol) _ _ _ _ myf).
                apply take_drop_middle in Hix as Hix'.
                rewrite <- Hix' in IHl'.
                (* clear Hix'. *)
                rewrite fmap_app in IHl'.
                rewrite fmap_cons in IHl'.
                rewrite Forall_app in IHl'.
                rewrite Forall_cons in IHl'.
                destruct IHl' as [_ [IHmy _]].
                unfold isSome in IHmy.
                ltac1:(case_match).
                {
                    clear IHmy.
                    ltac1:(rename H into Hmy).
                    ltac1:(rename t into tmy).
                    specialize (Htmp x tmy).
                    subst myf.
                    rewrite Hix' in Hmy.
                    ltac1:(ospecialize (Htmp _)).
                    {
                        eapply TermOver'_option_map__extension>[|apply Hmy].
                        intros a0 Ha0 Hevala0.
                        clear Htmp.
                        unfold Expression2_evaluate_nv in *.
                        unfold isSome in *.
                        ltac1:(case_match).
                        {
                            rewrite bind_Some in H.
                            destruct H as [x0 [H1x0 H2x0]].
                            clear Hevala0.
                            apply (inj Some) in H2x0.
                            subst t.
                            rewrite bind_Some.
                            exists x0.
                            split>[|reflexivity].
                            eapply Expression2_evaluate_extensive_Some>[|apply H1x0].
                            apply Hfilter.
                        }
                        {
                            inversion Hevala0.
                        }
                    }
                    symmetry.
                    eapply TermOver'_option_map__extension in Hmy as Hmy'.
                    rewrite Hmy'.
                    {
                        symmetry.
                        eapply TermOver'_option_map__extension>[|apply Hmy].
                        intros a0 H1a0 H2a0.
                        unfold Expression2_evaluate_nv in *.
                        unfold isSome in *.
                        ltac1:(case_match).
                        {
                            clear H2a0.
                            rewrite bind_Some.
                            rewrite bind_Some in H.
                            destruct H as [x0 [H1x0 H2x0]].
                            apply (inj Some) in H2x0.
                            subst t.
                            exists x0.
                            split>[|reflexivity].
                            eapply Expression2_evaluate_extensive_Some>[|apply H1x0].
                            apply Hfilter.
                        }
                        {
                            inversion H2a0.
                        }
                    }
                    {
                        intros a0 H1a0 H2a0.
                        unfold Expression2_evaluate_nv in *.
                        unfold isSome in *.
                        ltac1:(case_match).
                        {
                            rewrite bind_Some in H.
                            destruct H as [x0 [H1x0 H2x0]].
                            clear H2a0.
                            apply (inj Some) in H2x0.
                            subst t.
                            reflexivity.
                        }
                        {
                            inversion H2a0.
                        }
                    }
                }
                { inversion IHmy. }
            }
        }
    }
Qed.

(* Check eval_et_strip_helper. *)
(* Check Expression2_evalute_strip. *)
Lemma eval_et_strip
    {Σ : StaticModel}
    {_Cbv : Countable builtin_value}
    (program : ProgramT)
    (ρ : Valuation2)
    (et : TermOver Expression2)
    (nv : NondetValue)
    (g : TermOver builtin_value)
:
    eval_et program ρ nv et = Some g ->
    eval_et program (filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ vars_of et) ρ) nv et = Some g
.
Proof.
    unfold eval_et.
    intros HH.
    rewrite bind_Some in HH.
    rewrite bind_Some.
    destruct HH as [x [H1x H2x]].
    apply (inj Some) in H2x.
    subst g.
    exists x.
    split>[|reflexivity].
    eapply eval_et_strip_helper.
    { apply H1x. }
Qed.

Lemma eval_et_correct
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (et : TermOver Expression2)
    (nv : NondetValue)
    (g : TermOver builtin_value)
    :
    eval_et program ρ nv et = Some g ->
    satisfies ρ (program, (nv,g)) et
.
Proof.
    intros HH.
    unfold satisfies; simpl.
    unfold eval_et in HH.
    revert g HH.
    induction et; simpl in *; intros g HH.
    {
        destruct (Expression2_evaluate program ρ a) eqn:Heq.
        {
            simpl in *.
            ltac1:(simplify_eq/=).
            ltac1:(simp sat2E).
            rewrite Heq.
            rewrite bind_Some in HH.
            destruct HH as [x [H1x H2x]].
            apply (inj Some) in H2x.
            subst g.
            unfold Expression2_evaluate_nv in H1x.
            rewrite Heq in H1x.
            simpl in H1x.
            apply (inj Some) in H1x.
            subst x.
            simpl.
            reflexivity.
        }
        {
            simpl in *.
            unfold Expression2_evaluate_nv in HH.
            rewrite Heq in HH.
            simpl in HH.
            inversion HH.
        }
    }
    {
        destruct g.
        {
            simpl in *.
            ltac1:(simplify_option_eq).
        }
        {   
            ltac1:(simplify_option_eq).
            ltac1:(simp sat2E).
            inversion HH; subst; clear HH.
            split>[reflexivity|].
            rewrite length_fmap.
            ltac1:(rename H1 into l1).
            split.
            {
                apply length_list_collect_Some in Heqo0.
                rewrite length_fmap in Heqo0.
                symmetry. assumption.
            }
            {
                revert l1 Heqo0.
                induction l; intros l1 HH.
                {
                    intros.
                    rewrite lookup_nil in pf1.
                    inversion pf1.
                }
                {
                    rewrite Forall_cons in H.
                    destruct H as [IH1 IH2].
                    specialize (IHl IH2).
                    simpl in HH.
                    ltac1:(simplify_option_eq).
                    symmetry in Heqo0.
                    destruct (list_collect (TermOver_collect <$> map (TermOver_map (Expression2_evaluate program ρ)) l)) eqn:Heq';
                        ltac1:(simplify_eq/=).
                    specialize (IHl _ erefl).
                    intros.
                    destruct i.
                    {
                        simpl in *.
                        ltac1:(simplify_eq/=).
                        apply IH1.
                        { reflexivity. }
                    }
                    {
                        simpl in *.
                        apply IHl with (i := i ).
                        assumption.
                        assumption.
                    }
                    {
                        intros.
                        destruct i.
                        {
                            simpl in *.
                            ltac1:(simplify_eq/=).
                            apply IH1.
                            { reflexivity. }
                        }
                        {
                            simpl in *.
                            specialize (IHl H0 erefl i t' φ' pf1 pf2).
                            apply IHl.
                        }
                    }
                }
            }
        }
    }
Qed.

Lemma eval_et_correct_2
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (et : TermOver Expression2)
    (nv : NondetValue)
    (g : TermOver builtin_value)
    :
    satisfies ρ (program, (nv,g)) et ->
    eval_et program ρ nv et = Some g
.
Proof.
    revert g.
    induction et; intros g; destruct g; simpl in *; intros HH.
    {
        unfold satisfies in HH. simpl in HH.
        ltac1:(simp sat2E in HH).
        unfold eval_et. simpl.
        destruct (Expression2_evaluate program ρ a) eqn:Heq>[|ltac1:(contradiction)].
        simpl.
        unfold Expression2_evaluate_nv.
        rewrite Heq. simpl.
        rewrite HH. reflexivity.
    }
    {
        unfold satisfies in HH. simpl in HH.
        ltac1:(simp sat2E in HH).
        unfold eval_et. simpl. 
        destruct (Expression2_evaluate program ρ a) eqn:Heq>[|ltac1:(contradiction)].
        simpl.
        unfold Expression2_evaluate_nv.
        rewrite Heq.
        simpl.
        rewrite HH. reflexivity.
    }
    {
        unfold satisfies in HH. simpl in HH.
        ltac1:(simp sat2E in HH).
        destruct HH.
    }
    {
        unfold satisfies in HH. simpl in HH.
        ltac1:(simp sat2E in HH).
        destruct HH as [HH1 [HH2 HH3]].
        subst s0.
        revert l0 HH2 HH3.
        induction l; intros l0 HH2 HH3; simpl in *.
        {
            destruct l0; simpl in *.
            {
                unfold eval_et; simpl.
                reflexivity.
            }
            {
                ltac1:(lia).
            }
        }
        {
            rewrite Forall_cons in H.
            destruct H as [IH1 IH2].
            specialize (IHl IH2).
            destruct l0.
            {
                simpl in *. ltac1:(lia).
            }
            {
                clear IH2.
                specialize (IHl l0 ltac:(simpl in *;lia)).
                ltac1:(ospecialize (IHl _)).
                {
                    intros. apply HH3 with (i := (S i));
                        simpl in *;
                        assumption.
                }
                specialize (HH3 0 t a erefl erefl).


                unfold eval_et in *.
                (* ltac1:(rewrite [TermOver_map _ _]/=). *)
                (* rewrite fmap_Some. *)
                simpl.
                ltac1:(setoid_rewrite bind_Some).
                ltac1:(setoid_rewrite bind_Some).
                ltac1:(setoid_rewrite bind_Some).
                
                (* split>[|reflexivity]. *)

                specialize (IH1 _ HH3). clear HH3.
                rewrite bind_Some in IH1.
                destruct IH1 as [x [H1x H2x]].
                rewrite bind_Some in IHl.
                destruct IHl as [y [H1y H2y]].
                apply (inj Some) in H2y.
                apply (inj Some) in H2x.
                subst t.
                simpl in *.
                rewrite fmap_Some in H1y.
                destruct H1y as [z [H1z H2z]].
                subst y.
                simpl in *.
                ltac1:(injection H2y as H2y).
                subst l0.
                simpl in *.
                eexists (t_term s (?[U1]::?[U2])).
                simpl. split>[|reflexivity].
                exists (x::z).
                split>[|reflexivity].
                setoid_rewrite H1z.
                simpl.
                exists x.
                split>[|reflexivity].
                exact H1x.
            }
        }
    }
Qed.

Lemma TermOver'_option_map__Expression2_evaluate__extensive {Σ : StaticModel} a nv ρ1 ρ2 program
:
    ρ1 ⊆ ρ2 ->
    ∀ t : TermOver' (TermOver builtin_value),
    TermOver'_option_map
    (λ t0 : Expression2,
    Expression2_evaluate program ρ1 t0
    ≫= λ gt : NondetValue → TermOver builtin_value, Some (gt nv))
    a = Some t
    → @TermOver'_option_map symbol _ _
    (λ t0 : Expression2,
    Expression2_evaluate program ρ2 t0
    ≫= λ gt : NondetValue → TermOver builtin_value, Some (gt nv))
    a = Some t
.
Proof.
    intros Hρ.
    induction a; intros t Ht.
    {
        simpl in *.
        rewrite fmap_Some in Ht.
        destruct Ht as [x [H1x H2x]].
        subst t.
        rewrite bind_Some in H1x.
        destruct H1x as [y [H1y H2y]].
        apply (inj Some) in H2y.
        subst x.
        rewrite fmap_Some.
        exists (y nv).
        split>[|reflexivity].
        rewrite bind_Some.
        exists y.
        split>[|reflexivity].
        eapply Expression2_evaluate_extensive_Some.
        { apply Hρ. }
        { apply H1y. }
    }
    {
        simpl in *.
        rewrite fmap_Some in Ht.
        destruct Ht as [x [H1x H2x]].
        rewrite fmap_Some.
        subst t.
        exists x.
        split>[|reflexivity].
        revert x H1x H.
        induction l; intros x H1x H.
        {
            simpl in *.
            destruct x>[reflexivity|].
            simpl in *.
            inversion H1x.
        }
        {
            simpl in *.
            rewrite bind_Some.
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            rewrite bind_Some in H1x.
            destruct H1x as [x0 [H1x0 H2x0]].
            rewrite bind_Some in H2x0.
            destruct H2x0 as [x1 [H1x1 H2x1]].
            apply (inj Some) in H2x1.
            subst x.
            simpl in *.
            specialize (IHl _ H1x1 H2).
            exists x0.
            split.
            {
                apply H1.
                apply H1x0.
            }
            {
                clear H1 H1x0.
                rewrite bind_Some.
                exists x1.
                split>[|reflexivity].
                apply IHl.
            }
        }
    }
Qed.

Lemma eval_et_evaluate_None_relative
    {Σ : StaticModel}
    (program : ProgramT)
    (et : TermOver Expression2)
    (ρ1 ρ2 : Valuation2)
    (nv : NondetValue)
    :
    vars_of et ⊆ vars_of ρ1 ->
    ρ1 ⊆ ρ2 ->
    eval_et program ρ1 nv et = None ->
    eval_et program ρ2 nv et = None
.
Proof.
    induction et; simpl in *; intros HH1 HH2 HH3.
    {
        unfold eval_et in *; simpl in *.
        rewrite bind_None in HH3.
        rewrite bind_None.
        destruct HH3 as [HH3|HH3].
        {
            rewrite fmap_None in HH3.
            unfold Expression2_evaluate_nv in *.
            rewrite bind_None in HH3.
            destruct HH3 as [HH3|HH3].
            {
                eapply Expression2_evaluate_None_relative in HH3.
                {
                    rewrite HH3.
                    simpl.
                    left.
                    reflexivity.
                }
                {
                    apply HH1.
                }
                { apply HH2. }
            }
            {
                destruct HH3 as [x [H1x H2x]].
                inversion H2x.
            }
        }
        {
            destruct HH3 as [x [H1x H2x]].
            inversion H2x.
        }
    }
    {
        unfold eval_et in *.
        rewrite Forall_forall in H.
        rewrite bind_None.
        rewrite bind_None in HH3.
        simpl in *.
        destruct HH3 as [HH3|HH3].
        {
            simpl in *.
            rewrite fmap_None in HH3.
            apply list_collect_Exists_1 in HH3.
            rewrite Exists_exists in HH3.
            destruct HH3 as [x [H1x H2x]].
            simpl in H2x.
            unfold isSome in *.
            unfold is_true in *.
            left.
            destruct x; simpl in *.
            {
                ltac1:(contradiction H2x).
                reflexivity.
            }
            {
                clear H2x.
                rewrite fmap_None.
                apply list_collect_Exists.
                rewrite Exists_exists.
                exists None.
                simpl.
                unfold Expression2_evaluate_nv in *.
                rewrite elem_of_list_fmap in H1x.
                rewrite elem_of_list_fmap.
                split>[|intros HH; inversion HH].
                destruct H1x as [y [H1y H2y]].
                exists y.
                split>[|apply H2y].
                specialize (H _ H2y).
                ltac1:(ospecialize (H _)).
                {
                    rewrite elem_of_list_lookup in H2y.
                    destruct H2y as [i Hi].
                    apply take_drop_middle in Hi.
                    rewrite <- Hi in HH1.
                    unfold vars_of in HH1; simpl in HH1.
                    rewrite fmap_app in HH1.
                    rewrite fmap_cons in HH1.
                    rewrite union_list_app in HH1.
                    rewrite union_list_cons in HH1.
                    ltac1:(set_solver).
                }
                specialize (H HH2).
                rewrite bind_None in H.
                rewrite bind_None in H.
                ltac1:(ospecialize (H _)).
                {
                    left.
                    symmetry.
                    apply H1y.
                }
                destruct H as [H|H].
                {
                    symmetry.
                    apply H.
                }
                {
                    destruct H as [x [H1x H2x]].
                    inversion H2x.
                }
            }
        }
        {
            destruct HH3 as [x [H1x H2x]].
            inversion H2x.
        }
    }
Qed.

Lemma eval_et_extensive_Some
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ1 ρ2 : Valuation2)
    (et : TermOver Expression2)
    (nv : NondetValue)
    (t : TermOver builtin_value)
    :
    ρ1 ⊆ ρ2 ->
    eval_et program ρ1 nv et = Some t ->
    eval_et program ρ2 nv et = Some t.
Proof.
    revert t.
    induction et; intros t H1 H2; simpl in *.
    {
        unfold eval_et in *. simpl in *.
        destruct (Expression2_evaluate program ρ1 a) eqn:Heq1.
        {
            simpl in *.
            rewrite bind_Some in H2.
            destruct H2 as [x [H1x H2x]].
            rewrite fmap_Some in H1x.
            destruct H1x as [z [H1z H2z]].
            subst x.
            simpl in *.
            apply (inj Some) in H2x.
            subst z.
            unfold Expression2_evaluate_nv in H1z.
            rewrite Heq1 in H1z.
            simpl in H1z.
            apply (inj Some) in H1z.
            subst t.
            eapply Expression2_evaluate_extensive_Some in Heq1>[|apply H1].
            unfold Expression2_evaluate_nv.
            rewrite Heq1.
            simpl.
            reflexivity.
        }
        {
            simpl in *.
            ltac1:(repeat case_match; simplify_option_eq).
            rewrite bind_Some.
            unfold Expression2_evaluate_nv in Heqo0.
            rewrite Heq1 in Heqo0.
            simpl in Heqo0.
            inversion Heqo0.
        }
    }
    {
        unfold eval_et in *; simpl in *.
        ltac1:(simplify_option_eq).
        apply bind_Some.
        eexists (t_term s ?[U]).
        split> [|reflexivity].
        apply bind_Some.
        exists H2.
        split> [|reflexivity].
        Check TermOver'_option_map__Expression2_evaluate__extensive.
        (* Search list_collect. *)
        revert H2 H Heqo0.
        induction l;
            intros l' H Heqo0.
        {
            simpl in *.
            ltac1:(simplify_eq/=).
            reflexivity.
        }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [HH1 HH2].
            destruct l';
                ltac1:(simpl in *; simplify_option_eq)
            .
            apply bind_Some.
            simpl.
            exists t.
            ltac1:(simplify_option_eq).
            split>[|reflexivity].
            specialize (IHl l' HH2 erefl).
            clear HH2.
            specialize (HH1 (TermOver'_join t) H1 erefl).
            simpl in *.
            rewrite bind_Some in HH1.
            destruct HH1 as [x [H1x H2x]].
            apply (inj Some) in H2x.
            unfold Expression2_evaluate_nv in *.
            apply list_collect_inv in IHl as IHl'.
            clear IHl.
            apply list_collect_inv in Heqo1 as Heqo1'.
            clear Heqo1.
            eapply TermOver'_option_map__Expression2_evaluate__extensive.
            { apply H1. }
            apply Heqo.
        }
    }
Qed.

Lemma try_match_lhs_with_sc_complete
    {Σ : StaticModel}
    {_Cbv : Countable builtin_value}
    {Act : Set}
    (program : ProgramT)
    (g g' : TermOver builtin_value)
    (r : RewritingRule2 Act)
    (ρ : Valuation2)
    (nv : NondetValue)
    :
    vars_of (r_scs r) ⊆ vars_of (r_from r) ->
    vars_of (r_to r) ⊆ vars_of (r_from r) ->
    satisfies ρ g (r_from r) ->
    eval_et program ρ nv (r_to r) = Some g' ->
    satisfies ρ (program, nv) (r_scs r) ->
    {
        ρ' : (gmap variable (TermOver builtin_value)) &
        { g'' : TermOver builtin_value &
            vars_of ρ' = vars_of (r_from r) ∧
            ρ' ⊆ ρ ∧
            try_match_lhs_with_sc program g nv r = Some (ρ', g'')
        }
    }   
.
Proof.
    intros Hn Hn' H1 HX H2.
    apply try_match_new_complete in H1.
    destruct H1 as [ρ1 [H1ρ1 H2ρ1]].
    destruct H2ρ1 as [H2ρ1 H3ρ2].
    unfold satisfies in H2; simpl in H2.
    unfold try_match_lhs_with_sc.
    rewrite H3ρ2.
    simpl.
    eapply sc_satisfies_insensitive in H2.
    {
        rewrite H2.
        eapply eval_et_strip in HX as HX'.
        eapply eval_et_extensive_Some in HX'.
        {
            rewrite HX'.
            exists ρ1.
            exists g'.
            repeat split.
            {
                exact H1ρ1.
            }
            {
                exact H2ρ1.
            }
        }
        {
            apply map_subseteq_spec.
            intros i x Hfil.
            unfold Valuation2 in *.
            rewrite map_lookup_filter_Some in Hfil.
            destruct Hfil as [H1fil H2fil].
            simpl in H2fil.
            eapply elem_of_weaken in H2fil>[|apply Hn'].
            rewrite <- H1ρ1 in H2fil.
            unfold vars_of in H2fil; simpl in H2fil.
            unfold Valuation2 in *.
            rewrite elem_of_dom in H2fil.
            destruct H2fil as [x' Hx'].
            eapply lookup_weaken in Hx' as H'x'>[|apply H2ρ1].
            ltac1:(congruence).
        }
    }
    {
        unfold Valuation2_restrict.
        unfold Valuation2 in *.
        apply map_eq.
        intros i.
        rewrite map_lookup_filter.
        rewrite map_lookup_filter.
        ltac1:(simplify_option_eq).
        {
            unfold mbind,option_bind.
            destruct (ρ !! i) as [y|] eqn:Hρi, (ρ1 !! i) as [z|] eqn:Hρ1i.
            {
                eapply lookup_weaken in Hρ1i.
                rewrite Hρi in Hρ1i.
                exact Hρ1i.
                exact H2ρ1.     
            }
            {
                ltac1:(exfalso).
                unfold vars_of in H1ρ1; simpl in H1ρ1.
                assert (Htmp : i ∉ dom ρ1).
                {
                    intros HContra.
                    rewrite elem_of_dom in HContra.
                    destruct HContra as [zz Hzz].
                    ltac1:(simplify_eq/=).
                }
                unfold Valuation2 in *.
                rewrite H1ρ1 in Htmp.
                clear - Htmp Hn Hx H.
                unfold vars_of in Hn; simpl in Hn.
                ltac1:(set_solver).
            }
            {
                ltac1:(exfalso).
                eapply lookup_weaken in Hρ1i>[|apply H2ρ1].
                rewrite Hρi in Hρ1i.
                inversion Hρ1i.
            }
            { reflexivity. }
        }
        {
            destruct (ρ !! i) eqn:Heq1,(ρ1 !! i) eqn:Heq2; simpl in *;
                try reflexivity.
        }
    }
Qed.

Lemma valuation_restrict_vars_of_self
    {Σ : StaticModel}
    (ρ' ρ : Valuation2)
    :
    ρ' ⊆ ρ  ->
    Valuation2_restrict ρ' (vars_of ρ') = Valuation2_restrict ρ (vars_of ρ')
.
Proof.
    intros H.
    unfold Valuation2 in *.
    rewrite map_eq_iff.
    unfold Valuation2_restrict.
    intros i.
    unfold Valuation2 in *.
    rewrite map_lookup_filter.
    rewrite map_lookup_filter.
    destruct (ρ' !! i) eqn:Hρ'i.
    {
        simpl.
        ltac1:(repeat case_guard; simpl in *; simplify_eq/=).
        {
            assert (Hρi: ρ !! i = Some t).
            {
                eapply lookup_weaken>[|apply H].
                assumption.
            }
            rewrite Hρi.
            simpl.
            reflexivity.
        }
        {
            destruct (ρ !! i); reflexivity.
        }
    }
    {
        simpl.
        destruct (ρ!!i) eqn:Hρi; simpl.
        {
            ltac1:(repeat case_guard; simpl in *; simplify_eq/=; try reflexivity; exfalso).
            unfold vars_of in *; simpl in *.
            unfold Valuation2 in *.
            rewrite elem_of_dom in H0.
            destruct H0 as [g' Hg'].
            rewrite Hρ'i in Hg'.
            inversion Hg'.
        }
        {
            reflexivity.
        }
    }
Qed.


Lemma thy_lhs_match_one_None
    {Σ : StaticModel}
    {_Cbv : Countable builtin_value}
    {Act : Set}
    (program : ProgramT)
    (e : TermOver builtin_value)
    (Γ : RewritingTheory2 Act)
    (wfΓ : RewritingTheory2_wf Γ)
    (nv : NondetValue)
    :
    thy_lhs_match_one e nv Γ program = None ->
    notT { r : RewritingRule2 Act & { ρ : Valuation2 & { e' : TermOver builtin_value &
        ((r ∈ Γ) *
         (satisfies ρ e (r_from r)) *
         (satisfies ρ (program, nv) (r_scs r)) *
         (eval_et program ρ nv (r_to r) = Some e') *
         (vars_of (r_to r) ⊆ vars_of (r_from r))
        )%type
    } } }
        
.
Proof.
    unfold thy_lhs_match_one.
    intros H.
    intros [r [ρ [e' [[[[Hin HContra1] HContra2] HContra3] HContra4]]]].
    destruct (list_find isSome (try_match_lhs_with_sc program e nv <$> Γ)) eqn:Heqfound.
    {
        destruct p as [n oρ].
        rewrite list_find_Some in Heqfound.
        rewrite bind_None in H.
        ltac1:(destruct H as [H|H];[inversion H|]).
        destruct H as [[idx ρ2][H1 H2]].
        simpl in H2.
        inversion H1; subst; clear H1.
        ltac1:(destruct Heqfound as [Hfound [HSome HFirst]]).
        apply bind_None_T_1 in H2.
        destruct H2 as [H2|H2].
        {
            rewrite H2 in HSome. inversion HSome.
        }
        {
            destruct H2 as [x [H21 H22]].
            apply bind_None_T_1 in H22.
            destruct H22 as [H22|H22].
            {
                rewrite list_lookup_fmap in Hfound.
                rewrite H22 in Hfound.
                simpl in Hfound. inversion Hfound.
            }
            {
                subst ρ2.
                destruct H22 as [x0 [H221 HContra]].
                inversion HContra.
            }
        }
    }
    {
        simpl in H.
        clear H.
        rewrite list_find_None in Heqfound.
        rewrite Forall_forall in Heqfound.
        ltac1:(rename HContra1 into Hsat1).
        ltac1:(rename HContra2 into Hsat2).
        unfold satisfies in Hsat1; simpl in Hsat1.
        apply try_match_new_complete in Hsat1.
        destruct Hsat1 as [ρ' [H1 [H2 H3]]].
        assert (Hc := try_match_lhs_with_sc_complete program e e' r).
        specialize (Hc ρ').
        ltac1:(ospecialize (Hc nv _ _)).
        {
            unfold is_true in wfΓ.
            specialize (wfΓ r).
            specialize (wfΓ Hin).
            apply wfΓ.
        }
        {
            apply HContra4.
        }
        assert (H3' := H3).
        apply try_match_new_correct in H3'.
        specialize (Hc H3').
        ltac1:(ospecialize (Hc _ _)).
        {
            clear Hc.
            apply eval_et_strip in HContra3 as HContra3'.
            eapply eval_et_extensive_Some in HContra3'.
            { apply HContra3'. }
            {
                clear HContra3'.
                assert (Hfs: filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ vars_of (r_to r)) ρ ⊆ filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ vars_of (r_from r)) ρ).
                {
                    unfold Valuation2 in *.
                    unfold Subseteq_Valuation2.
                    rewrite map_filter_subseteq_ext.
                    intros i x Hix.
                    simpl.
                    intros HH.
                    eapply elem_of_weaken.
                    { apply HH. }
                    { apply HContra4. }
                }
                unfold Valuation2 in *.
                apply transitivity with (y := filter
                    (λ kv : variable * TermOver builtin_value,
                    kv.1 ∈ vars_of (r_from r))
                    ρ).
                { apply Hfs. }
                {
                    clear Hfs.
                    rewrite <- H1.
                    unfold Valuation2 in *.
                    apply map_subseteq_spec.
                    intros i x Hfltr.
                    rewrite map_lookup_filter in Hfltr.
                    rewrite bind_Some in Hfltr.
                    destruct Hfltr as [x0 [H1x0 H2x0]].
                    rewrite bind_Some in H2x0.
                    simpl in H2x0.
                    destruct H2x0 as [HHH [H1x1 H2x1]].
                    apply (inj Some) in H2x1.
                    subst x0.
                    clear H1x1.
                    unfold vars_of in HHH; simpl in HHH.
                    unfold Valuation2 in *.
                    rewrite elem_of_dom in HHH.
                    destruct HHH as [y Hy].
                    eapply lookup_weaken in Hy as Hy'>[|apply H2].
                    ltac1:(congruence).
                }
            }
        }
        {
            unfold satisfies; simpl.
            eapply sc_satisfies_insensitive in Hsat2 as Hsat2'.
            apply Hsat2'.
            assert (Htmp := valuation_restrict_vars_of_self ρ' ρ H2).
            eapply Valuation2_restrict_eq_subseteq in Htmp.
            symmetry. apply Htmp.
            rewrite H1.   
            unfold is_true in wfΓ.
            specialize (wfΓ r).
            specialize (wfΓ Hin).
            unfold RewritingRule2_wf in *.
            destruct wfΓ as [[wf11 wf12] wf2].
            unfold RewritingRule2_wf1 in *.
            unfold RewritingRule2_wf2 in *.
            eapply transitivity>[|apply wf11].
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        destruct Hc as [ρ'' [H1ρ'' [H2ρ'' [H3ρ'' H4ρ'']]]].
        unfold try_match_lhs_with_sc in H4ρ''.
        rewrite bind_Some in H4ρ''.
        destruct H4ρ'' as [x [H1x H2x]].
        (* apply try_match_new_correct in H1x. *)
        unfold satisfies in *; simpl in *.
        (* Search try_match_new. *)
        ltac1:(repeat case_match).
        {
            ltac1:(simplify_eq/=).
            eapply Heqfound.
            rewrite elem_of_list_fmap.
            unfold try_match_lhs_with_sc.
            exists r.
            rewrite H3.
            simpl.
            rewrite H.
            rewrite H0.
            split>[reflexivity|].
            exact Hin.
            simpl. reflexivity.
        }
        {
            inversion H2x.
        }
        {
            inversion H2x.
        }
    }
Qed.


Lemma thy_lhs_match_one_Some
    {Σ : StaticModel}
    {Act : Set}
    (e e' : TermOver builtin_value)
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    (r : RewritingRule2 Act)
    (ρ : Valuation2)
    (nv : NondetValue)
    (rule_idx : nat)
    :
    thy_lhs_match_one e nv Γ program = Some (r, ρ, e', rule_idx) ->
    ((r ∈ Γ) * (satisfies ρ e (r_from r)) * (eval_et program ρ nv (r_to r) = Some e') * (satisfies ρ (program, nv) (r_scs r)))%type
.
Proof.
    intros H.
    unfold thy_lhs_match_one in H.
    unfold is_Some in H.
    (repeat ltac1:(case_match)); subst.
    {
        apply bind_Some_T_1 in H.
        destruct H as [[idx oρ][H1 H2]].
        simpl in *.
        rewrite list_find_Some in H1.
        destruct H1 as [H11 H12].
        rewrite list_lookup_fmap in H11.
        apply fmap_Some_T_1 in H11.
        destruct H11 as [ot [Hot1 Hot2]].
        subst.
        apply bind_Some_T_1 in H2.
        destruct H2 as [ρ' [H1ρ' H2ρ']].
        apply bind_Some_T_1 in H2ρ'.
        destruct H2ρ' as [r' [H1r' H2r']].
        inversion H2r'; subst; clear H2r'.
        rewrite Hot1 in H1r'.
        inversion H1r'; subst; clear H1r'.
        split.
        {
            split.
            {
                split.
                {
                    rewrite elem_of_list_lookup.
                    exists rule_idx. apply Hot1.
                }
                {
                    destruct H12 as [H1 H2].
                    unfold is_true, isSome in H1.
                    destruct (try_match_lhs_with_sc program e nv r) eqn:HTM>[|inversion H1].
                    clear H1.
                    inversion H1ρ'; subst; clear H1ρ'.
                    unfold try_match_lhs_with_sc in HTM.
                    apply bind_Some_T_1 in HTM.
                    destruct HTM as [x [H1x H2x]].
                    apply try_match_new_correct in H1x.
                    destruct (SideCondition_evaluate program x nv (r_scs r)) eqn:Heq.
                    {
                        unfold isSome in H2x.
                        destruct (eval_et program x nv (r_to r)) eqn:Heq2.
                        {
                            apply (inj Some) in H2x.
                            subst ρ'.
                            apply H1x.
                        }
                        {
                            inversion H2x.
                        }
                    }
                    {
                        inversion H2x.
                    }   
                }
            }
            {
                unfold try_match_lhs_with_sc in H1ρ'.
                apply bind_Some_T_1 in H1ρ'.
                destruct H1ρ' as [x [H1x H2x]].
                ltac1:(repeat case_match; simpl in *; simplify_eq/=).
                assumption.
            }
        }
        {
            destruct H12 as [H1 H2].
            unfold is_true, isSome in H1.
            destruct (try_match_lhs_with_sc program e nv r) eqn:HTM>[|inversion H1].
            clear H1.
            inversion H1ρ'; subst; clear H1ρ'.
            unfold try_match_lhs_with_sc in HTM.
            apply bind_Some_T_1 in HTM.
            destruct HTM as [x [H1x H2x]].
            destruct (SideCondition_evaluate program x nv (r_scs r)) eqn:Heq.
            {

                unfold isSome in H2x.
                destruct (eval_et program x nv (r_to r)) eqn:Heq2.
                {
                    apply (inj Some) in H2x.
                    subst ρ'.
                    simpl.
                    apply Heq.
                }
                {
                    inversion H2x.
                }
            }
            {
                inversion H2x.
            }
        }
    }
Qed.


Lemma naive_interpreter_sound
    {Σ : StaticModel}
    {_Cbv : Countable builtin_value}
    {Act : Set}
    (Γ : RewritingTheory2 Act)
    : Interpreter_sound Γ (naive_interpreter Γ).
Proof.
    unfold Interpreter_sound.
    intros wfΓ.
    unfold naive_interpreter.
    unfold Interpreter_sound.
    unfold stuck,not_stuck.
    unfold naive_interpreter_ext.
    repeat split.
    {
        intros program e1 e2 nv.
        intros Hbind.
        apply bind_Some_T_1 in Hbind.
        destruct Hbind as [x [H1x H2x]].
        destruct (thy_lhs_match_one e1 nv Γ) eqn:Hmatch.
        {
            destruct p as [p idx].
            destruct p as [p g].
            destruct p as [r ρ].
            ltac1:(simplify_option_eq).
            apply thy_lhs_match_one_Some in Hmatch.
            simpl.
            exists r.
            destruct Hmatch as [[[Hin Hm1] Hm2] Hm3].
            exists (r_act r).
            split>[apply Hin|].
            unfold rewrites_to.
            exists ρ.
            unfold rewrites_in_valuation_under_to.
            apply eval_et_correct in Hm2.
            (repeat split); try assumption.
        }
        {
            inversion H1x.
        }
    }
    {
        intros program e Hstuck nv.
        destruct (thy_lhs_match_one e nv Γ) eqn:Hmatch>[|reflexivity].
        {
            destruct p as [p idx].
            destruct p as [p g].
            destruct p as [r ρ].
            (* destruct p as [[r ρ] rule_idx]. *)
            {
                apply thy_lhs_match_one_Some in Hmatch.
                destruct Hmatch as [Hin Hsat].
                assert (Hts := @thy_lhs_match_one_Some Σ).
                unfold rewriting_relation in Hstuck.
                unfold rewrites_to in Hstuck.
                unfold rewrites_in_valuation_under_to in Hstuck.
                assert (Hev := eval_et_correct program ρ (r_to r) nv).
                ltac1:(cut (~ ∃ g', eval_et program ρ nv (r_to r) = Some g')).
                {
                    intros HContra.
                    rewrite <- eq_None_ne_Some.
                    intros x HC.
                    rewrite bind_Some in HC.
                    destruct HC as [x0 [HC1 HC2]].
                    ltac1:(simplify_option_eq).
                    apply HContra. clear HContra.
                    exists g.
                    apply Hin.
                }
                intros HContra.
                destruct HContra as [pg' Hg'].
                apply Hev in Hg'.
                clear Hev.
                apply Hstuck. clear Hstuck.
                exists pg'. exists nv. exists r.
                exists (r_act r).
                (* destruct Hin. *)
                split>[apply Hin|].
                exists ρ.
                repeat split; try assumption.
                apply Hin.
            }
        }
    }
    {
        intros program e Hnotstuck.
        (* Check not_stuck. *)
        (* unfold naive_interpreter. *)

        destruct Hnotstuck as [e' He'].
        destruct He' as [nv [r' [a [H1r' H2r']]]].
        unfold rewrites_to in H2r'.
        destruct H2r' as [ρ' Hρ'].
        unfold rewrites_in_valuation_under_to in Hρ'.
        destruct Hρ' as [[[H1ρ' H2ρ'] H3ρ'] H4ρ'].
        subst a.
        unfold satisfies in *; simpl in *.
        (* Search thy_lhs_match_one. *)

        
        destruct (thy_lhs_match_one e nv Γ program) eqn:Hmatch.
        {
            destruct p as [[[r ρ] e''] rule_idx]; cbn in *.
            apply thy_lhs_match_one_Some in Hmatch as Hmatch'.
            destruct Hmatch' as [[Hin H1sat] H2sat].
            eexists. eexists. rewrite Hmatch.
            simpl. reflexivity.
        }
        {
            ltac1:(exfalso).
            apply thy_lhs_match_one_None in Hmatch.
            apply Hmatch.
            clear Hmatch.
            exists r'.
            unfold satisfies; simpl.
            exists ρ'.
            exists e'.
            (repeat split); try assumption.
            {
                apply eval_et_correct_2.
                apply H2ρ'.
            }
            {
                apply wfΓ.
                apply H1r'.
            }
            {
                apply wfΓ.
            }
        }
    }
Qed.

