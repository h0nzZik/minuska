
From Minuska Require Import
    prelude
    spec
    basic_properties
    varsof
    syntax_properties
    properties
    spec_lowlang_interpreter
    spec_interpreter
    basic_matching
    try_match
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

Definition evaluate_sc
    {Σ : StaticModel}
    (ρ : Valuation2)
    (sc : SideCondition2)
    : bool
:=
    match Expression2_evaluate ρ (sc_left sc), Expression2_evaluate ρ (sc_right sc) with
    | Some l, Some r => bool_decide (l = r)
    | _, _ => false
    end
.

Definition evaluate_scs
    {Σ : StaticModel}
    (ρ : Valuation2)
    (scs : list SideCondition2)
    : bool
:=
    forallb (evaluate_sc ρ ) scs
.

Definition try_match_lhs_with_sc
    {Σ : StaticModel}
    {Act : Set}
    (g : TermOver builtin_value)
    (r : RewritingRule2 Act)
    : option Valuation2
:=
    ρ ← try_match_new g (r_from r);
    if evaluate_scs ρ (r_scs r)
    then (Some ρ)
    else None
.

Definition thy_lhs_match_one
    {Σ : StaticModel}
    {Act : Set}
    (e : TermOver builtin_value)
    (Γ : list (RewritingRule2 Act))
    : option (RewritingRule2 Act * Valuation2 * nat)%type
:=
    let froms : list (TermOver BuiltinOrVar)
        := r_from <$> Γ
    in
    let vs : list (option Valuation2)
        := (try_match_lhs_with_sc e) <$> Γ
    in
    let found : option (nat * option Valuation2)
        := list_find isSome vs
    in
    nov ← found;
    let idx : nat := nov.1 in
    let ov : option Valuation2 := nov.2 in
    v ← ov;
    r ← Γ !! idx;
    Some (r, v, idx)
.

(* TODO move *)
Definition list_collect
    {A : Type}
    (l : list (option A))
    : option (list A)
:=
    foldr (fun ox ol => x ← ox; l' ← ol; Some (x::l')) (Some []) l
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

Fixpoint TermOver_join
    {Σ : StaticModel}
    {A : Type}
    (t : TermOver (TermOver A))
    : TermOver A
:=
    match t with
    | t_over x => x
    | t_term s l =>
        t_term s (TermOver_join <$> l)
    end
.

Definition eval_et
    {Σ : StaticModel}
    (ρ : Valuation2)
    (et : TermOver Expression2)
    : option (TermOver builtin_value)
:=
    TermOver_join <$> (TermOver_collect (TermOver_map (Expression2_evaluate ρ) et))
.

Definition naive_interpreter_ext
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (e : TermOver builtin_value)
    : option ((TermOver builtin_value)*nat)
:=
    let oρ : option ((RewritingRule2 Act)*Valuation2*nat)
        := thy_lhs_match_one e Γ in
    match oρ with
    | None => None
    | Some (r,ρ,idx) =>
        e' ← (eval_et ρ (r_to r));
        Some (e',idx)
    end
.

Definition naive_interpreter
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (e : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    ei ← naive_interpreter_ext Γ e;
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
                    unfold vars_of at 1; simpl.
                    ltac1:(rewrite dom_merge_use_left).
                    unfold vars_of at 1 in HH1; simpl in HH1.
                    rewrite HH1.
                    ltac1:(rewrite vars_of_t_term).
                    unfold vars_of in H4 at 1; simpl in H4.
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
                rewrite take_length in HHρ'.
                rewrite zip_with_length in HHρ'.
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
                    rewrite take_length.
                    rewrite zip_with_length.
                    ltac1:(lia).
                }
                rewrite app_length.
                rewrite take_length.
                simpl.
                rewrite zip_with_length.
                rewrite zip_with_length.
                rewrite drop_length.
                rewrite drop_length.
                unfold Valuation2,TermOver in *.
                apply lookup_lt_Some in HHφ'.
                ltac1:(lia).
            }
            {
                unfold Valuation2,TermOver in *.
                rewrite take_length.
                rewrite take_length.
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
    :
    ∀ (v1 v2 : Valuation2) (b : SideCondition2),
            Valuation2_restrict v1 (vars_of b) = Valuation2_restrict v2 (vars_of b) ->
            satisfies v1 () b -> satisfies v2 () b
.
Proof.
    intros.
    unfold satisfies in *; simpl in *.
    unfold Valuation2_restrict in H.
    destruct X as [H1 H2].
    unfold is_true in *.
    unfold isSome in *.
    destruct (Expression2_evaluate v1 (sc_left b)) eqn:Heq>[|ltac1:(congruence)].
    clear H2.
    symmetry in H1.
    apply Expression2_evalute_strip in Heq.
    apply Expression2_evalute_strip in H1.
    assert (H'1:
        filter (λ x : variable * TermOver builtin_value, x.1 ∈ vars_of (sc_left b)) v1 =
        filter (λ x : variable * TermOver builtin_value, x.1 ∈ vars_of (sc_left b)) v2
    ).
    {
        unfold Valuation2 in *.
        apply map_eq.
        intros x.
        destruct (filter (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of (sc_left b)) v1 !! x)
            eqn:Heq1,
            (filter (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of (sc_left b)) v2 !! x)
            eqn:Heq2
        .
        {
            rewrite map_lookup_filter in Heq1.
            rewrite map_lookup_filter in Heq2.
            rewrite bind_Some in Heq1.
            rewrite bind_Some in Heq2.
            destruct Heq1 as [z [H1z H2z]].
            destruct Heq2 as [z' [H1z' H2z']].
            rewrite bind_Some in H2z.
            rewrite bind_Some in H2z'.
            simpl in *.
            destruct H2z as [v [H1v H2v]].
            destruct H2z' as [w [H1w H2w]].
            ltac1:(simplify_eq/=).
            assert (H0:
                (filter
                    (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of b)
                    v1
                ) !! x = Some t0
            ).
            {
                rewrite map_lookup_filter.
                rewrite bind_Some.
                exists t0.
                split>[exact H1z|].
                rewrite bind_Some.
                simpl.
                ltac1:(unshelve(eexists)).
                {
                    unfold vars_of; simpl.
                    rewrite elem_of_union.
                    left.
                    assumption.
                }
                {
                    split>[|reflexivity].
                    ltac1:(simplify_option_eq).
                    { f_equal; apply proof_irrelevance. }
                    {
                        ltac1:(contradiction).
                    }
                    {
                        ltac1:(exfalso).
                        unfold vars_of in H2; simpl in H2.
                        ltac1:(set_solver).
                    }
                }
            }
            rewrite H in H0.
            clear - H1z' H0.
            rewrite map_lookup_filter in H0.
            ltac1:(simplify_option_eq).
            reflexivity.
        }
        {
            rewrite map_lookup_filter in Heq1.
            rewrite map_lookup_filter in Heq2.
            rewrite bind_Some in Heq1.
            rewrite bind_None in Heq2.
            ltac1:(exfalso).
            destruct Heq1 as [y [H1y H2y]].
            ltac1:(simplify_option_eq).
            destruct Heq2 as [Heq2|Heq2].
            {
                assert (Hfil : filter (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of b) v1 !! x = Some t0).
                {
                    rewrite map_lookup_filter.
                    rewrite bind_Some.
                    exists t0.
                    split>[assumption|].
                    ltac1:(simplify_option_eq).
                    {   reflexivity. }
                    {
                        unfold vars_of in H3; simpl in H3.
                        ltac1:(exfalso; clear - H3 H2; set_solver).
                    }
                }
                rewrite H in Hfil.
                rewrite map_lookup_filter in Hfil.
                rewrite Heq2 in Hfil.
                simpl in Hfil.
                inversion Hfil.
            }
            {
                destruct Heq2 as [x0 [H1x0 H2x0]].
                inversion H2x0.
            }
        }
        {
            rewrite map_lookup_filter in Heq1.
            rewrite map_lookup_filter in Heq2.
            rewrite bind_Some in Heq2.
            rewrite bind_None in Heq1.
            ltac1:(exfalso).
            destruct Heq2 as [y [H1y H2y]].
            ltac1:(simplify_option_eq).
            destruct Heq1 as [Heq2|Heq2].
            {
                assert (Hfil : filter (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of b) v2 !! x = Some t0).
                {
                    rewrite map_lookup_filter.
                    rewrite bind_Some.
                    exists t0.
                    split>[assumption|].
                    ltac1:(simplify_option_eq).
                    {   reflexivity. }
                    {
                        unfold vars_of in H3; simpl in H3.
                        ltac1:(exfalso; clear - H3 H2; set_solver).
                    }
                }
                rewrite <- H in Hfil.
                rewrite map_lookup_filter in Hfil.
                rewrite Heq2 in Hfil.
                simpl in Hfil.
                inversion Hfil.
            }
            {
                destruct Heq2 as [x0 [H1x0 H2x0]].
                inversion H2x0.
            }
        }
        { reflexivity. }
    }
    assert (H'2:
        filter (λ x : variable * TermOver builtin_value, x.1 ∈ vars_of (sc_right b)) v1 =
        filter (λ x : variable * TermOver builtin_value, x.1 ∈ vars_of (sc_right b)) v2
    ).
    {
        unfold Valuation2 in *.
        apply map_eq.
        intros x.
        destruct (filter (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of (sc_right b)) v1 !! x)
            eqn:Heq1,
            (filter (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of (sc_right b)) v2 !! x)
            eqn:Heq2
        .
        {
            rewrite map_lookup_filter in Heq1.
            rewrite map_lookup_filter in Heq2.
            rewrite bind_Some in Heq1.
            rewrite bind_Some in Heq2.
            destruct Heq1 as [z [H1z H2z]].
            destruct Heq2 as [z' [H1z' H2z']].
            rewrite bind_Some in H2z.
            rewrite bind_Some in H2z'.
            simpl in *.
            destruct H2z as [v [H1v H2v]].
            destruct H2z' as [w [H1w H2w]].
            ltac1:(simplify_eq/=).
            assert (H0:
                (filter
                    (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of b)
                    v1
                ) !! x = Some t0
            ).
            {
                rewrite map_lookup_filter.
                rewrite bind_Some.
                exists t0.
                split>[exact H1z|].
                rewrite bind_Some.
                simpl.
                ltac1:(unshelve(eexists)).
                {
                    unfold vars_of; simpl.
                    rewrite elem_of_union.
                    right.
                    assumption.
                }
                {
                    split>[|reflexivity].
                    ltac1:(simplify_option_eq).
                    { f_equal; apply proof_irrelevance. }
                    {
                        ltac1:(contradiction).
                    }
                    {
                        ltac1:(exfalso).
                        unfold vars_of in H2; simpl in H2.
                        ltac1:(set_solver).
                    }
                }
            }
            rewrite H in H0.
            clear - H1z' H0.
            rewrite map_lookup_filter in H0.
            ltac1:(simplify_option_eq).
            reflexivity.
        }
        {
            rewrite map_lookup_filter in Heq1.
            rewrite map_lookup_filter in Heq2.
            rewrite bind_Some in Heq1.
            rewrite bind_None in Heq2.
            ltac1:(exfalso).
            destruct Heq1 as [y [H1y H2y]].
            ltac1:(simplify_option_eq).
            destruct Heq2 as [Heq2|Heq2].
            {
                assert (Hfil : filter (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of b) v1 !! x = Some t0).
                {
                    rewrite map_lookup_filter.
                    rewrite bind_Some.
                    exists t0.
                    split>[assumption|].
                    ltac1:(simplify_option_eq).
                    {   reflexivity. }
                    {
                        unfold vars_of in H3; simpl in H3.
                        ltac1:(exfalso; clear - H3 H2; set_solver).
                    }
                }
                rewrite H in Hfil.
                rewrite map_lookup_filter in Hfil.
                rewrite Heq2 in Hfil.
                simpl in Hfil.
                inversion Hfil.
            }
            {
                destruct Heq2 as [x0 [H1x0 H2x0]].
                inversion H2x0.
            }
        }
        {
            rewrite map_lookup_filter in Heq1.
            rewrite map_lookup_filter in Heq2.
            rewrite bind_Some in Heq2.
            rewrite bind_None in Heq1.
            ltac1:(exfalso).
            destruct Heq2 as [y [H1y H2y]].
            ltac1:(simplify_option_eq).
            destruct Heq1 as [Heq2|Heq2].
            {
                assert (Hfil : filter (λ x0 : variable * TermOver builtin_value, x0.1 ∈ vars_of b) v2 !! x = Some t0).
                {
                    rewrite map_lookup_filter.
                    rewrite bind_Some.
                    exists t0.
                    split>[assumption|].
                    ltac1:(simplify_option_eq).
                    {   reflexivity. }
                    {
                        unfold vars_of in H3; simpl in H3.
                        ltac1:(exfalso; clear - H3 H2; set_solver).
                    }
                }
                rewrite <- H in Hfil.
                rewrite map_lookup_filter in Hfil.
                rewrite Heq2 in Hfil.
                simpl in Hfil.
                inversion Hfil.
            }
            {
                destruct Heq2 as [x0 [H1x0 H2x0]].
                inversion H2x0.
            }
        }
        { reflexivity. }
    }
    rewrite H'1 in Heq.
    rewrite H'2 in H1.

    eapply Expression2_evaluate_extensive_Some in Heq.
    rewrite Heq.
    eapply Expression2_evaluate_extensive_Some in H1.
    rewrite H1.
    (repeat split).
    unfold Valuation2 in *.
    apply map_filter_subseteq.
    unfold Valuation2 in *.
    apply map_filter_subseteq.
Qed.


Lemma try_match_lhs_with_sc_complete
    {Σ : StaticModel}
    {Act : Set}
    (g : TermOver builtin_value)
    (r : RewritingRule2 Act)
    (ρ : Valuation2)
    :
    vars_of (r_scs r) ⊆ vars_of (r_from r) ->
    satisfies ρ g (r_from r) ->
    satisfies ρ () (r_scs r) ->
    {
        ρ' : (gmap variable (TermOver builtin_value)) &
        vars_of ρ' = vars_of (r_from r) ∧
        ρ' ⊆ ρ ∧
        try_match_lhs_with_sc g r = Some ρ'
    }   
.
Proof.
    (*
        If a side condition `sc` contains a variable
        that is not in the 'from' part `fr` of the rule,
        then the side condition evaluates to `false`.
        Why?
        Because if it evaluated to `true`,
        then `vars_of sc ⊆ vars_of ρ `.
        But vars_of ρ = vars_of fr, because of
        the NOOTA property.
    *)
    intros Hn H1 H2.
    apply try_match_new_complete in H1.
    destruct H1 as [ρ1 [H1ρ1 H2ρ1]].
    destruct H2ρ1 as [H2ρ1 H3ρ2].
    (*destruct (matchesb ρ1 () (fr_scs r)) eqn:Hm.*)
    {
        
        unfold try_match_lhs_with_sc.
        (* ltac1:(setoid_rewrite bind_Some). *)
        exists ρ1.
        split.
        {
            unfold Valuation2 in *.
            rewrite H1ρ1.
            reflexivity.
        }
        split.
        {
            assumption.
        }
        apply bind_Some_T_2.
        exists ρ1.
        split>[apply H3ρ2|].
        unfold matchesb in *; simpl in *.
        ltac1:(case_match).
        { reflexivity. }
        unfold satisfies in H2; simpl in H2.
        unfold evaluate_scs in H.
        rewrite <- not_true_iff_false in H.
        ltac1:(exfalso).
        apply H. clear H.
        rewrite forallb_forall.
        intros x Hx.
        rewrite <- elem_of_list_In in Hx.
        specialize (H2 x Hx) as H2x.

        apply sc_satisfies_insensitive with (v2 := ρ1) in H2x.
        {
            unfold satisfies in H2x. simpl in H2x. unfold evaluate_sc.
            
            ltac1:(repeat case_match; destruct_and?; simplify_eq/=).
            {
                apply bool_decide_eq_true.
                reflexivity.
            }
            {
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
                    unfold vars_of in H1ρ1 at 1; simpl in H1ρ1.
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
                    rewrite elem_of_list_lookup in Hx.
                    destruct Hx as [j Hj].
                    apply take_drop_middle in Hj.
                    rewrite <- Hj in Hn. clear Hj.
                    unfold vars_of at 1 in Hn; simpl in Hn.
                    rewrite fmap_app in Hn.
                    rewrite union_list_app in Hn.
                    rewrite fmap_cons in Hn.
                    rewrite union_list_cons in Hn.
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
                destruct (ρ !! i) as [y|] eqn:Hρi, (ρ1 !! i) as [z|] eqn:Hρ1i;
                    ltac1:(simplify_option_eq);
                    reflexivity.
            }
            
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
    {Act : Set}
    (e : TermOver builtin_value)
    (Γ : RewritingTheory2 Act)
    (wfΓ : RewritingTheory2_wf Γ)
    :
    thy_lhs_match_one e Γ = None ->
    notT { r : RewritingRule2 Act & { ρ : Valuation2 &
        ((r ∈ Γ) * (satisfies ρ e (r_from r)) * (satisfies ρ tt (r_scs r)))%type
    } }
        
.
Proof.
    unfold thy_lhs_match_one.
    intros H [r [ρ [[Hin HContra1] HContra2]]].
    destruct (list_find isSome (try_match_lhs_with_sc e <$> Γ)) eqn:Heqfound.
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
        clear H.
        rewrite list_find_None in Heqfound.
        rewrite Forall_forall in Heqfound.
        ltac1:(rename HContra1 into Hsat1).
        ltac1:(rename HContra2 into Hsat2).
        apply try_match_new_complete in Hsat1.
        destruct Hsat1 as [ρ' [H1 [H2 H3]]].

        assert (Hc := try_match_lhs_with_sc_complete e r).
        specialize (Hc ρ').
        ltac1:(ospecialize (Hc _)).
        {
            unfold RewritingTheory_wf in wfΓ.
            unfold is_true in wfΓ.
            specialize (wfΓ r).
            unfold RewritingRule_wf in wfΓ.
            specialize (wfΓ Hin).
            apply wfΓ.
        }
        assert (H3' := H3).
        apply try_match_new_correct in H3'.
        specialize (Hc H3').
        ltac1:(ospecialize (Hc _)).
        {
            unfold satisfies; simpl.
            intros x Hx.
            eapply sc_satisfies_insensitive in Hsat2 as Hsat2'. apply Hsat2'.
            unfold RewritingTheory_wf in wfΓ.
            assert (Htmp := valuation_restrict_vars_of_self ρ' ρ H2).
            eapply Valuation2_restrict_eq_subseteq in Htmp.
            symmetry. apply Htmp.
            {
                rewrite H1.
                
                unfold is_true in wfΓ.
                specialize (wfΓ r).
                unfold RewritingRule_wf in wfΓ.
                specialize (wfΓ Hin).
                unfold RewritingRule2_wf in *.
                destruct wfΓ as [wf1 wf2].
                unfold RewritingRule2_wf1 in *.
                unfold RewritingRule2_wf2 in *.
                eapply transitivity>[|apply wf1].
                unfold vars_of at 2; simpl.
                rewrite elem_of_list_lookup in Hx.
                destruct Hx as [i Hi].
                apply take_drop_middle in Hi.
                rewrite <- Hi.
                ltac1:(rewrite fmap_app fmap_cons union_list_app union_list_cons).
                ltac1:(set_solver).
            }
            { exact Hx. }
        }
        destruct Hc as [ρ'' [H1ρ'' [H2ρ'' H3ρ'']]].

        specialize (Heqfound (Some ρ'')).
        ltac1:(ospecialize (Heqfound _)).
        {
            clear Heqfound.
            
            unfold Valuation2 in *.
            rewrite elem_of_list_fmap.
            exists (r).
            split.
            {
                symmetry.
                exact H3ρ''.
            }
            {
                exact Hin.
            }
        }
        apply Heqfound.
        unfold isSome.
        reflexivity.
    }
Qed.


Lemma fmap_Some_T_1 (A B : Type) (f : A → B) (mx : option A) (y : B):
  f <$> mx = Some y ->
  {x : A & mx = Some x ∧ y = f x }
.
Proof.
    intros H.
    destruct mx; simpl in *.
    {
        inversion H; subst; clear H.
        exists a.
        split;reflexivity.
    }
    {
        inversion H.
    }
Qed.

Lemma evaluate_scs_correct
    {Σ : StaticModel}
    (ρ : Valuation2)
    (scs : list SideCondition2)
    :
    evaluate_scs ρ scs = true ->
    satisfies ρ () scs
.
Proof.
    intros HH.
    unfold evaluate_scs in HH.
    rewrite forallb_forall in HH.
    unfold satisfies; simpl.
    intros x Hx.
    specialize (HH x).
    rewrite elem_of_list_In in Hx.
    specialize (HH Hx).
    
    unfold evaluate_sc in HH.
    unfold satisfies; simpl.
    ltac1:(repeat case_match).
    {
        apply bool_decide_eq_true in HH.
        subst.
        (repeat split).
    }
    {
        inversion HH.
    }
    {
        inversion HH.
    }
Qed.

Lemma thy_lhs_match_one_Some
    {Σ : StaticModel}
    {Act : Set}
    (e : TermOver builtin_value)
    (Γ : list (RewritingRule2 Act))
    (r : RewritingRule2 Act)
    (ρ : Valuation2)
    (rule_idx : nat)
    :
    thy_lhs_match_one e Γ = Some (r, ρ, rule_idx) ->
    ((r ∈ Γ) * (satisfies ρ e (r_from r)) * (satisfies ρ tt (r_scs r)))%type
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
                rewrite elem_of_list_lookup.
                exists rule_idx. apply Hot1.
            }
            {
                destruct H12 as [H1 H2].
                unfold is_true, isSome in H1.
                destruct (try_match_lhs_with_sc e r) eqn:HTM>[|inversion H1].
                clear H1.
                inversion H1ρ'; subst; clear H1ρ'.
                unfold try_match_lhs_with_sc in HTM.
                apply bind_Some_T_1 in HTM.
                destruct HTM as [x [H1x H2x]].
                destruct (evaluate_scs x (r_scs r)) eqn:Heq.
                {
                    inversion H2x; subst; clear H2x.
                    apply try_match_new_correct in H1x.
                    assumption.
                }
                {
                    inversion H2x.
                }         
            }
        }
        {
            destruct H12 as [H1 H2].
            unfold is_true, isSome in H1.
            destruct (try_match_lhs_with_sc e r) eqn:HTM>[|inversion H1].
            clear H1.
            inversion H1ρ'; subst; clear H1ρ'.
            unfold try_match_lhs_with_sc in HTM.
            apply bind_Some_T_1 in HTM.
            destruct HTM as [x [H1x H2x]].
            destruct (evaluate_scs x (r_scs r)) eqn:Heq.
            {
                inversion H2x; subst; clear H2x.
                apply evaluate_scs_correct in Heq.
                exact Heq.
            }
            {
                inversion H2x.
            }
        }
    }
Qed.

Lemma list_collect_Some_length
    {A : Type}
    (l : list (option A))
    (l' : list A)
    :
    list_collect l = Some l' ->
    length l = length l'
.
Proof.
    revert l'.
    induction l; intros l' HH; destruct l'; simpl in *.
    { reflexivity. }
    {
        ltac1:(simplify_eq/=).
    }
    {
        ltac1:(simplify_option_eq).
    }
    {
        ltac1:(simplify_option_eq).
        erewrite IHl.
        reflexivity.
        reflexivity.
    }
Qed.

Lemma eval_et_correct
    {Σ : StaticModel}
    (ρ : Valuation2)
    (et : TermOver Expression2)
    (g : TermOver builtin_value)
    :
    eval_et ρ et = Some g ->
    satisfies ρ g et
.
Proof.
    intros HH.
    unfold satisfies; simpl.
    unfold eval_et in HH.
    revert g HH.
    induction et; simpl in *; intros g HH.
    {
        destruct (Expression2_evaluate ρ a) eqn:Heq.
        {
            simpl in *.
            ltac1:(simplify_eq/=).
            ltac1:(simp sat2E).
        }
        {
            simpl in *.
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
            split>[reflexivity|].
            rewrite fmap_length.
            ltac1:(rename H1 into l1).
            split.
            {
                apply list_collect_Some_length in Heqo0.
                rewrite fmap_length in Heqo0.
                rewrite map_length in Heqo0.
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
                    destruct (list_collect (TermOver_collect <$> map (TermOver_map (Expression2_evaluate ρ)) l)) eqn:Heq';
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

                }
            }
        }
    }
Qed.

Lemma eval_et_correct_2
    {Σ : StaticModel}
    (ρ : Valuation2)
    (et : TermOver Expression2)
    (g : TermOver builtin_value)
    :
    satisfies ρ g et ->
    eval_et ρ et = Some g
.
Proof.
    revert g.
    induction et; intros g; destruct g; simpl in *; intros HH.
    {
        unfold satisfies in HH. simpl in HH.
        ltac1:(simp sat2E in HH).
        unfold eval_et. simpl. rewrite HH. simpl. reflexivity.
    }
    {
        unfold satisfies in HH. simpl in HH.
        ltac1:(simp sat2E in HH).
        unfold eval_et. simpl. rewrite HH. simpl. reflexivity.
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
                ltac1:(rewrite [TermOver_map _ _]/=).
                rewrite fmap_Some.
                simpl.
                ltac1:(setoid_rewrite bind_Some).
                ltac1:(setoid_rewrite bind_Some).
                ltac1:(setoid_rewrite bind_Some).

                specialize (IH1 _ HH3).
                rewrite fmap_Some in IH1.
                destruct IH1 as [y [H1y H2y]].

                rewrite fmap_Some in IHl.
                destruct IHl as [x [H1x H2x]].
                ltac1:(setoid_rewrite H1y).
                simpl in H1x.
                rewrite bind_Some in H1x.
                destruct H1x as [z [H1z H2z]].
                ltac1:(setoid_rewrite H1z).
                exists (t_term s (y::z)).
                subst t.
                simpl.
                ltac1:(simplify_eq/=).
                (repeat split).
                exists (y::z).
                (repeat split).
                exists y.
                (repeat split).
                exists z.
                (repeat split).
            }
        }
    }
Qed.


Lemma naive_interpreter_sound
    {Σ : StaticModel}
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
        intros e1 e2.
        intros Hbind.
        apply bind_Some_T_1 in Hbind.
        destruct Hbind as [x [H1x H2x]].
        destruct (thy_lhs_match_one e1 Γ) eqn:Hmatch.
        {
            destruct p as [[r ρ] idx].
            apply thy_lhs_match_one_Some in Hmatch.
            inversion H2x; subst; clear H2x.
            apply bind_Some_T_1 in H1x.
            destruct H1x as [y [H1y H2y]].
            inversion H2y; subst; clear H2y.
            simpl.
            unfold rewriting_relation_flat.
            exists r.
            destruct Hmatch as [[Hin Hm1] Hm2].
            exists (r_act r).
            split>[apply Hin|].
            unfold rewrites_to.
            exists ρ.
            unfold rewrites_in_valuation_under_to.
            apply eval_et_correct in H1y.
            (repeat split); try assumption.
            apply Hm2. exact H.
            apply Hm2. exact H.
        }
        {
            inversion H1x.
        }
    }
    {
        intros e Hstuck.
        destruct (thy_lhs_match_one e Γ) eqn:Hmatch>[|reflexivity].
        {
            destruct p as [[r ρ] rule_idx].
            {
                apply thy_lhs_match_one_Some in Hmatch.
                destruct Hmatch as [Hin Hsat].
                assert (Hts := @thy_lhs_match_one_Some Σ).
                unfold rewriting_relation in Hstuck.
                unfold rewrites_to in Hstuck.
                unfold rewrites_in_valuation_under_to in Hstuck.
                assert (Hev := eval_et_correct ρ (r_to r)).
                ltac1:(cut (~ ∃ g', eval_et ρ (r_to r) = Some g')).
                {
                    intros HContra. clear -HContra.
                    rewrite <- eq_None_ne_Some.
                    intros x HC.
                    rewrite bind_Some in HC.
                    destruct HC as [x0 [HC1 HC2]].
                    inversion HC2; subst; clear HC2.
                    rewrite bind_Some in HC1.
                    ltac1:(naive_solver).
                }
                intros HContra.
                destruct HContra as [pg' Hg'].
                apply Hev in Hg'.
                clear Hev.
                apply Hstuck. clear Hstuck.
                exists pg'. exists r.
                exists (r_act r).
                destruct Hin.
                split>[assumption|].
                exists ρ.
                repeat split; try assumption.
                { apply Hsat. assumption. }
                { apply Hsat. assumption. }
            }
        }
    }
    {
        intros e Hnotstuck.
        unfold naive_interpreter.

        destruct Hnotstuck as [e' He'].
        unfold rewriting_relation_flat in He'.
        destruct He' as [r' [a [H1r' H2r']]].
        unfold rewrites_to in H2r'.
        destruct H2r' as [ρ' Hρ'].
        unfold rewrites_in_valuation_under_to in Hρ'.

        
        destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
        {
            destruct p as [[r ρ] rule_idx]; cbn in *.
            apply thy_lhs_match_one_Some in Hmatch.
            destruct Hmatch as [Hin Hsat].
            
            
            destruct (eval_et ρ (r_to r)) eqn:Heval.
            {
                eexists. reflexivity.
            }
            {
                ltac1:(exfalso).
                unfold RewritingTheory_wf in wfΓ.
                unfold RewritingRule_wf in wfΓ.
                specialize (wfΓ r).
                destruct Hin.
                specialize (wfΓ ltac:(assumption)).
                destruct wfΓ as [wf1 wf2].
                unfold RewritingRule_wf2 in wf2.
                specialize (wf2 e ρ).
                specialize (wf2 ltac:(assumption) ltac:(assumption)).
                destruct wf2 as [g' Hg'].
                assert (Hn : notT { g : _ & eval_et ρ (r_to r) = Some g } ).
                {
                    intros HContra.
                    destruct HContra as [g HContra].
                    rewrite Heval in HContra.
                    inversion HContra.
                }
                apply Hn. clear Hn.
                exists g'.
                apply eval_et_correct_2 in Hg'.
                apply Hg'.
            }
        }
        {
            ltac1:(exfalso).
            destruct Hρ' as [[[H1 H2] H3] H4].
            apply thy_lhs_match_one_None in Hmatch.
            apply Hmatch.
            exists r'. exists ρ'.
            (repeat split); try assumption.
            apply H3.
            assumption.
            apply H3.
            assumption.
            assumption.
        }
    }
Qed.



Lemma vars_of_E2conv
    {Σ : StaticModel}
    (e : Expression2)
    :
    vars_of (Expression2_to_Expression e) = vars_of e
.
Proof.
    induction e; unfold vars_of in *; simpl in *;
        (ltac1:(set_solver)).
Qed.

Lemma vars_of_sc2_to_sc
    {Σ : StaticModel}
    {Act : Set}
    (r2 : RewritingRule2 Act)
    :
    vars_of (sc2_to_sc <$> r_scs r2) ⊆ vars_of (r_scs r2)
.
Proof.
    clear Hwf1.
    unfold vars_of in *; simpl in *.
    unfold vars_of in *; simpl in *.
    unfold vars_of_SideCondition.
    rewrite elem_of_subseteq.
    intros x Hx.
    rewrite elem_of_union_list in Hx.
    rewrite elem_of_union_list.
    destruct Hx as [X [H1X H2x]].
    rewrite elem_of_list_fmap in H1X.
    destruct H1X as [y [H1y H2y]].
    subst X.
    destruct y; simpl in *.
    rewrite elem_of_list_fmap in H2y.
    destruct H2y as [y [H1'y H2'y]].
    destruct c; simpl in *.
    destruct y; simpl in *.
    inversion H1'y; subst; clear H1'y.
    ltac1:(exists (vars_of
        (apeq (Expression2_to_Expression sc_left)
        (Expression2_to_Expression sc_right)))).
    split>[|assumption].
    destruct r2; simpl in *.
    rewrite elem_of_list_fmap.
    eexists;split>[|exact H2'y].
    unfold vars_of; simpl.
    rewrite vars_of_E2conv.
    rewrite vars_of_E2conv.
    reflexivity.
Qed.

Lemma fmap_prettify_uglify_val
    {Σ : StaticModel}
    (ρ : Valuation2)
    :
    (prettify <$> (uglify' <$> ρ)) = ρ
.
Proof.
    unfold Valuation2 in *.
    rewrite <- map_fmap_compose.
    rewrite compose_prettify_uglify.
    rewrite map_fmap_id.
    reflexivity.
Qed.

Lemma fmap_uglify_prettify_val
    {Σ : StaticModel}
    (ρ : Valuation)
    :
    uglify' <$> (prettify <$> (ρ)) = ρ
.
Proof.
    unfold Valuation2 in *.
    rewrite <- map_fmap_compose.
    rewrite compose_uglify_prettify.
    rewrite map_fmap_id.
    reflexivity.
Qed.


#[export]
Instance cancel_fr_r
    {Σ : StaticModel}
    {Act : Set}
    : Cancel eq (@fr_to_r _ Act) r_to_fr
.
Proof.
    intros r. destruct r. simpl.
    rewrite (cancel prettify uglify').
    rewrite (cancel prettify uglify').
    rewrite (cancel (TermOver_map Expression_to_Expression2) (TermOver_map Expression2_to_Expression)).
    f_equal.
    induction r_scs; simpl.
    { reflexivity. }
    {
        do 2 (rewrite (cancel Expression_to_Expression2 Expression2_to_Expression)).
        f_equal.
        {
            destruct a; reflexivity.
        }
        apply IHr_scs.
    }
Qed.

Lemma naive_interpreter_sound
    {Σ : StaticModel}
    {Act : Set}
    {_eA : EqDecision Act}
    (Γ : list (RewritingRule2 Act))
    : Interpreter_sound Γ (naive_interpreter Γ).
Proof.
    intros Hwf.
    assert(Hsound := flat_naive_interpreter_sound (fmap r_to_fr Γ)).
    ltac1:(ospecialize (Hsound _)).
    {
        clear -Hwf _eA.
        unfold RewritingTheory_wf.
        unfold RewritingTheory2_wf in Hwf.
        intros r Hr.
        apply elem_of_list_fmap_T_1 in Hr.
        destruct Hr as [r2 [H1r2 H2r2]].
        subst r.
        specialize (Hwf _ H2r2). clear H2r2.
        unfold RewritingRule_wf.
        unfold RewritingRule2_wf in Hwf.
        destruct Hwf as [Hwf1 Hwf2].
        split.
        {
            unfold RewritingRule_wf1.
            unfold RewritingRule2_wf1 in Hwf1.
            simpl.
            ltac1:(rewrite vars_of_uglify').
            eapply transitivity>[|apply Hwf1].
            apply vars_of_sc2_to_sc.
        }
        {
            unfold RewritingRule_wf2.
            unfold RewritingRule2_wf2 in Hwf2.
            intros g ρ.
            specialize (Hwf2 (prettify g) (fmap prettify ρ)).
            intros H1 H2.
            ltac1:(ospecialize (Hwf2 _ _)).
            {
                unfold satisfies; simpl.
                apply uglify_sat2B.
                rewrite fmap_uglify_prettify_val.
                rewrite (cancel uglify' prettify).
                apply H1.
            }
            {
                unfold satisfies; simpl.
                unfold satisfies in H2; simpl in H2.
                intros x Hx.
                specialize (H2 (sc2_to_sc x)).
                ltac1:(ospecialize (H2 _)).
                {
                    clear H2.
                    rewrite elem_of_list_fmap.
                    exists x.
                    split>[reflexivity|exact Hx].
                }
                unfold satisfies; simpl.
                unfold satisfies in H2; simpl in H2.
                unfold satisfies in H2; simpl in H2.
                do 2 (rewrite Expression2_Expression_evaluate).
                rewrite (fmap_uglify_prettify_val).
                destruct H2 as [H21 H22].
                rewrite H21.
                simpl.
                split>[reflexivity|].
                unfold isSome in H22.
                destruct (Expression_evaluate ρ (Expression2_to_Expression (sc_left x)))>
                    [|inversion H22].
                rewrite <- H21. simpl. reflexivity.
            }
            destruct Hwf2 as [g' H3].
            exists (uglify' g').
            unfold satisfies in H3; simpl in H3.
            apply sat2E_uglify in H3.
            rewrite fmap_uglify_prettify_val in H3.
            apply H3.
        }
    }
    unfold Interpreter_sound'.
    unfold FlatInterpreter_sound' in Hsound.
    destruct Hsound as [[Hsound1 Hsound2] Hsound3].
    repeat split.
    {
        intros e1 e2 HH.
        specialize (Hsound1 (uglify' e1) (uglify' e2)).
        unfold naive_interpreter in HH.
        apply bind_Some_T_1 in HH.
        destruct HH as [[t n] [HH1 HH2]].
        simpl in *.
        injection HH2 as HH2. subst e2.
        ltac1:(ospecialize (Hsound1 _)).
        {
            apply bind_Some_T_2.
            exists (t, n).
            rewrite HH1.
            split>[reflexivity|].
            simpl.
            rewrite (cancel uglify' prettify).
            reflexivity.
        }
        rewrite (cancel uglify' prettify) in Hsound1.
        unfold rewriting_relation_flat in Hsound1.
        destruct Hsound1 as [r [a [HH2 HH3]]].
        unfold rewriting_relation.
        exists (fr_to_r r).
        exists a.
        split.
        {
            rewrite elem_of_list_fmap in HH2.
            destruct HH2 as [y [HH2 HH2']].
            subst r.
            rewrite (cancel fr_to_r r_to_fr).
            exact HH2'.
        }
        unfold rewrites_to.
        unfold flattened_rewrites_to in HH3.
        destruct HH3 as [ρ Hρ].
        exists (fmap prettify ρ).
        unfold rewrites_in_valuation_under_to.
        unfold flattened_rewrites_in_valuation_under_to in Hρ.
        destruct Hρ as [[[HH4 HH5] HH6] HH7].
        unfold satisfies; simpl.
        split.
        split.
        split.
        {
            apply uglify_sat2B.
            rewrite fmap_uglify_prettify_val.
            destruct r;  simpl in *.
            rewrite (cancel uglify' prettify).
            exact HH4.
        }
        {
            apply uglify_sat2E.
            rewrite fmap_uglify_prettify_val.
            destruct r;  simpl in *.
            rewrite (cancel (TermOver_map Expression2_to_Expression) (TermOver_map Expression_to_Expression2)).
            unfold satisfies; simpl.
            do 2 (rewrite (cancel uglify' prettify)).
            exact HH5.
        }
        {
            intros x Hx.
            unfold satisfies in HH6; simpl in HH6.
            specialize (HH6 (sc2_to_sc x)).
            ltac1:(ospecialize (HH6 _)).
            {
                destruct r; simpl in *.
                rewrite elem_of_list_fmap in Hx.
                destruct Hx as [y [H1y H2y]].
                subst x.
                rewrite (cancel sc2_to_sc sc_to_sc2).
                exact H2y.
            }
            unfold satisfies; simpl.
            unfold satisfies in HH6; simpl in HH6.
            unfold satisfies in HH6; simpl in HH6.
            rewrite Expression2_Expression_evaluate.
            rewrite Expression2_Expression_evaluate.
            rewrite (fmap_uglify_prettify_val).
            split.
            {
                apply f_equal.
                apply HH6.
            }
            {
                destruct HH6 as [HH61 HH62].
                unfold isSome in HH62.
                destruct (Expression_evaluate ρ (Expression2_to_Expression (sc_left x)))>
                    [|inversion HH62].
                reflexivity.
            }
        }
        {
            destruct r; simpl in *.
            apply HH7.
        }
    }
    {
        intros e Hstuck.
        specialize (Hsound2 (uglify' e)).
        ltac1:(ospecialize (Hsound2 _)).
        {
            unfold stuck in Hstuck.
            unfold flat_stuck.
            intros HContra. apply Hstuck. clear Hstuck.
            unfold not_stuck. unfold not_stuck_flat in HContra.
            destruct HContra as [e' He'].
            exists (prettify e').
            unfold rewriting_relation.
            unfold rewriting_relation_flat in He'.
            destruct He' as [r [a [Hrewr1 Hrewr2]]].
            exists (fr_to_r r).
            exists a.
            split.
            {
                rewrite elem_of_list_fmap in Hrewr1.
                destruct Hrewr1 as [y [H1y H2y]].
                subst r.
                rewrite (cancel fr_to_r r_to_fr).
                exact H2y.
            }
            {
                unfold rewrites_to.
                unfold flattened_rewrites_to in Hrewr2.
                destruct Hrewr2 as [ρ Hρ].
                exists (fmap prettify ρ).
                unfold flattened_rewrites_in_valuation_under_to in Hρ.
                unfold rewrites_in_valuation_under_to.


                (* TODO this is a duplication *)
                destruct Hρ as [[[HH4 HH5] HH6] HH7].
                unfold satisfies; simpl.
                split. split. split.
                {
                    apply uglify_sat2B.
                    rewrite fmap_uglify_prettify_val.
                    destruct r;  simpl in *.
                    rewrite (cancel uglify' prettify).
                    exact HH4.
                }
                {
                    apply uglify_sat2E.
                    rewrite fmap_uglify_prettify_val.
                    destruct r;  simpl in *.
                    rewrite (cancel (TermOver_map Expression2_to_Expression) (TermOver_map Expression_to_Expression2)).
                    unfold satisfies; simpl.
                    do 2 (rewrite (cancel uglify' prettify)).
                    exact HH5.
                }
                {
                    intros x Hx.
                    unfold satisfies in HH6; simpl in HH6.
                    specialize (HH6 (sc2_to_sc x)).
                    ltac1:(ospecialize (HH6 _)).
                    {
                        destruct r; simpl in *.
                        rewrite elem_of_list_fmap in Hx.
                        destruct Hx as [y [H1y H2y]].
                        subst x.
                        rewrite (cancel sc2_to_sc sc_to_sc2).
                        exact H2y.
                    }
                    unfold satisfies; simpl.
                    unfold satisfies in HH6; simpl in HH6.
                    rewrite Expression2_Expression_evaluate.
                    rewrite Expression2_Expression_evaluate.
                    rewrite (fmap_uglify_prettify_val).
                    unfold satisfies in HH6; simpl in HH6.
                    destruct HH6 as [HH61 HH62].
                    split.
                    {
                        apply f_equal.
                        apply HH61.
                    }
                    {
                        unfold isSome in HH62.
                        destruct (Expression_evaluate ρ (Expression2_to_Expression (sc_left x)))>
                            [|inversion HH62].
                        reflexivity.
                    }
                }
                {
                    destruct r; simpl in *.
                    apply HH7.
                }
            }
        }
        unfold naive_interpreter.
        unfold flat_naive_interpreter in Hsound2.
        rewrite bind_None in Hsound2.
        rewrite bind_None.
        destruct Hsound2 as [Hsound2|Hsound2].
        {
            left. exact Hsound2.
        }
        {
            right.
            destruct Hsound2 as [[g n] [HH1 HH2]].
            inversion HH2.
        }
    }
    {
        intros e Hns.
        specialize (Hsound3 (uglify' e)).
        ltac1:(ospecialize (Hsound3 _)).
        {
            unfold not_stuck in Hns.
            unfold not_stuck_flat.
            destruct Hns as [e' He'].
            exists (uglify' e').
            unfold rewriting_relation in He'.
            unfold rewriting_relation_flat.
            destruct He' as [r [a [HH1 HH2]]].
            exists (r_to_fr r).
            exists a.
            repeat split.
            {
                rewrite elem_of_list_fmap.
                exists r.
                split>[reflexivity|exact HH1].
            }
            {
                unfold flattened_rewrites_to.
                unfold rewrites_to in HH2.
                destruct HH2 as [ρ Hρ].
                exists (fmap uglify' ρ).
                unfold rewrites_in_valuation_under_to in Hρ.
                destruct Hρ as [[[HH1' HH2] HH3] HH4].
                repeat split.
                {
                    unfold satisfies in *|-; simpl in *|-.
                    apply sat2B_uglify in HH1'.
                    destruct r; simpl in *. apply HH1'.
                }
                {
                    unfold satisfies in *|-; simpl in *|-.
                    apply sat2E_uglify in HH2.
                    destruct r; simpl in *. apply HH2.
                }
                {
                    unfold satisfies in *|-; simpl in *|-.
                    intros x.
                    specialize (HH3 (sc_to_sc2 x)).
                    intros Hx.
                    ltac1:(ospecialize (HH3 _)).
                    {
                        destruct r; simpl in *.
                        rewrite elem_of_list_fmap in Hx.
                        destruct Hx as [y [H1y H2y]].
                        subst x.
                        rewrite (cancel sc_to_sc2 sc2_to_sc).
                        exact H2y.
                    }
                    unfold satisfies in HH3; simpl in HH3.
                    unfold satisfies; simpl.
                    destruct x; simpl in *.
                    destruct c; simpl in *.
                    unfold satisfies; simpl.
                    destruct HH3 as [HH31 HH32].
                    rewrite Expression2_Expression_evaluate in HH31.
                    rewrite Expression2_Expression_evaluate in HH31.
                    rewrite Expression2_Expression_evaluate in HH32.
                    unfold isSome in HH32.
                    destruct (prettify <$>
                        Expression_evaluate (uglify' <$> ρ)
                        (Expression2_to_Expression (Expression_to_Expression2 e1)))
                        eqn:Heq>[|inversion HH32].
                    apply (f_equal (fmap uglify')) in Heq.
                    apply (f_equal (fmap uglify')) in HH31.
                    clear HH32.
                    simpl in HH31.
                    rewrite fmap_uglify_prettify_option in Heq.
                    rewrite fmap_uglify_prettify_option in HH31.
                    rewrite (cancel Expression2_to_Expression Expression_to_Expression2) in HH31.
                    rewrite (cancel Expression2_to_Expression Expression_to_Expression2) in Heq.
                    rewrite Heq.
                    rewrite <- HH31.
                    simpl.
                    repeat split.
                }
                {
                    subst a.
                    destruct r; simpl in *. reflexivity.
                }
            }
        }
        destruct Hsound3 as [e' He'].
        exists (prettify e').
        unfold naive_interpreter.
        unfold flat_naive_interpreter in He'.
        rewrite bind_Some in He'.
        rewrite bind_Some.
        destruct He' as [[g n] [H1 H2]].
        simpl in *.
        inversion H2; subst; clear H2.
        exists (e',n).
        repeat split.
        apply H1.
    }
Qed.