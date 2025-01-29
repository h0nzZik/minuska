
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

Definition try_match_lhs_with_sc
    {Σ : StaticModel}
    {Act : Set}
    (program : ProgramT)
    (g : TermOver builtin_value)
    (nv : NondetValue)
    (r : RewritingRule2 Act)
    : option Valuation2
:=
    ρ ← try_match_new g (r_from r);
    if SideCondition_evaluate program ρ nv (r_scs r)
    then (Some ρ)
    else None
.

Definition thy_lhs_match_one
    {Σ : StaticModel}
    {Act : Set}
    (e : TermOver builtin_value)
    (nv : NondetValue)
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    : option (RewritingRule2 Act * Valuation2 * nat)%type
:=
    let froms : list (TermOver BuiltinOrVar)
        := r_from <$> Γ
    in
    let vs : list (option Valuation2)
        := (try_match_lhs_with_sc program e nv) <$> Γ
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
    (program : ProgramT)
    (ρ : Valuation2)
    (nv : NondetValue)
    (et : TermOver Expression2)
    : option (TermOver builtin_value)
:=
    let tmp1 := (TermOver_map (fun x => let y := Expression2_evaluate program ρ x in ((fun f => f nv)<$> y)) et) in
    let tmp2 := (TermOver_collect tmp1) in
    TermOver_join <$> tmp2
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
    let oρ : option ((RewritingRule2 Act)*Valuation2*nat)
        := thy_lhs_match_one e nv Γ program in
    match oρ with
    | None => None
    | Some (r,ρ,idx) =>
        e' ← (eval_et program ρ nv (r_to r));
        Some (e',idx)
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
            satisfies v1 (program, nv) b -> satisfies v2 (program, nv) b
.
Proof.
    intros.
    unfold satisfies in *; simpl in *.
    unfold Valuation2_restrict in H.
    eapply SideCondition_satisfies_strip in X.
    rewrite H in X.
    eapply SideCondition_satisfies_extensive>[|apply X].
    unfold Valuation2 in *.
    apply map_filter_subseteq.
Qed.


Lemma try_match_lhs_with_sc_complete
    {Σ : StaticModel}
    {Act : Set}
    (program : ProgramT)
    (g : TermOver builtin_value)
    (r : RewritingRule2 Act)
    (ρ : Valuation2)
    (nv : NondetValue)
    :
    vars_of (r_scs r) ⊆ vars_of (r_from r) ->
    satisfies ρ g (r_from r) ->
    satisfies ρ (program, nv) (r_scs r) ->
    {
        ρ' : (gmap variable (TermOver builtin_value)) &
        vars_of ρ' = vars_of (r_from r) ∧
        ρ' ⊆ ρ ∧
        try_match_lhs_with_sc program g nv r = Some ρ'
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
        simpl in *.
        ltac1:(case_match).
        { reflexivity. }
        unfold satisfies in H2; simpl in H2.
        rewrite <- not_true_iff_false in H.
        ltac1:(exfalso).
        apply H. clear H.
        eapply sc_satisfies_insensitive>[|apply H2].
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
            destruct (ρ !! i) as [y|] eqn:Hρi, (ρ1 !! i) as [z|] eqn:Hρ1i;
                ltac1:(simplify_option_eq);
                reflexivity.
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
    (program : ProgramT)
    (e : TermOver builtin_value)
    (Γ : RewritingTheory2 Act)
    (wfΓ : RewritingTheory2_wf Γ)
    (nv : NondetValue)
    :
    thy_lhs_match_one e nv Γ program = None ->
    notT { r : RewritingRule2 Act & { ρ : Valuation2 &
        ((r ∈ Γ) * (satisfies ρ e (r_from r)) * (satisfies ρ (program, nv) (r_scs r)))%type
    } }
        
.
Proof.
    unfold thy_lhs_match_one.
    intros H [r [ρ [[Hin HContra1] HContra2]]].
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
        clear H.
        rewrite list_find_None in Heqfound.
        rewrite Forall_forall in Heqfound.
        ltac1:(rename HContra1 into Hsat1).
        ltac1:(rename HContra2 into Hsat2).
        apply try_match_new_complete in Hsat1.
        destruct Hsat1 as [ρ' [H1 [H2 H3]]].

        assert (Hc := try_match_lhs_with_sc_complete program e r).
        specialize (Hc ρ').
        ltac1:(ospecialize (Hc nv _)).
        {
            unfold is_true in wfΓ.
            specialize (wfΓ r).
            specialize (wfΓ Hin).
            apply wfΓ.
        }
        assert (H3' := H3).
        apply try_match_new_correct in H3'.
        specialize (Hc H3').
        ltac1:(ospecialize (Hc _)).
        {
            unfold satisfies; simpl.
            eapply sc_satisfies_insensitive in Hsat2 as Hsat2'. apply Hsat2'.
            assert (Htmp := valuation_restrict_vars_of_self ρ' ρ H2).
            eapply Valuation2_restrict_eq_subseteq in Htmp.
            symmetry. apply Htmp.
            rewrite H1.   
            unfold is_true in wfΓ.
            specialize (wfΓ r).
            specialize (wfΓ Hin).
            unfold RewritingRule2_wf in *.
            destruct wfΓ as [wf1 wf2].
            unfold RewritingRule2_wf1 in *.
            unfold RewritingRule2_wf2 in *.
            eapply transitivity>[|apply wf1].
            unfold vars_of; simpl.
            ltac1:(set_solver).
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
(* 
Lemma evaluate_scs_correct
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (nv : NondetValue)
    (scs : list SideCondition)
    :
    evaluate_scs program ρ nv scs = true ->
    satisfies ρ (program, nv) scs
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
    
    unfold satisfies; simpl.
    ltac1:(repeat case_match).
    {
        assumption.
    }
Qed. *)

Lemma thy_lhs_match_one_Some
    {Σ : StaticModel}
    {Act : Set}
    (e : TermOver builtin_value)
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    (r : RewritingRule2 Act)
    (ρ : Valuation2)
    (nv : NondetValue)
    (rule_idx : nat)
    :
    thy_lhs_match_one e nv Γ program = Some (r, ρ, rule_idx) ->
    ((r ∈ Γ) * (satisfies ρ e (r_from r)) * (satisfies ρ (program, nv) (r_scs r)))%type
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
                destruct (try_match_lhs_with_sc program e nv r) eqn:HTM>[|inversion H1].
                clear H1.
                inversion H1ρ'; subst; clear H1ρ'.
                unfold try_match_lhs_with_sc in HTM.
                apply bind_Some_T_1 in HTM.
                destruct HTM as [x [H1x H2x]].
                apply try_match_new_correct in H1x.
                destruct (SideCondition_evaluate program x nv (r_scs r)) eqn:Heq.
                {
                    inversion H2x; subst; clear H2x.
                    apply H1x.
                }
                {
                    inversion H2x.
                }         
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
                inversion H2x; subst; clear H2x.
                exact Heq.
            }
            {
                inversion H2x.
            }
        }
    }
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
            reflexivity.
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
            rewrite length_fmap.
            ltac1:(rename H1 into l1).
            split.
            {
                apply length_list_collect_Some in Heqo0.
                rewrite length_fmap in Heqo0.
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
        rewrite HH. reflexivity.
    }
    {
        unfold satisfies in HH. simpl in HH.
        ltac1:(simp sat2E in HH).
        unfold eval_et. simpl. 
        destruct (Expression2_evaluate program ρ a) eqn:Heq>[|ltac1:(contradiction)].
        simpl. rewrite HH. reflexivity.
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
        intros program e1 e2 nv.
        intros Hbind.
        apply bind_Some_T_1 in Hbind.
        destruct Hbind as [x [H1x H2x]].
        destruct (thy_lhs_match_one e1 nv Γ) eqn:Hmatch.
        {
            destruct p as [[r ρ] idx].
            apply thy_lhs_match_one_Some in Hmatch.
            inversion H2x; subst; clear H2x.
            apply bind_Some_T_1 in H1x.
            destruct H1x as [y [H1y H2y]].
            inversion H2y; subst; clear H2y.
            simpl.
            exists r.
            destruct Hmatch as [[Hin Hm1] Hm2].
            exists (r_act r).
            split>[apply Hin|].
            unfold rewrites_to.
            exists ρ.
            unfold rewrites_in_valuation_under_to.
            apply eval_et_correct in H1y.
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
            destruct p as [[r ρ] rule_idx].
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
                exists pg'. exists nv. exists r.
                exists (r_act r).
                destruct Hin.
                split>[assumption|].
                exists ρ.
                repeat split; try assumption.
            }
        }
    }
    {
        intros program e Hnotstuck.
        unfold naive_interpreter.

        destruct Hnotstuck as [e' He'].
        destruct He' as [nv [r' [a [H1r' H2r']]]].
        unfold rewrites_to in H2r'.
        destruct H2r' as [ρ' Hρ'].
        unfold rewrites_in_valuation_under_to in Hρ'.

        
        destruct (thy_lhs_match_one e nv Γ program) eqn:Hmatch.
        {
            destruct p as [[r ρ] rule_idx]; cbn in *.
            apply thy_lhs_match_one_Some in Hmatch as Hmatch'.
            destruct Hmatch' as [Hin Hsat].
            
            
            destruct (eval_et program ρ nv (r_to r)) eqn:Heval.
            {
                eexists. exists nv. rewrite Hmatch. simpl.
                rewrite Heval. simpl.
                reflexivity.
            }
            {
                ltac1:(exfalso).
                specialize (wfΓ r).
                destruct Hin.
                specialize (wfΓ ltac:(assumption)).
                destruct wfΓ as [wf1 wf2].
                specialize (wf2 e ρ).
                specialize (wf2 program nv ltac:(assumption) ltac:(assumption)).
                destruct wf2 as [g' Hg'].
                assert (Hn : notT { g : _ & eval_et program ρ nv (r_to r) = Some g } ).
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
            {
                exists r'. exists ρ'.
                (repeat split); try assumption.
            }
            assumption.
        }
    }
Qed.
