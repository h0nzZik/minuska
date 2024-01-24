
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    syntax_properties
    semantics_properties
    flattened
    basic_matching
    try_match
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Logic.FunctionalExtensionality.

Definition evaluate_sc
    {Σ : StaticModel}
    (ρ : Valuation)
    (sc : SideCondition)
    : bool :=
match sc with
| sc_constraint c =>
    matchesb ρ () c
end.


Definition evaluate_rhs_pattern
    {Σ : StaticModel}
    (ρ : Valuation)
    (φ : AppliedOperatorOr' symbol Expression)
    : option GroundTerm :=
    let f : Expression -> option GroundTerm
        := (Expression_evaluate ρ) in
    let fφ  : AppliedOperatorOr' symbol (option GroundTerm)
        := f <$> φ in 
    let cfφ : option (AppliedOperatorOr' symbol GroundTerm)
        := AppliedOperatorOr'_collapse_option fφ in
    cfφ' ← cfφ;
    let flat := AppliedOperatorOr'_symbol_A_to_OpenTermB id cfφ' in
    Some flat
.

Definition rewrite_with
    {Σ : StaticModel}
    
    (r : FlattenedRewritingRule)
    (g : GroundTerm)
    : option GroundTerm
:=
    ρ ← try_match g (fr_from r);
    if (forallb (evaluate_sc ρ) (fr_scs r)) then
        evaluate_rhs_pattern ρ (fr_to r)
    else None
.

Lemma evaluate_rhs_pattern_correct
    {Σ : StaticModel}
    
    (φ : RhsPattern)
    (ρ : Valuation)
    (g : GroundTerm)
    :
    evaluate_rhs_pattern ρ φ = Some g <->
    matchesb ρ g φ = true
.
Proof.
    unfold evaluate_rhs_pattern.
    rewrite bind_Some.
    
    ltac1:(
        under [fun e => _]functional_extensionality => e
    ).
    {
        ltac1:(rewrite inj_iff).
        ltac1:(over).
    }
    destruct φ; cbn.
    {
        cbn.
        ltac1:(
            under [fun e => _]functional_extensionality => e
        ).
        {
            ltac1:(rewrite bind_Some).
            ltac1:(
                under [fun e' => _]functional_extensionality => e'
            ).
            {
                ltac1:(rewrite inj_iff).
                ltac1:(over).
            }
            ltac1:(over).
        }
        destruct g; cbn.
        {
            unfold matchesb; simpl.
            cbn.

            split; intros H.
            {
                destruct H as [e H].
                destruct H as [H1 H2].
                destruct H1 as [e' [H11 H12]].
                cbn in *.
                subst.
                cbn in *.
                inversion H2; subst; clear H2.
                cbn in *.
                inversion H11; subst; clear H11.
                revert e' H0.
                induction ao; intros e' H0.
                {
                    cbn in *.
                    inversion H0; subst; clear H0.
                    simpl. unfold matchesb; simpl.
                    apply bool_decide_eq_true.
                    reflexivity.
                }
                {
                    cbn in *.
                    rewrite bind_Some in H0.
                    destruct H0 as [x [H1 H2]].
                    rewrite bind_Some in H2.
                    destruct H2 as [x0 H2].
                    destruct H2 as [H2 H3].
                    inversion H3; subst; clear H3.
                    cbn.
                    destruct x0.
                    {
                        unfold matchesb; simpl.
                        rewrite andb_true_iff.
                        unfold matchesb in IHao; simpl in IHao.
                        rewrite IHao.
                        {
                            split>[reflexivity|].
                            unfold matchesb; simpl.
                            apply bool_decide_eq_true.
                            assumption.
                        }
                        {
                            assumption.
                        }
                    }
                    {
                        unfold matchesb; simpl.
                        rewrite andb_true_iff.
                        unfold matchesb in IHao; simpl in IHao.
                        split.
                        {
                            apply IHao.
                            exact H1.
                        }
                        {
                            unfold matchesb; simpl.
                            apply bool_decide_eq_true.
                            assumption.
                        }
                    }
                }
                {
                    cbn in *.
                    rewrite bind_Some in H0.
                    destruct H0 as [x [H1 H2]].
                    rewrite bind_Some in H2.
                    destruct H2 as [x0 H2].
                    destruct H2 as [H2 H3].
                    inversion H3; subst; clear H3.
                    specialize (IHao1 _ H1).
                    specialize (IHao2 _ H2).
                    cbn.
                    unfold matchesb; simpl.
                    rewrite andb_true_iff.
                    split; assumption.
                }
            }
            {
                
                remember (fun (v:builtin_value) (e':Expression) =>
                    match Expression_evaluate ρ e' with
                    | Some v' => v'
                    | None => aoo_operand v
                    end
                ) as zipper.
                remember (fun (s1 s2 : symbol) => s1) as symleft.
                remember (fun (g : AppliedOperator' symbol builtin_value) (e' : Expression) =>
                    (aoo_app g)
                ) as f1.
                remember (fun (b : builtin_value) (et : AppliedOperator' symbol Expression) =>
                    (@aoo_operand symbol _ b)
                ) as f2.
                remember (AppliedOperator'_zipWith symleft zipper f1 f2 ao0 ao) as zipped.
                exists (aoo_app zipped).
                cbn.
                split.
                {
                    exists zipped.
                    subst.
                    repeat constructor.
                    clear -H.
                    apply matchesb_implies_satisfies in H.

                    induction H.
                    {
                        simpl.
                        cbn.
                        reflexivity.
                    }
                    {
                        cbn in H0.
                        cbn.
                        rewrite bind_Some.
                        cbn.
                        ltac1:(
                            under [fun e => _]functional_extensionality => e
                        ).
                        {
                            ltac1:(rewrite bind_Some).
                            ltac1:(
                                under [fun e' => _]functional_extensionality => e'
                            ).
                            {
                                ltac1:(rewrite inj_iff).
                                ltac1:(over).
                            }
                            ltac1:(over).
                        }
                        cbn in *.
                        eexists.
                        split>[apply IHaoxy_satisfies_aoxz|].
                        eexists.
                        split>[apply H0|].
                        apply f_equal.
                        rewrite H0.
                        reflexivity.
                    }
                    {
                        cbn in H0.
                        cbn.
                        rewrite bind_Some.
                        cbn in *.
                        ltac1:(
                            under [fun e => _]functional_extensionality => e
                        ).
                        {
                            ltac1:(rewrite bind_Some).
                            ltac1:(
                                under [fun e' => _]functional_extensionality => e'
                            ).
                            {
                                ltac1:(rewrite inj_iff).
                                ltac1:(over).
                            }
                            ltac1:(over).
                        }
                        cbn in *.
                        eexists.
                        split>[apply IHaoxy_satisfies_aoxz|].
                        eexists.
                        split>[apply H0|].
                        reflexivity.
                    }
                    {
                        unfold satisfies in H0; simpl in H0.
                        inversion H0.
                    }
                    {
                        cbn in H0.
                        cbn.
                        rewrite bind_Some.
                        cbn in *.
                        ltac1:(
                            under [fun e => _]functional_extensionality => e
                        ).
                        {
                            ltac1:(rewrite bind_Some).
                            ltac1:(
                                under [fun e' => _]functional_extensionality => e'
                            ).
                            {
                                ltac1:(rewrite inj_iff).
                                ltac1:(over).
                            }
                            ltac1:(over).
                        }
                        cbn in *.
                        eexists.
                        split>[apply IHaoxy_satisfies_aoxz1|].
                        eexists.
                        split>[apply IHaoxy_satisfies_aoxz2|].
                        reflexivity.
                    }
                }
                {
                    subst. cbn.
                    apply f_equal.
                    apply matchesb_implies_satisfies in H.
                    induction H.
                    {
                        cbn. reflexivity.
                    }
                    {
                        cbn in *.
                        rewrite H0.
                        rewrite IHaoxy_satisfies_aoxz.
                        reflexivity.
                    }
                    {
                        cbn in *.
                        rewrite IHaoxy_satisfies_aoxz.
                        reflexivity.
                    }
                    {
                        unfold satisfies in H0; simpl in H0.
                        inversion H0.
                    }
                    {
                        cbn in *.
                        rewrite IHaoxy_satisfies_aoxz1.
                        rewrite IHaoxy_satisfies_aoxz2.
                        reflexivity.
                    }
                }
            }
        }
        {
            cbn.
            split; intros H.
            {
                destruct H as [e H].
                destruct H as [H1 H2].
                destruct H1 as [e' [H11 H12]].
                subst. cbn in *.
                inversion H2.
            }
            {
                inversion H.
            }
        }
    }
    {
        ltac1:(
            under [fun e => _]functional_extensionality => e
        ).
        {
            ltac1:(rewrite bind_Some).
            ltac1:(
                under [fun e' => _]functional_extensionality => e'
            ).
            {
                ltac1:(rewrite inj_iff).
                ltac1:(over).
            }
            ltac1:(over).
        }
        cbn.
        destruct g; cbn.
        {
            split; intros H.
            {
                destruct H as [e H].
                destruct H as [[e' [H'1 H'2]] H].
                subst.
                cbn in H.
                subst.
                unfold matchesb; simpl.
                unfold matchesb; simpl.
                apply bool_decide_eq_true.
                assumption.
            }
            {
                eexists.
                split.
                {
                    unfold matchesb in H; simpl in H.
                    unfold matchesb in H; simpl in H.
                    apply bool_decide_eq_true in H.
                    eexists. split>[|reflexivity].
                    apply H.
                }
                {
                    cbn. reflexivity.
                }
            }
        }
        {
            split; intros H.
            {
                destruct H as [e H].
                destruct H as [[e' [H'1 H'2]] H].
                subst.
                cbn in H.
                subst.
                do 2 (unfold matchesb; simpl).
                apply bool_decide_eq_true.
                assumption.
            }
            {
                eexists.
                split.
                {
                    do 2 (unfold matchesb in H; simpl in H).
                    apply bool_decide_eq_true in H.
                    eexists. split>[|reflexivity].
                    apply H.
                }
                {
                    cbn. reflexivity.
                }
            }
        }
    }
Qed.

Definition try_match_lhs_with_sc
    {Σ : StaticModel}
    
    (g : GroundTerm)
    (r : FlattenedRewritingRule)
    : option Valuation
:=
    ρ ← try_match g (fr_from r);
    let validates := matchesb ρ () (fr_scs r) in
    if validates then Some ρ else None
.

(*
#[global]
Instance VarsOf_list_SideCondition
    {Σ : StaticModel}
    :
    VarsOf (list SideCondition) variable
:= {|
    vars_of := fun scs => union_list (vars_of <$> scs) ;
|}.
*)

Lemma try_match_lhs_with_sc_complete
    {Σ : StaticModel}
    
    (g : GroundTerm)
    (r : FlattenedRewritingRule)
    (ρ : gmap variable GroundTerm)
    :
    vars_of (fr_scs r) ⊆ vars_of (fr_from r) ->
    matchesb ρ g (fr_from r) = true ->
    matchesb ρ () (fr_scs r) = true ->
    ∃ ρ' : (gmap variable GroundTerm),
        vars_of ρ' = vars_of (fr_from r) ∧
        ρ' ⊆ ρ ∧
        try_match_lhs_with_sc g r = Some ρ'
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
    (*
    assert (H10 := H1).
    assert (H20 := H2).*)
    apply try_match_complete in H1.
    destruct H1 as [ρ1 [H1ρ1 H2ρ1]].
    destruct H2ρ1 as [H2ρ1 H3ρ2].
    (*destruct (matchesb ρ1 () (fr_scs r)) eqn:Hm.*)
    {
        
        unfold try_match_lhs_with_sc.
        ltac1:(setoid_rewrite bind_Some).
        exists ρ1.
        split.
        {
            unfold Valuation in *.
            rewrite H1ρ1.
            reflexivity.
        }
        split.
        {
            assumption.
        }
        exists ρ1.
        split>[apply H3ρ2|].
        unfold matchesb in *; simpl in *.
        ltac1:(case_match).
        { reflexivity. }
        rewrite forallb_forall in H2.
        assert (HH : ~ (forallb [eta matchesb ρ1 ()] (fr_scs r) = true)).
        {
            intros HContra.
            unfold matchesb in *; simpl in *.
            rewrite HContra in H. inversion H.
        }
        clear H.
        rewrite forallb_forall in HH.
        ltac1:(exfalso).
        apply HH. clear HH.
        intros x Hx.
        specialize (H2 x Hx).
        erewrite matchesb_insensitive in H2. apply H2.
        unfold valuation_restrict.
        rewrite map_eq_iff.
        intros i.
        do 2 (rewrite map_lookup_filter).
        unfold Valuation in *.
        
        destruct (ρ!!i) eqn:Hρi, (ρ1!!i) eqn:Hρ1i; simpl in *.
        {
            unfold mguard,option_guard; simpl.
            ltac1:(case_match).
            {
                ltac1:(rewrite map_subseteq_spec in H2ρ1).
                specialize (H2ρ1 i).
                specialize (H2ρ1 g1 Hρ1i).
                ltac1:(simplify_eq/=).
                reflexivity.
            }
            {
                reflexivity.
            }
        }
        {
            unfold mguard,option_guard; simpl.
            ltac1:(case_match)>[|reflexivity].
            ltac1:(exfalso).
            clear H.
            ltac1:(cut(i ∈ vars_of ρ1)).
            {
                intros HHH. unfold vars_of in HHH; simpl in HHH.
                rewrite elem_of_dom in HHH.
                destruct HHH as [s Hs].
                rewrite Hs in Hρ1i.
                inversion Hρ1i.
            }
            clear H2ρ1.
            rewrite H1ρ1.
            clear H1ρ1.
            eapply elem_of_weaken>[|apply Hn].
            clear Hn.
            rewrite <- elem_of_list_In in Hx.
            unfold vars_of; simpl.
            rewrite elem_of_union_list.
            exists (vars_of x).
            split>[|assumption].
            rewrite elem_of_list_fmap.
            exists x.
            split>[reflexivity|].
            exact Hx.
        }
        {
            ltac1:(exfalso).
            eapply lookup_weaken in Hρ1i>[|apply H2ρ1].
            rewrite Hρi in Hρ1i.
            inversion Hρ1i.
        }
        {
            reflexivity.
        }
    }
Qed.

Lemma valuation_restrict_vars_of_self
    {Σ : StaticModel}
    (ρ' ρ : gmap variable GroundTerm)
    :
    ρ' ⊆ ρ  ->
    valuation_restrict ρ' (vars_of ρ') = valuation_restrict ρ (vars_of ρ')
.
Proof.
    intros H.
    rewrite map_eq_iff.
    unfold valuation_restrict.
    intros i.
    rewrite map_lookup_filter.
    rewrite map_lookup_filter.
    destruct (ρ' !! i) eqn:Hρ'i.
    {
        simpl.
        unfold mguard,option_guard; simpl.
        assert (Hρi: ρ !! i = Some g).
        {
            eapply lookup_weaken>[|apply H].
            assumption.
        }
        rewrite Hρi.
        simpl.
        reflexivity.
    }
    {
        simpl.
        destruct (ρ!!i) eqn:Hρi; simpl.
        {
            unfold mguard, option_guard.
            ltac1:(case_match)>[|reflexivity].
            unfold vars_of in e. clear H0.
            simpl in e.
            rewrite elem_of_dom in e.
            destruct e as [g' Hg'].
            rewrite Hρ'i in Hg'.
            inversion Hg'.
        }
        {
            reflexivity.
        }
    }
Qed.

Definition thy_lhs_match_one
    {Σ : StaticModel}
    
    (e : GroundTerm)
    (Γ : list FlattenedRewritingRule)
    : option (FlattenedRewritingRule * Valuation * nat)%type
:=
    let froms : list OpenTerm
        := fr_from <$> Γ
    in
    let vs : list (option Valuation)
        := (try_match_lhs_with_sc e) <$> Γ
    in
    let found : option (nat * option Valuation)
        := list_find is_Some vs
    in
    nov ← found;
    let idx : nat := nov.1 in
    let ov : option Valuation := nov.2 in
    v ← ov;
    r ← Γ !! idx;
    Some (r, v, idx)
.

Lemma thy_lhs_match_one_None
    {Σ : StaticModel}
    
    (e : GroundTerm)
    (Γ : FlattenedRewritingTheory)
    (wfΓ : FlattenedRewritingTheory_wf Γ)
    :
    thy_lhs_match_one e Γ = None ->
    ~ exists (r : FlattenedRewritingRule) (ρ : Valuation),
        r ∈ Γ /\ satisfies ρ e (fr_from r) /\ satisfies ρ () (fr_scs r)
.
Proof.
    unfold thy_lhs_match_one.
    intros H [r [ρ [Hin HContra]]].
    destruct (list_find is_Some (try_match_lhs_with_sc e <$> Γ)) eqn:Heqfound.
    {
        destruct p as [n oρ].
        rewrite list_find_Some in Heqfound.
        rewrite bind_None in H.
        ltac1:(destruct H as [H|H];[inversion H|]).
        destruct H as [[idx ρ2][H1 H2]].
        simpl in H2.
        inversion H1; subst; clear H1.
        ltac1:(destruct Heqfound as [Hfound [HSome HFirst]]).
        rewrite bind_None in H2.
        destruct HSome as [ρ2' HSome].
        subst.
        (destruct H2 as [H2|H2])>[inversion H2|].
        destruct H2 as [ρ3 [H2 H3]].
        inversion H2; subst; clear H2.
        rewrite bind_None in H3.
        destruct H3 as [H3|H3].
        {
            unfold try_match_lhs_with_sc in Hfound.
            rewrite list_lookup_fmap in Hfound.
            rewrite fmap_Some in Hfound.
            destruct Hfound as [r' [H1r' H2r']].
            rewrite H3 in H1r'. inversion H1r'.
        }
        {
            destruct H3 as [r' [H1r' H2r']].
            inversion H2r'.
        }
    }
    {
        clear H.
        rewrite list_find_None in Heqfound.
        rewrite Forall_forall in Heqfound.
        destruct HContra as [Hsat1 Hsat2].
        ltac1:(unshelve(eapply satisfies_implies_matchesb in Hsat1)).
        {
            unfold GroundTerm, OpenTerm.
            apply _.
        }
        {
            apply _.
        }
        ltac1:(unshelve(eapply satisfies_implies_matchesb in Hsat2)).
        {
            unfold GroundTerm, OpenTerm.
            apply _.
        }
        {
            apply _.
        }
        apply try_match_complete in Hsat1.
        destruct Hsat1 as [ρ' [H1 [H2 H3]]].

        assert (Hc := try_match_lhs_with_sc_complete e r).
        specialize (Hc ρ').
        ltac1:(ospecialize (Hc _)).
        {
            unfold FlattenedRewritingTheory_wf in wfΓ.
            unfold is_true in wfΓ.
            rewrite Forall_forall in wfΓ.
            specialize (wfΓ r).
            unfold FlattenedRewritingRule_wf in wfΓ.
            specialize (wfΓ Hin).
            apply wfΓ.
        }
        assert (H3' := H3).
        apply try_match_correct in H3'.
        specialize (Hc H3').
        ltac1:(ospecialize (Hc _)).
        {
            erewrite matchesb_insensitive.
            apply Hsat2.
            unfold FlattenedRewritingTheory_wf in wfΓ.
            unfold is_true in wfΓ.
            rewrite Forall_forall in wfΓ.
            specialize (wfΓ r).
            unfold FlattenedRewritingRule_wf in wfΓ.
            specialize (wfΓ Hin).
            eapply valuation_restrict_eq_subseteq.
            { apply wfΓ. }
            rewrite <- H1.
            clear -H2.
            apply valuation_restrict_vars_of_self.
            assumption.
        }
        destruct Hc as [ρ'' [H1ρ'' [H2ρ'' H3ρ'']]].

        specialize (Heqfound (Some ρ'')).
        ltac1:(ospecialize (Heqfound _)).
        {
            clear Heqfound.
            
            unfold Valuation in *.
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
        unfold is_Some.
        exists ρ''.
        reflexivity.
    }
Qed.


Lemma thy_lhs_match_one_Some
    {Σ : StaticModel}
    
    (e : GroundTerm)
    (Γ : list FlattenedRewritingRule)
    (r : FlattenedRewritingRule)
    (ρ : Valuation)
    (rule_idx : nat)
    :
    thy_lhs_match_one e Γ = Some (r, ρ, rule_idx) ->
    r ∈ Γ /\ satisfies ρ e (fr_from r) /\ satisfies ρ () (fr_scs r)
.
Proof.
    intros H.
    unfold thy_lhs_match_one in H.
    unfold is_Some in H.
    (repeat ltac1:(case_match)); subst.
    {
        rewrite bind_Some in H.
        destruct H as [[idx oρ][H1 H2]].
        simpl in *.
        rewrite list_find_Some in H1.
        destruct H1 as [H11 H12].
        rewrite list_lookup_fmap in H11.
        rewrite fmap_Some in H11.
        destruct H11 as [ot [Hot1 Hot2]].
        subst.
        rewrite bind_Some in H2.
        destruct H2 as [ρ' [H1ρ' H2ρ']].
        rewrite bind_Some in H2ρ'.
        destruct H2ρ' as [r' [H1r' H2r']].
        inversion H2r'; subst; clear H2r'.
        rewrite Hot1 in H1r'.
        inversion H1r'; subst; clear H1r'.
        split.
        {
            rewrite elem_of_list_lookup.
            exists rule_idx. apply Hot1.
        }
        {
            destruct H12 as [H1 H2].
            destruct H1 as [x Hx].
            rewrite Hx in H1ρ'.
            inversion H1ρ'; subst; clear H1ρ'.
            unfold try_match_lhs_with_sc in Hx.
            rewrite bind_Some in Hx.
            destruct Hx as [x [H1x H2x]].
            destruct (matchesb x () (fr_scs r)) eqn:Heq.
            {
                inversion H2x; subst; clear H2x.
                apply try_match_correct in H1x.
                apply matchesb_implies_satisfies in Heq.
                apply matchesb_implies_satisfies in H1x.
                split; assumption.
            }
            {
                inversion H2x.
            }
        }
    }
Qed.


Definition naive_interpreter_ext
    {Σ : StaticModel}
    
    (Γ : list FlattenedRewritingRule)
    (e : GroundTerm)
    : option (GroundTerm*nat)
:=
    let oρ : option (FlattenedRewritingRule*Valuation*nat)
        := thy_lhs_match_one e Γ in
    match oρ with
    | None => None
    | Some (r,ρ,idx) =>
        e' ← (evaluate_rhs_pattern ρ (fr_to r));
        Some (e',idx)
    end
.

Definition naive_interpreter
    {Σ : StaticModel}
    
    (Γ : list FlattenedRewritingRule)
    (e : GroundTerm)
    : option (GroundTerm)
:=
    ei ← naive_interpreter_ext Γ e;
    Some ei.1
.


Lemma naive_interpreter_sound
    {Σ : StaticModel}
    
    (Γ : FlattenedRewritingTheory)
    (wfΓ : FlattenedRewritingTheory_wf Γ)
    : FlatInterpreter_sound Γ wfΓ (naive_interpreter Γ).
Proof.
    unfold naive_interpreter.
    unfold FlatInterpreter_sound.
    unfold flat_stuck,not_stuck_flat.
    unfold naive_interpreter_ext.
    split.
    {
        intros e Hstuck.
        destruct (thy_lhs_match_one e Γ) eqn:Hmatch>[|reflexivity].
        {
            destruct p as [[r ρ] rule_idx].
            {
                apply thy_lhs_match_one_Some in Hmatch.
                destruct Hmatch as [Hin Hsat].
                assert (Hts := thy_lhs_match_one_Some).
                unfold rewriting_relation_flat in Hstuck.
                unfold flattened_rewrites_to in Hstuck.
                unfold flattened_rewrites_in_valuation_to in Hstuck.
                assert (Hev := evaluate_rhs_pattern_correct (fr_to r) ρ).
                ltac1:(cut (~ ∃ g', evaluate_rhs_pattern ρ (fr_to r) = Some g')).
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
                rewrite Hev in Hg'.
                clear Hev.
                apply matchesb_implies_satisfies in Hg'.
                apply Hstuck. clear Hstuck.
                exists pg'. exists r.
                split>[assumption|].
                exists ρ.
                split>[apply Hsat|].
                split>[assumption|].
                apply Hsat.
            }
        }
    }
    {
        intros e Hnotstuck.
        unfold naive_interpreter.

        destruct Hnotstuck as [e' He'].
        unfold rewriting_relation_flat in He'.
        destruct He' as [r' [H1r' H2r']].
        unfold flattened_rewrites_to in H2r'.
        destruct H2r' as [ρ' Hρ'].
        unfold flattened_rewrites_in_valuation_to in Hρ'.

        
        destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
        {
            destruct p as [[r ρ] rule_idx]; cbn in *.
            apply thy_lhs_match_one_Some in Hmatch.
            destruct Hmatch as [Hin Hsat].
            
            
            destruct (evaluate_rhs_pattern ρ (fr_to r)) eqn:Heval.
            {
                eexists. reflexivity.
            }
            {
                ltac1:(exfalso).
                unfold FlattenedRewritingTheory_wf in wfΓ.
                unfold FlattenedRewritingRule_wf in wfΓ.
                rewrite Forall_forall in wfΓ.
                specialize (wfΓ r).
                specialize (wfΓ ltac:(assumption)).
                destruct wfΓ as [wf1 wf2].
                unfold FlattenedRewritingRule_wf2 in wf2.
                specialize (wf2 e ρ).
                destruct Hsat as [Hsat1 Hsat2].
                specialize (wf2 Hsat1 Hsat2).
                destruct wf2 as [g' Hg'].
                ltac1:(unshelve(eapply satisfies_implies_matchesb in Hg')).
                {
                    apply _.
                }
                {
                    apply _.
                }

                assert (Hn : ~ exists g, evaluate_rhs_pattern ρ (fr_to r) = Some g).
                {
                    intros HContra.
                    destruct HContra as [g HContra].
                    rewrite Heval in HContra.
                    inversion HContra.
                }
                ltac1:(setoid_rewrite evaluate_rhs_pattern_correct in Hn).
                apply Hn. clear Hn. clear Heval.
                exists g'.
                apply Hg'.
            }
        }
        {
            ltac1:(exfalso).
            apply thy_lhs_match_one_None in Hmatch.
            { ltac1:(naive_solver). }
            { assumption. }
        }
    }
Qed.

