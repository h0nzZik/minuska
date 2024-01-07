
From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    semantics_properties
    flattened
    (*flatten*)
    basic_matching
    try_match
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.




(*
Definition GroundTerm_try_match_OpenTerm
    {Σ : Signature}
    :
    GroundTerm -> OpenTerm -> option Valuation :=
    ApppliedOperatorOr'_try_match_AppliedOperatorOr'
        builtin_value
        BuiltinOrVar
.
*)
    
Definition evaluate_match
    {Σ : Signature}
    (ρ : Valuation)
    (m : Match)
    : bool :=
match m with
| mkMatch _ x φ =>
    match ρ !! x with
    | None => false
    | Some g => matchesb ρ g φ
    end
end.

Definition evaluate_sc
    `{CΣ : ComputableSignature}
    (ρ : Valuation)
    (sc : SideCondition)
    : bool :=
match sc with
| sc_constraint c =>
    matchesb ρ () c
| sc_match m =>
    evaluate_match ρ m
end.


Definition evaluate_rhs_pattern
    {Σ : Signature}
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
    {Σ : Signature}
    {CΣ : ComputableSignature}
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
    {Σ : Signature}
    {CΣ : ComputableSignature}
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
                    | None => aoo_operand _ _ v
                    end
                ) as zipper.
                remember (fun (s1 s2 : symbol) => s1) as symleft.
                remember (fun (g : AppliedOperator' symbol builtin_value) (e' : Expression) =>
                    (aoo_app symbol _ g)
                ) as f1.
                remember (fun (b : builtin_value) (et : AppliedOperator' symbol Expression) =>
                    (aoo_operand symbol _ b)
                ) as f2.
                remember (AppliedOperator'_zipWith symleft zipper f1 f2 ao0 ao) as zipped.
                exists (aoo_app _ _ zipped).
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
Print FlattenedRewritingRule.

Definition try_match_lhs_with_sc
    {Σ : Signature}
    {CΣ : ComputableSignature}
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
    {Σ : Signature}
    :
    VarsOf (list SideCondition) variable
:= {|
    vars_of := fun scs => union_list (vars_of <$> scs) ;
|}.
*)

Lemma try_match_lhs_with_sc_complete
    {Σ : Signature}
    {CΣ : ComputableSignature}
    (g : GroundTerm)
    (r : FlattenedRewritingRule)
    (ρ : gmap variable GroundTerm)
    :
    try_match_lhs_with_sc g r = Some ρ ->
    ∃ ρ' : (gmap variable GroundTerm),
        vars_of ρ' = vars_of (fr_from r) ∪ vars_of (fr_scs r) ∧
        ρ' ⊆ ρ ∧
        try_match_lhs_with_sc g r = Some ρ'
.
Proof.
    intros H.
    unfold try_match_lhs_with_sc in H.
    rewrite bind_Some in H.
    destruct H as [ρ1 [H1ρ1 H2ρ1]].
    destruct (matchesb ρ1 () (fr_scs r)) eqn:Hm>[|inversion H2ρ1].
    inversion H2ρ1; subst; clear H2ρ1.
    unfold try_match_lhs_with_sc.
    ltac1:(setoid_rewrite bind_Some).
    ltac1:(setoid_rewrite H1ρ1).
    exists ρ.
    split.
    {
        assert (H1 : vars_of ρ ⊆ vars_of (fr_from r) ∪ vars_of (fr_scs r)).
        {
            unfold vars_of; simpl.

            apply try_match_correct in H1ρ1.
            Search vars_of.
            unfold matchesb in H1ρ1; simpl in H1ρ1.
        }
        assert (H2 : vars_of (fr_from r) ∪ vars_of (fr_scs r) ⊆ vars_of ρ).
        {
            clear H1.
            unfold vars_of; simpl.
            apply try_match_correct in H1ρ1.
            apply matchesb_vars_of in Hm.
            apply matchesb_vars_of in H1ρ1.
            unfold vars_of in *; simpl in *.
            ltac1:(set_solver).
        }
        clear -H1 H2. ltac1:(set_solver).
        

        Search eq subseteq.
        Search valuation_satisfies_sc_bool.
        apply try_match_correct in H1ρ1.
    }
Qed.

Definition thy_lhs_match_one
    {Σ : Signature}
    {CΣ : ComputableSignature}
    (e : GroundTerm)
    (Γ : list FlattenedRewritingRule)
    : option (FlattenedRewritingRule * Valuation)%type
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
    Some (r, v)
.

Lemma thy_lhs_match_one_None
    {Σ : Signature}
    {CΣ : ComputableSignature}
    (e : GroundTerm)
    (Γ : list FlattenedRewritingRule)
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
        ltac1:(unshelve(eapply satisfies_implies_matchesb in Hsat2)).
        {
            unfold GroundTerm, OpenTerm.
            apply _.
        }
        apply try_match_complete in Hsat1.
        destruct Hsat1 as [ρ' [H1 [H2 H3]]].

        specialize (Heqfound (Some ρ')).
        ltac1:(ospecialize (Heqfound _)).
        {
            rewrite <- elem_of_list_In.
            unfold Valuation in *.
            rewrite elem_of_list_fmap.
            exists (r).
            split.
            {
                symmetry.
                unfold try_match_lhs_with_sc.
                rewrite bind_Some.
                exists ρ'.
                rewrite H3.
                split>[reflexivity|].
                clear -H2 Hsat2.
                unfold matchesb in *; simpl in *.
                rewrite forallb_forall in Hsat2.
                ltac1:(case_match).
                {
                    reflexivity.
                }
                ltac1:(exfalso).
                ltac1:(assert(H': ~ (forallb (matchesb ρ' ()) (fr_scs r) = true))).
                {
                    ltac1:(rewrite H).
                    intros HContra. inversion HContra.
                }
                clear H.
                rewrite forallb_forall in H'.
                apply H'. intros x. specialize (Hsat2 x). clear H'.
                intros Hin. specialize (Hsat2 Hin). clear Hin.
                (* FIXME I should extract this to a separate proof but am too tired today. *)
                unfold matchesb in *; simpl in *.
                induction x; simpl in *.
                {
                    unfold matchesb in *; simpl in *.
                    induction c; simpl in *.
                    {
                        reflexivity.
                    }
                    {
                        unfold matchesb in *; simpl in *.
                        induction ap; simpl in *.
                        {
                            rewrite andb_true_iff.
                            rewrite andb_true_iff in Hsat2.
                            destruct Hsat2 as [Hs1 Hs2].
                            apply bool_decide_eq_true in Hs1.
                            rewrite bool_decide_eq_true.
                            unfold isSome in *.
                            destruct (Expression_evaluate ρ e1) eqn:Hev1.
                            {
                                clear Hs2. symmetry in Hs1.
                                assert (He1 := Expression_evalute_total_iff e1 ρ).
                                rewrite Hev1 in He1.
                                apply proj1 in He1.
                                ltac1:(ospecialize (He1 _)).
                                {
                                    eexists. reflexivity.
                                }
                                assert (He2 := Expression_evalute_total_iff e2 ρ).
                                rewrite Hs1 in He2.
                                apply proj1 in He2.
                                ltac1:(ospecialize (He2 _)).
                                {
                                    eexists. reflexivity.
                                }
                                assert (Hsame1 := Expression_evalute_total_same e1).
                                assert (Hsame2 := Expression_evalute_total_same e2).
                                unfold vars_of in *. simpl in *.
                                erewrite Hsame1 with (ρ2 := ρ).
                                {

                                }
                                {
                                    assumption.
                                }
                                Search Expression_evaluate.
                                eapply Expression_evaluate_extensive_Some in Hs1.
                            }
                            {
                                inversion Hs2.
                            }
                            
                            Search Expression_evaluate.
                        }
                    }
                }
            }
            {
                assumption.
            }
        }
        unfold is_Some in Heqfound.
        apply Heqfound.
        exists ρ'.
        reflexivity.
    }
Qed.


Lemma thy_lhs_match_one_Some
    {Σ : Signature}
    {CΣ : ComputableSignature}
    (e : GroundTerm)
    (Γ : list FlattenedRewritingRule)
    (r : FlattenedRewritingRule)
    (ρ : Valuation)
    :
    thy_lhs_match_one e Γ = Some (r, ρ) ->
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
        rewrite list_lookup_fmap in Hot1.
        rewrite fmap_Some in Hot1.
        destruct Hot1 as [frr [Hfrr1 Hfrr2]].
        subst.
        destruct H12 as [H121 H122].
        destruct H121 as [ρ' Hρ'].
        rewrite bind_Some in H2.
        destruct H2 as [ρ'' [Hρ''1 Hρ''2]].
        rewrite bind_Some in Hρ''2.
        destruct Hρ''2 as [frr2 [Hfrr21 Hfrr22]].
        inversion Hfrr22; subst; clear Hfrr22.
        split.
        {
            rewrite elem_of_list_lookup.
            exists idx. exact Hfrr21.
        }
        apply try_match_correct in Hρ'.
        apply try_match_correct in Hρ''1.
        unfold Valuation in *.
        ltac1:(unshelve(eapply matchesb_implies_satisfies)).
        ltac1:(cut (frr = r)).
        {
            intros ?. subst. assumption.
        }
        {
            ltac1:(naive_solver).
        }
    }
Qed.


Definition naive_interpreter
    {Σ : Signature}
    {CΣ : ComputableSignature}
    (Γ : list FlattenedRewritingRule)
    (e : GroundTerm)
    : option GroundTerm
:=
    let oρ : option (FlattenedRewritingRule*Valuation)
        := thy_lhs_match_one e Γ in
    match oρ with
    | None => None
    | Some (r,ρ) => (evaluate_rhs_pattern ρ (fr_to r))
    end
.

Lemma naive_interpreter_sound
    {Σ : Signature}
    {CΣ : ComputableSignature}
    (Γ : list FlattenedRewritingRule)
    : FlatInterpreter_sound Γ (naive_interpreter Γ).
Proof.
    unfold naive_interpreter.
    unfold FlatInterpreter_sound.
    unfold flat_stuck,not_stuck_flat.
    split.
    {
        intros e Hstuck.
        destruct (thy_lhs_match_one e Γ) eqn:Hmatch>[|reflexivity].
        {
            destruct p as [r ρ].
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
                split>[assumption|].
                split>[assumption|].
                (* Almost there!*)
                admit.
            }
        }
    }
    {
        intros e Hnotstuck.
        unfold naive_interpreter.
        destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
        {
            destruct p as [r ρ]; cbn in *.
            apply thy_lhs_match_one_Some in Hmatch.
            destruct Hmatch as [Hin Hsat].
            destruct (evaluate_rhs_pattern ρ (fr_to r)) eqn:Heval.
            {
                eexists. reflexivity.
            }
            {
                ltac1:(exfalso).
                unfold thy_weakly_well_defined in Hwwd.
                specialize (Hwwd r Hin).
                unfold rule_weakly_well_defined in Hwwd.
                specialize (Hwwd e ρ Hsat).
                destruct Hwwd as [e' Hsate'].
                apply evaluate_rhs_rule_correct. in Heval.
            }
        }
    }
Qed.




End with_decidable_signature.
