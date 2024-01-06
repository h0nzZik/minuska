
From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
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
        := (try_match e) <$> froms
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
        r ∈ Γ /\ satisfies ρ e (fr_from r)
.
Proof.
    unfold thy_lhs_match_one.
    intros H [r [ρ [Hin HContra]]].
    destruct (list_find is_Some (try_match e <$> (fr_from <$> Γ))) eqn:Heqfound.
    {
        destruct p as [n oρ].
        rewrite list_find_Some in Heqfound.
        ltac1:(destruct Heqfound as [Hfound [HSome HFirst]]).
        destruct oρ.
        {
            subst. clear HFirst.
            rewrite bind_None in H.
            destruct H as [H|H].
            {
                inversion H.
            }
            destruct H as [[idx oρ] [H1 H2]].
            simpl in *.
            inversion H1; subst; clear H1.
            clear HSome.
            rewrite bind_None in H2.
            destruct H2 as [H|H].
            {
                inversion H.
            }
            destruct H as [oρ2 [H21 H22]].
            rewrite bind_None in H22.
            inversion H21; subst; clear H21.
            rewrite list_lookup_fmap in Hfound.
            rewrite fmap_Some in Hfound.
            destruct Hfound as [ot [Hot1 Hot2]].
            rewrite list_lookup_fmap in Hot1.
            rewrite fmap_Some in Hot1.
            destruct Hot1 as [fr [Hfr1 Hfr2]].
            rewrite Hfr1 in H22.
            destruct H22 as [H|H].
            { inversion H. }
            subst ot.
            destruct H as [frr [Hfrr1 Hfrr2]].
            inversion Hfrr2.
        }
        {
            inversion HSome. inversion H0.
        }
    }
    {
        clear H.
        rewrite list_find_None in Heqfound.
        rewrite Forall_forall in Heqfound.
        ltac1:(unshelve(eapply satisfies_implies_matchesb in HContra)).
        {
            unfold GroundTerm, OpenTerm.
            apply _.
        }
        apply try_match_complete in HContra.
        destruct HContra as [ρ' [H1 [H2 H3]]].

        specialize (Heqfound (Some ρ')).
        ltac1:(ospecialize (Heqfound _)).
        {
            rewrite <- elem_of_list_In.
            unfold Valuation in *.
            rewrite elem_of_list_fmap.
            exists (fr_from r).
            split.
            {
                symmetry. assumption.
            }
            rewrite elem_of_list_fmap.
            exists r.
            split>[reflexivity|].
            assumption.
        }
        unfold is_Some in Heqfound.
        apply Heqfound.
        exists ρ'.
        reflexivity.
    }
Qed.


    Lemma thy_lhs_match_one_Some
        (e : Element)
        (Γ : RewritingTheory)
        (r : RewritingRule)
        (ρ : Valuation)
        :
        thy_lhs_match_one e Γ = Some (r, ρ) ->
        r ∈ Γ /\ rr_satisfies LR_Left ρ r e
    .
    Proof.
        intros H.
        unfold thy_lhs_match_one in H.
        unfold is_Some in H.
        (repeat ltac1:(case_match)); subst.
        {
            inversion H; subst; clear H.
            ltac1:(rewrite list_find_Some in H0).
            ltac1:(rewrite list_lookup_fmap in H0).
            ltac1:(rewrite H3 in H0).
            ltac1:(rewrite fmap_Some in H0).
            ltac1:(destruct_and!).
            destruct_ex!.
            ltac1:(destruct_and!).
            ltac1:(simplify_eq /=).
            symmetry in H0.
            ltac1:(rewrite lhs_match_one_Some in H0).
            split>[()|apply H0].
            apply elem_of_list_lookup_2 in H3.
            exact H3.
        }
        {
            inversion H.
        }
        {
            inversion H.
        }
        {
            inversion H.
        }
    Qed.

    Lemma weakly_well_defined_baked_in ρ r e:
        rr_satisfies LR_Left ρ r e ->
        exists e', rr_satisfies LR_Right ρ r e'
    .
    Proof.
        intros H.
        ltac1:(funelim (rr_satisfies LR_Left ρ r e));
            ltac1:(simp rr_satisfies in H).
        {
            
        }
    Qed.

    Definition naive_interpreter
        (Γ : RewritingTheory)
        (e : Element)
        : option Element
    :=
        let oρ : option (RewritingRule*Valuation) := thy_lhs_match_one e Γ in
        match oρ with
        | None => None
        | Some (r,ρ) => (rhs_evaluate_rule ρ r)
        end
    .

    Lemma naive_interpreter_sound
        (Γ : RewritingTheory)
     : Interpreter_sound Γ (naive_interpreter Γ).
    Proof.
        split.
        {
            unfold naive_interpreter.
            unfold Interpreter_sound.
            unfold stuck,not_stuck.
            intros e Hstuck.
            destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
            {
                destruct p as [r ρ].
                {
                    apply thy_lhs_match_one_Some in Hmatch.
                    destruct Hmatch as [Hin Hsat].
                    ltac1:(rewrite -lhs_match_one_Some in Hsat).
                    unfold rewriting_relation, rewrites_to in Hstuck.
                    destruct (rhs_evaluate_rule ρ r) eqn:Heval; cbn in *.
                    {
                        apply lhs_match_one_Some in Hsat.
                        apply rhs_evaluate_rule_correct_1 in Heval.
                        ltac1:(exfalso).
                        apply Hstuck. clear Hstuck.
                        unfold rewrites_in_valuation_to.
                        exists e0.
                        exists r.
                        split.
                        { exact Hin. }
                        exists ρ.
                        split; assumption.
                    }
                    {
                        reflexivity.
                    }
                }
            }
            {
                reflexivity.
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
                destruct (rhs_evaluate_rule ρ r) eqn:Heval.
                {
                    exists e0. reflexivity.
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
