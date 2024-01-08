From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    basic_matching
.


Definition use_left
{Σ : Signature}
(og1 og2: option GroundTerm): option GroundTerm :=
match og1, og2 with
| None, None => None
| Some g1, None => Some g1
| None, Some g2 => Some g2
| Some g1, Some g2 => Some g1
end.

Definition valuations_compatible
    {Σ : Signature}
    (ρ1 ρ2 : Valuation) : bool
    := forallb (fun k => bool_decide (ρ1 !! k = ρ2 !! k)) (elements (dom ρ1 ∩ dom ρ2))
.

Definition merge_valuations
    {Σ : Signature}
    (ρ1 ρ2 : Valuation)
    : option Valuation :=
if decide (valuations_compatible ρ1 ρ2)
then
    Some (merge use_left ρ1 ρ2)
else
    None
.

Lemma merge_valuations_correct
    {Σ : Signature}
    (ρ1 ρ2 ρ : Valuation):
    merge_valuations ρ1 ρ2 = Some ρ ->
    ρ1 ⊆ ρ /\
    ρ2 ⊆ ρ
.
Proof.
    unfold Valuation in *.
    unfold merge_valuations.
    unfold is_left.
    destruct (decide (valuations_compatible ρ1 ρ2)) as [Hcompat|Hnocompat]; intros H.
    {
        inversion H; subst; clear H.
        unfold valuations_compatible in Hcompat.
        unfold is_true in Hcompat.
        rewrite forallb_forall in Hcompat; cbn.
        ltac1:(setoid_rewrite <- elem_of_list_In in Hcompat).
        ltac1:(setoid_rewrite elem_of_elements in Hcompat).
        split; intros i;
            destruct (ρ1 !! i) eqn:Hρ1i;
            destruct (ρ2 !! i) eqn:Hρ2i;
            destruct (merge use_left ρ1 ρ2 !! i) eqn:Hmergei;
            simpl;
            try (exact I);
            ltac1:(rewrite lookup_merge in Hmergei);
            unfold diag_None in Hmergei;
            specialize (Hcompat i);
            ltac1:(rewrite Hρ1i in Hmergei);
            ltac1:(rewrite Hρ2i in Hmergei);
            unfold use_left in Hmergei;
            ltac1:(simplify_eq /=);
            try reflexivity
        .
        
        ltac1:(ospecialize (Hcompat _)).
        {
            rewrite elem_of_intersection.
            do 2 ltac1:(rewrite elem_of_dom).
            split; eexists.
            {
                apply Hρ1i.
            }
            {
                apply Hρ2i.
            }
        }
        apply bool_decide_eq_true_1 in Hcompat.
        unfold Valuation in *.
        rewrite Hcompat in Hρ1i.
        rewrite Hρ1i in Hρ2i.
        ltac1:(congruence).
    }
    {
        inversion H.
    }
Qed.

Lemma merge_valuations_empty_r
    {Σ : Signature} x
    :
    merge_valuations x ∅ = Some x
.
Proof.
    unfold merge_valuations.
    ltac1:(case_match).
    {
        clear H.
        apply f_equal.
        rewrite <- merge_Some.
        intros i.
        unfold use_left.
        ltac1:(case_match).
        {
            ltac1:(rewrite lookup_empty).
            reflexivity.
        }
        {
            ltac1:(rewrite lookup_empty).
            reflexivity.
        }
        reflexivity.
    }
    {
        unfold is_left in H.
        ltac1:(case_match).
        { inversion H. }
        ltac1:(exfalso).
        apply n.
        unfold Valuation.
        unfold valuations_compatible.
        ltac1:(rewrite dom_empty_L).
        rewrite intersection_empty_r_L.
        rewrite elements_empty.
        reflexivity.
    }
Qed.

Lemma merge_valuations_empty_l
    {Σ : Signature} x:
    merge_valuations ∅ x = Some x
.
Proof.
    unfold merge_valuations.
    ltac1:(case_match).
    {
        clear H.
        apply f_equal.
        rewrite <- merge_Some.
        intros i.
        unfold use_left.
        repeat ltac1:(case_match);
            try reflexivity.
        {
            ltac1:(rewrite lookup_empty in H).
            inversion H.
        }
        {
            ltac1:(rewrite lookup_empty in H).
            inversion H.
        }
        reflexivity.
    }
    {
        unfold is_left in H.
        ltac1:(case_match).
        { inversion H. }
        ltac1:(exfalso).
        apply n.
        unfold Valuation.
        unfold valuations_compatible.
        ltac1:(rewrite dom_empty_L).
        rewrite intersection_empty_l_L.
        rewrite elements_empty.
        reflexivity.
    }
Qed.


Lemma merge_use_left_subseteq
    {Σ : Signature}
    (ρ1 ρ2 : Valuation):
    ρ1 ⊆ ρ2 ->
    merge use_left ρ1 ρ2 = ρ2
.
Proof.
    unfold subseteq. simpl.
    unfold Subseteq_Valuation.
    unfold Valuation in *. simpl.
    unfold map_subseteq.
    unfold map_included.
    unfold map_relation.
    unfold option_relation.
    intros H.
    apply map_subseteq_po.
    {
        unfold Valuation.
        rewrite map_subseteq_spec.
        intros i x Hix.
        rewrite lookup_merge in Hix.
        unfold diag_None in Hix.
        unfold use_left in Hix.
        ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
        {
            specialize (H i).
            rewrite H0 in H.
            rewrite H1 in H.
            subst.
            reflexivity.
        }
        {
            specialize (H i).
            rewrite H0 in H.
            rewrite H1 in H.
            inversion H.
        }
    }
    {
        unfold Valuation.
        rewrite map_subseteq_spec.
        intros i x Hix.
        rewrite lookup_merge.
        unfold diag_None.
        unfold use_left.
        ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
        specialize (H i).
        rewrite H1 in H.
        rewrite H0 in H.
        subst.
        reflexivity.
    }
Qed.


Lemma merge_valuations_dom
    {Σ : Signature}
    (ρ1 ρ2 ρ : Valuation):
    merge_valuations ρ1 ρ2 = Some ρ ->
    dom ρ = dom ρ1 ∪ dom ρ2
.
Proof.
    assert (Hm := merge_valuations_correct ρ1 ρ2 ρ).
    unfold merge_valuations in *.
    destruct (decide (valuations_compatible ρ1 ρ2)); simpl in *;
        intros H; inversion H; subst; clear H.
    apply leibniz_equiv.
    rewrite set_equiv_subseteq.
    split.
    {
        clear Hm.
        rewrite elem_of_subseteq.
        intros x Hx.
        unfold Valuation in *.
        rewrite elem_of_dom in Hx.
        rewrite elem_of_union.
        rewrite elem_of_dom.
        rewrite elem_of_dom.
        destruct Hx as [y Hy].
        rewrite lookup_merge in Hy.
        unfold diag_None, use_left in Hy.
        ltac1:(repeat case_match; simplify_eq/=);
            unfold is_Some.
        {
            left; eexists; reflexivity.
        }
        {
            left; eexists; reflexivity.
        }
        {
            right; eexists; reflexivity.
        }
    }
    {
        specialize (Hm eq_refl).
        destruct Hm as [Hm1 Hm2].
        rewrite union_subseteq.
        rewrite elem_of_subseteq.
        rewrite elem_of_subseteq.
        unfold Valuation in *.
        split; intros x Hx; rewrite elem_of_dom in Hx;
            destruct Hx as [y Hy]; rewrite elem_of_dom;
            exists y; eapply lookup_weaken>[apply Hy|];
            assumption.
    }
Qed.


Lemma omap_Some
    {Σ : Signature}
    (ρ : Valuation):
    omap [eta Some] ρ = ρ
.
Proof.
    rewrite <- map_fmap_alt.
    rewrite map_fmap_id.
    reflexivity.
Qed.

Class TryMatch
    {Σ : Signature}
    (A B : Type)
    {_VB: VarsOf B variable}
    {_SAB : Satisfies Valuation A B variable}
    {_MAB : Matches Valuation A B variable}
    :=
{
    try_match :
        A -> B -> option Valuation ;

    try_match_correct :
        ∀ (a : A) (b : B) (ρ : Valuation),
            try_match a b = Some ρ ->
            matchesb ρ a b = true ;

    try_match_complete :
        ∀ (a : A) (b : B) (ρ : Valuation),
            matchesb ρ a b = true ->
            ∃ (ρ' : Valuation),
                vars_of ρ' = vars_of b /\
                ρ' ⊆ ρ /\
                try_match a b = Some ρ' ;

    (* It does not invent variables out of thin air *)
    try_match_noOOTA :
        ∀ (a : A) (b : B) (ρ : Valuation),
            try_match a b = Some ρ ->
            vars_of ρ ⊆ vars_of b
}.

Fixpoint ApppliedOperator'_try_match_AppliedOperator'
    {Σ : Signature}
    {Operand1 Operand2 : Type}
    {_VOperand2 : VarsOf Operand2 variable}
    {_S0 : Satisfies Valuation (Operand1) Operand2 variable}
    {_M0 : Matches Valuation (Operand1) Operand2 variable}
    {_TM0 : TryMatch Operand1 Operand2}
    {_S1 : Satisfies Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_M1 : Matches Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_TM1 : TryMatch Operand1 (AppliedOperator' symbol Operand2)}
    {_S2 : Satisfies Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_M2 : Matches Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_TM2 : TryMatch (AppliedOperator' symbol Operand1) Operand2}
    (x : AppliedOperator' symbol Operand1)
    (y : AppliedOperator' symbol Operand2)
    :
    option Valuation
:=
match x, y with
| ao_operator a1, ao_operator a2 =>
    if decide (a1 = a2) then Some ∅ else None
| ao_operator _, ao_app_operand _ _ => None
| ao_operator _, ao_app_ao _ _ => None
| ao_app_operand _ _ , ao_operator _ => None
| ao_app_operand app1 o1, ao_app_operand app2 o2 =>
    ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
        app1
        app2;
    ρ2 ← try_match o1 o2;
    merge_valuations ρ1 ρ2

| ao_app_operand app1 o1, ao_app_ao app2 o2 =>
    ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
        app1
        app2 ;
    ρ2 ← try_match o1 o2;
    merge_valuations ρ1 ρ2

(* TODO? *)
| ao_app_ao app1 o1, ao_operator _ => None

| ao_app_ao app1 o1, ao_app_operand app2 o2 =>
    ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
        app1
        app2 ;
    ρ2 ← try_match o1 o2;
    merge_valuations ρ1 ρ2

| ao_app_ao app1 o1, ao_app_ao app2 o2 =>
    ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
        app1
        app2 ;
    ρ2 ← ApppliedOperator'_try_match_AppliedOperator' 
        o1
        o2 ;
    merge_valuations ρ1 ρ2
end.

(*
    Note: I think that this lemma needs to be formulated in this
    generalized way, with two valuations related by inclusion.
    The interface, as represented by the `TryMatch` class,
    hides this detail.
*)
Lemma ApppliedOperator'_try_match_AppliedOperator'_correct
    {Σ : Signature}
    {Operand1 Operand2 : Type}
    {_VOperand1 : VarsOf Operand1 variable}
    {_VOperand2 : VarsOf Operand2 variable}
    {_S0 : Satisfies Valuation (Operand1) Operand2 variable}
    {_M0 : Matches Valuation (Operand1) Operand2 variable}
    {_TM0 : TryMatch Operand1 Operand2}
    {_S1 : Satisfies Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_M1 : Matches Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_TM1 : TryMatch Operand1 (AppliedOperator' symbol Operand2)}
    {_S2 : Satisfies Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_M2 : Matches Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_TM2 : TryMatch (AppliedOperator' symbol Operand1) Operand2}
    (ρ ρ' : Valuation)
    (a : AppliedOperator' symbol Operand1)
    (b : AppliedOperator' symbol Operand2)
    :
    ρ ⊆ ρ' ->
    ApppliedOperator'_try_match_AppliedOperator' a b = Some ρ ->
    matchesb ρ' a b = true
.
Proof.
    revert b ρ ρ'.
    induction a; intros b' ρ ρ' HH H; destruct b'; cbn in *; intros.
    {
        intros.
        unfold is_left in *.
        unfold decide,bool_decide in *.
        repeat ltac1:(case_match); subst; simpl;
            try reflexivity; try ltac1:(congruence).
        {
            ltac1:(simplify_eq/=).
            unfold matchesb. simpl.
            unfold bool_decide; ltac1:(case_match); subst;
                ltac1:(congruence).
        }
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
    {
        rewrite bind_Some in H.
        destruct H as [x [H21 H22]].
        rewrite bind_Some in H22.
        destruct H22 as [x0 [H221 H222]].
        

        assert (H221' := H221).
        apply try_match_correct in H221.
        assert (H222' := H222).
        apply merge_valuations_correct in H222'.
        destruct H222' as [Hsub1 Hsub2].

        assert (IH := IHa _ _ _ Hsub1 H21).
        unfold matchesb; simpl.
        apply matchesb_ext with (v2 := ρ') in IH>[|assumption].
        unfold matchesb in IH; simpl in IH.
        rewrite IH; simpl.
        eapply matchesb_ext in H221>[|apply Hsub2].
        eapply matchesb_ext in H221>[|apply HH].
        assumption.
    }
    {
        rewrite bind_Some in H.
        destruct H as [x [H21 H22]].
        unfold matchesb; simpl.
        rewrite bind_Some in H22.
        destruct H22 as [x0 [Hx01 Hx02]].
        apply merge_valuations_correct in Hx02.
        apply try_match_correct in Hx01.
        eapply matchesb_ext in Hx01>[|apply Hx02].
        eapply matchesb_ext in Hx01>[|apply HH].
        rewrite Hx01.
        eapply IHa in H21>[|apply Hx02].
        eapply matchesb_ext in H21>[|apply HH].
        unfold matchesb in H21; simpl in H21.
        rewrite H21.
        reflexivity.
    }
    {
        inversion H.
    }
    {
        rewrite bind_Some in H.
        destruct H as [x [H21 H22]].
        rewrite bind_Some in H22.
        destruct H22 as [x0 [H221 H222]].
        apply merge_valuations_correct in H222.
        destruct H222 as [Hxρ Hx0ρ].
        unfold matchesb; simpl.

        assert (IH1 := IHa1 _ _ _ Hxρ H21).
        apply matchesb_ext with (v2 := ρ') in IH1>[|assumption].
        unfold matchesb in IH1; simpl in IH1.
        rewrite IH1; simpl.

        apply try_match_correct in H221.
        eapply matchesb_ext in H221>[|apply Hx0ρ].
        eapply matchesb_ext in H221>[|apply HH].
        exact H221.
    }
    {
        rewrite bind_Some in H.
        destruct H as [x [H21 H22]].
        rewrite bind_Some in H22.
        destruct H22 as [x0 [H221 H222]].
        assert (Hsub := H222).
        apply merge_valuations_correct in Hsub.
        destruct Hsub as [Hsub1 Hsub2].


        unfold matchesb; simpl.
        eapply IHa1 in H21>[|apply Hsub1].
        eapply IHa2 in H221>[|apply Hsub2].
        eapply matchesb_ext in H21>[|apply HH].
        eapply matchesb_ext in H221>[|apply HH].
        unfold matchesb in H21,H221. simpl in H21,H221.
        rewrite H21. rewrite H221.
        reflexivity.
    }
Qed.

(*
    I define this here only for Valuations
    to behave extensionaly.
*)
#[local]
Instance GTEquiv {Σ : Signature}
    : Equiv GroundTerm := (=).

#[local]
Instance GTLeibnizEquiv {Σ : Signature}
    : LeibnizEquiv GroundTerm.
Proof.
    intros x y H. apply H.
Qed.

Lemma dom_merge_use_left
    {Σ : Signature}
    (ρ' ρ'' : Valuation)
    :
    dom (merge use_left ρ' ρ'') = dom ρ'' ∪ dom ρ'
.
Proof.
    unfold Valuation in *.
    apply set_eq.
    intros x.
    rewrite elem_of_dom.
    unfold is_Some.
    rewrite lookup_merge.
    unfold diag_None.
    destruct (ρ' !! x) eqn:Heq1,(ρ'' !! x) eqn:Heq2; simpl.
    {
        split; intros H.
        { 
            destruct H as [x' Hx'].
            inversion Hx'; subst; clear Hx'.
            rewrite elem_of_union.
            left.
            rewrite elem_of_dom.
            exists g0. assumption.
        }
        {
            eexists. reflexivity.
        }
    }
    {
        split; intros H.
        {
            rewrite elem_of_union.
            right.
            rewrite elem_of_dom.
            exists g.
            assumption.
        }
        {
            eexists. reflexivity.
        }
    }
    {
        split; intros H.
        {
            rewrite elem_of_union.
            left.
            rewrite elem_of_dom.
            exists g.
            assumption.
        }
        {
            eexists. reflexivity.
        }
    }
    {
        split; intros H.
        {
            destruct H as [x' Hx'].
            inversion Hx'.
        }
        {
            rewrite elem_of_union in H.
            destruct H as [H|H].
            {
                rewrite elem_of_dom in H.
                destruct H as [g Hg].
                ltac1:(simplify_eq/=).
            }
            {
                rewrite elem_of_dom in H.
                destruct H as [g Hg].
                ltac1:(simplify_eq/=).
            }
        }
    }
Qed.

Lemma merge_use_left_below {Σ : Signature} (ρ ρ' ρ'': Valuation) :
    ρ' ⊆ ρ ->
    ρ'' ⊆ ρ ->
    merge use_left ρ' ρ'' ⊆ ρ
.
Proof.
    intros H1 H2.
    unfold Valuation in *.
    apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_merge in Hix.
    unfold diag_None, use_left in Hix.
    ltac1:(repeat case_match; simplify_eq/=).
    {
        eapply lookup_weaken.
        { apply H. }
        { assumption. }
    }
    {
        eapply lookup_weaken.
        { apply H. }
        { assumption. }
    }
    {
        eapply lookup_weaken.
        { apply H0. }
        { assumption. }
    }
Qed.

Lemma ApppliedOperator'_try_match_AppliedOperator'_complete
    {Σ : Signature}
    {Operand1 Operand2 : Type}
    {_VOperand1 : VarsOf Operand1 variable}
    {_VOperand2 : VarsOf Operand2 variable}
    {_S0 : Satisfies Valuation (Operand1) Operand2 variable}
    {_M0 : Matches Valuation (Operand1) Operand2 variable}
    {_TM0 : TryMatch Operand1 Operand2}
    {_S1 : Satisfies Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_M1 : Matches Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_TM1 : TryMatch Operand1 (AppliedOperator' symbol Operand2)}
    {_S2 : Satisfies Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_M2 : Matches Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_TM2 : TryMatch (AppliedOperator' symbol Operand1) Operand2}
    (ρ : Valuation)
    (a : AppliedOperator' symbol Operand1)
    (b : AppliedOperator' symbol Operand2)
    :
    matchesb ρ a b = true ->
    ∃ ρ',
        vars_of ρ' = vars_of b /\
        ρ' ⊆ ρ /\
        ApppliedOperator'_try_match_AppliedOperator' a b = Some ρ'
.
Proof.
    unfold Valuation in *.
    revert ρ b.
    induction a; intros ρ b''.
    {
        (*subst f.*) 
        unfold matchesb; simpl.
        unfold decide,decide_rel,is_left,bool_decide.
        repeat ltac1:(case_match); subst;
            intros H; try (ltac1:(congruence)).

        clear H.
        cbn.
        exists ∅.
        cbn.
        repeat split.
        unfold Valuation in *.
        apply map_empty_subseteq.
    }
    {
        cbn.
        destruct b''.
        {
            intros H; inversion H.
        }
        {
            intros H.
            unfold matchesb in H.
            simpl in H.
            rewrite andb_true_iff in H.
            destruct H as [H1 H2].
            specialize (IHa ρ b'' H1).
            destruct IHa as [ρ' [IH0 [IH1 IH2]]].
            apply try_match_complete in H2.
            destruct H2 as [ρ'' [Hρ''0 [Hρ''1 Hρ''2]]].
            rewrite IH2.
            cbn.
            rewrite Hρ''2.
            cbn.
            
            exists (merge use_left ρ' ρ'').
            split.
            {
                unfold vars_of; simpl.
                rewrite <- Hρ''0.
                unfold vars_of in IH0. simpl in IH0.
                rewrite <- IH0.
                unfold Valuation in *.
                rewrite dom_merge_use_left.
                clear.
                ltac1:(set_solver).
            }
            split.
            {
                apply merge_use_left_below; assumption.
            }
            {
                unfold merge_valuations.
                ltac1:(case_match).
                {
                    reflexivity.
                }
                {
                    ltac1:(exfalso).
                    apply bool_decide_eq_false in H.
                    apply H. clear H.
                    unfold valuations_compatible.
                    unfold is_true.
                    rewrite forallb_forall.
                    intros x Hx.
                    apply bool_decide_eq_true.
                    apply elem_of_list_In in Hx.
                    rewrite elem_of_elements in Hx.
                    rewrite elem_of_intersection in Hx.
                    destruct Hx as [Hxρ' Hxρ''].
                    unfold Valuation in *.
                    rewrite elem_of_dom in Hxρ'.
                    rewrite elem_of_dom in Hxρ''.
                    destruct Hxρ' as [g1 Hg1].
                    destruct Hxρ'' as [g2 Hg2].
                    rewrite Hg1.
                    rewrite Hg2.
                    apply f_equal.
                    apply lookup_weaken with (m2 := ρ) in Hg1>[|assumption].
                    apply lookup_weaken with (m2 := ρ) in Hg2>[|assumption].
                    ltac1:(simplify_eq/=).
                    reflexivity.
                }
            }   
        }
        {
            intros H.
            unfold matchesb in H.
            simpl in H.
            rewrite andb_true_iff in H.
            destruct H as [H1 H2].
            specialize (IHa ρ _ H1).
            destruct IHa as [ρ' [IH0 [IH1 IH2]]].
            apply try_match_complete in H2.
            destruct H2 as [ρ'' [Hρ''0 [Hρ''1 Hρ''2]]].
            rewrite IH2.
            cbn.
            rewrite Hρ''2.
            cbn.
            
            exists (merge use_left ρ' ρ'').
            split.
            {
                unfold vars_of in Hρ''0. simpl in Hρ''0.
                unfold vars_of; simpl.
                rewrite <- Hρ''0.
                unfold vars_of in IH0. simpl in IH0.
                rewrite <- IH0.
                unfold Valuation in *.
                rewrite dom_merge_use_left.
                clear.
                ltac1:(set_solver).
            }
            split.
            {
                apply merge_use_left_below; assumption.
            }
            {
                unfold merge_valuations.
                ltac1:(case_match).
                {
                    reflexivity.
                }
                {
                    ltac1:(exfalso).
                    apply bool_decide_eq_false in H.
                    apply H. clear H.
                    unfold valuations_compatible.
                    unfold is_true.
                    rewrite forallb_forall.
                    intros x Hx.
                    apply bool_decide_eq_true.
                    apply elem_of_list_In in Hx.
                    rewrite elem_of_elements in Hx.
                    rewrite elem_of_intersection in Hx.
                    destruct Hx as [Hxρ' Hxρ''].
                    unfold Valuation in *.
                    rewrite elem_of_dom in Hxρ'.
                    rewrite elem_of_dom in Hxρ''.
                    destruct Hxρ' as [g1 Hg1].
                    destruct Hxρ'' as [g2 Hg2].
                    rewrite Hg1.
                    rewrite Hg2.
                    apply f_equal.
                    apply lookup_weaken with (m2 := ρ) in Hg1>[|assumption].
                    apply lookup_weaken with (m2 := ρ) in Hg2>[|assumption].
                    ltac1:(simplify_eq/=).
                    reflexivity.
                }
            }   
        }
    }
    {
        cbn.
        destruct b''.
        {
            intros H; inversion H.
        }
        {
            intros H.
            unfold matchesb in H.
            simpl in H.
            rewrite andb_true_iff in H.
            destruct H as [H1 H2].
            unfold Valuation in *.
            specialize (IHa1 _ _ H1).

            destruct IHa1 as [ρ' [IH0 [IH1 IH2]]].
            apply try_match_complete in H2.
            destruct H2 as [ρ'' [Hρ''0 [Hρ''1 Hρ''2]]].
            rewrite IH2.
            cbn.
            rewrite Hρ''2.
            cbn.
            
            exists (merge use_left ρ' ρ'').
            split.
            {
                unfold vars_of; simpl.
                rewrite <- Hρ''0.
                unfold vars_of in IH0. simpl in IH0.
                rewrite <- IH0.
                unfold Valuation in *.
                rewrite dom_merge_use_left.
                clear.
                ltac1:(set_solver).
            }
            split.
            {
                apply merge_use_left_below; assumption.
            }
            {
                unfold merge_valuations.
                ltac1:(case_match).
                {
                    reflexivity.
                }
                {
                    ltac1:(exfalso).
                    apply bool_decide_eq_false in H.
                    apply H. clear H.
                    unfold valuations_compatible.
                    unfold is_true.
                    rewrite forallb_forall.
                    intros x Hx.
                    apply bool_decide_eq_true.
                    apply elem_of_list_In in Hx.
                    rewrite elem_of_elements in Hx.
                    rewrite elem_of_intersection in Hx.
                    destruct Hx as [Hxρ' Hxρ''].
                    unfold Valuation in *.
                    rewrite elem_of_dom in Hxρ'.
                    rewrite elem_of_dom in Hxρ''.
                    destruct Hxρ' as [g1 Hg1].
                    destruct Hxρ'' as [g2 Hg2].
                    rewrite Hg1.
                    rewrite Hg2.
                    apply f_equal.
                    apply lookup_weaken with (m2 := ρ) in Hg1>[|assumption].
                    apply lookup_weaken with (m2 := ρ) in Hg2>[|assumption].
                    ltac1:(simplify_eq/=).
                    reflexivity.
                }
            }   
        }
        {
            intros H.
            unfold matchesb in H.
            simpl in H.
            rewrite andb_true_iff in H.
            destruct H as [H1 H2].
            specialize (IHa1 _ _ H1).
            specialize (IHa2 _ _ H2).
            destruct IHa1 as [ρ1' [IH10 [IH11 IH12]]].
            destruct IHa2 as [ρ2' [IH20 [IH21 IH22]]].
            
            exists (merge use_left ρ1' ρ2').
            split.
            {
                unfold vars_of in *|-. simpl in *|-.
                simpl.
                unfold vars_of; simpl.
                rewrite <- IH10.
                rewrite <- IH20.
                unfold Valuation in *.
                rewrite dom_merge_use_left.
                clear.
                ltac1:(set_solver).
            }
            split.
            {
                apply merge_use_left_below; assumption.
            }
            {
                rewrite bind_Some.
                eexists.
                split>[apply IH12|].
                rewrite bind_Some.
                eexists.
                split>[apply IH22|].
                unfold merge_valuations.
                ltac1:(case_match).
                {
                    reflexivity.
                }
                {
                    ltac1:(exfalso).
                    apply bool_decide_eq_false in H.
                    apply H. clear H.
                    unfold valuations_compatible.
                    unfold is_true.
                    rewrite forallb_forall.
                    intros x Hx.
                    apply bool_decide_eq_true.
                    apply elem_of_list_In in Hx.
                    rewrite elem_of_elements in Hx.
                    rewrite elem_of_intersection in Hx.
                    destruct Hx as [Hxρ' Hxρ''].
                    unfold Valuation in *.
                    rewrite elem_of_dom in Hxρ'.
                    rewrite elem_of_dom in Hxρ''.
                    destruct Hxρ' as [g1 Hg1].
                    destruct Hxρ'' as [g2 Hg2].
                    rewrite Hg1.
                    rewrite Hg2.
                    apply f_equal.
                    apply lookup_weaken with (m2 := ρ) in Hg1>[|assumption].
                    apply lookup_weaken with (m2 := ρ) in Hg2>[|assumption].
                    ltac1:(simplify_eq/=).
                    reflexivity.
                }
            }   
        }
    }
Qed.

#[export]
Program Instance TryMatch_AppliedOperator'
    {Σ : Signature}
    {Operand1 Operand2 : Type}
    {_VOperand1 : VarsOf Operand1 variable}
    {_VOperand2 : VarsOf Operand2 variable}
    {_S0 : Satisfies Valuation (Operand1) Operand2 variable}
    {_M0 : Matches Valuation (Operand1) Operand2 variable}
    {_TM0 : TryMatch Operand1 Operand2}
    {_S1 : Satisfies Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_M1 : Matches Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_TM1 : TryMatch Operand1 (AppliedOperator' symbol Operand2)}
    {_S2 : Satisfies Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_M2 : Matches Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_TM2 : TryMatch (AppliedOperator' symbol Operand1) Operand2}
:
    TryMatch (AppliedOperator' symbol Operand1) (AppliedOperator' symbol Operand2)
:= {|
    try_match := ApppliedOperator'_try_match_AppliedOperator' ;
    try_match_correct := _;
    try_match_complete := _;
|}.
Next Obligation.
    apply ApppliedOperator'_try_match_AppliedOperator'_correct with (ρ := ρ).
    { 
        unfold Valuation in *.
        apply reflexivity.
    }
    { apply H. }
Qed.
Next Obligation.
    apply ApppliedOperator'_try_match_AppliedOperator'_complete.
    assumption.
Qed.
Next Obligation.
    revert a ρ H H0.
    induction b; unfold vars_of; simpl in *; intros a' ρ' H' H'0.
    {
        destruct a'; simpl in *; ltac1:(repeat case_match; simplify_eq/=).
        apply H'0.
    }
    {
        destruct a'; simpl in *; ltac1:(simplify_eq/=).
        {
            rewrite bind_Some in H'.
            destruct H' as [x0 [H1x0 H2x0]].
            rewrite bind_Some in H2x0.
            destruct H2x0 as [x1 [H1x1 H2x1]].
            assert (H2x1' := H2x1).
            apply merge_valuations_dom in H2x1'.
            unfold Valuation in *.
            rewrite H2x1' in H'0.
            rewrite elem_of_union in H'0.
            destruct H'0 as [H|H].
            {
                specialize (IHb a' x0 H1x0 H).
                rewrite elem_of_union.
                right. apply IHb.
            }
            {
                apply try_match_noOOTA in H1x1.
                clear - H1x1 H.
                ltac1:(set_solver).
            }
        }
        {
            rewrite bind_Some in H'.
            destruct H' as [x0 [H1x0 H2x0]].
            rewrite bind_Some in H2x0.
            destruct H2x0 as [x1 [H1x1 H2x1]].
            assert (H2x1' := H2x1).
            apply merge_valuations_dom in H2x1'.
            unfold Valuation in *.
            rewrite H2x1' in H'0.
            rewrite elem_of_union in H'0.
            destruct H'0 as [H|H].
            {
                assert (IH := IHb a'1).
                specialize (IH x0 H1x0 H).
                rewrite elem_of_union.
                right. apply IH.
            }
            {
                apply try_match_noOOTA in H1x1.
                clear - H1x1 H.
                ltac1:(set_solver).
            }
        }
    }
    {
        destruct a'; simpl in *; ltac1:(simplify_eq/=).
        {
            rewrite bind_Some in H'.
            destruct H' as [x0 [H1x0 H2x0]].
            rewrite bind_Some in H2x0.
            destruct H2x0 as [x1 [H1x1 H2x1]].
            assert (H2x1' := H2x1).
            apply merge_valuations_dom in H2x1'.
            unfold Valuation in *.
            rewrite H2x1' in H'0.
            rewrite elem_of_union in H'0.
            destruct H'0 as [H|H].
            {
                assert (IH1 := IHb1 a').
                specialize (IH1 x0 H1x0 H).
                rewrite elem_of_union.
                left. apply IH1.
            }
            {
                apply try_match_noOOTA in H1x1.
                clear - H1x1 H.
                ltac1:(set_solver).
            }
        }
        {
            rewrite bind_Some in H'.
            destruct H' as [x0 [H1x0 H2x0]].
            rewrite bind_Some in H2x0.
            destruct H2x0 as [x1 [H1x1 H2x1]].
            assert (H2x1' := H2x1).
            apply merge_valuations_dom in H2x1'.
            unfold Valuation in *.
            rewrite H2x1' in H'0.
            rewrite elem_of_union in H'0.
            destruct H'0 as [H|H].
            {
                assert (IH1 := IHb1 a'1).
                specialize (IH1 _ H1x0 H).
                rewrite elem_of_union.
                left. apply IH1.
            }
            {
                assert (IH2 := IHb2 a'2).
                specialize (IH2 _ H1x1 H).
                rewrite elem_of_union.
                right. apply IH2.
            }
        }
    }
Qed.
Fail Next Obligation.

Definition ApppliedOperatorOr'_try_match_AppliedOperatorOr'
    {Σ : Signature}
    {Operand1 Operand2 : Type}
    {_V1 : VarsOf Operand1 variable}
    {_V2 : VarsOf Operand2 variable}
    {_S1 : Satisfies Valuation Operand1 Operand2 variable}
    {_M1 : Matches Valuation Operand1 Operand2 variable}
    {_TM1 : TryMatch Operand1 Operand2}
    {_S2 : Satisfies Valuation Operand1 (AppliedOperator' symbol Operand2) variable}
    {_M2 : Matches Valuation Operand1 (AppliedOperator' symbol Operand2) variable}
    {_TM2 : TryMatch Operand1 (AppliedOperator' symbol Operand2)}
    {_S3 : Satisfies Valuation (AppliedOperator' symbol Operand1) Operand2 variable}
    {_M3 : Matches Valuation (AppliedOperator' symbol Operand1) Operand2 variable}
    {_TM3 : TryMatch (AppliedOperator' symbol Operand1) Operand2}
    (x : AppliedOperatorOr' symbol Operand1)
    (y : AppliedOperatorOr' symbol Operand2)
    : option Valuation :=
match x, y with
| aoo_app _ _ app1, aoo_app _ _ app2 =>
    try_match app1 app2
| aoo_app _ _ app1, aoo_operand _ _ o2 =>
    try_match app1 o2
| aoo_operand _ _ o1, aoo_app _ _ app2 =>
    None (* try_match o1 app2 *)
| aoo_operand _ _ o1, aoo_operand _ _ o2 =>
    try_match o1 o2
end.


#[export]
Program Instance TryMatch_AppliedOperatorOr'
    {Σ : Signature}
    {Operand1 Operand2 : Type}
    {_VOperand1 : VarsOf Operand1 variable}
    {_VOperand2 : VarsOf Operand2 variable}
    {_S0 : Satisfies Valuation (Operand1) Operand2 variable}
    {_M0 : Matches Valuation (Operand1) Operand2 variable}
    {_TM0 : TryMatch Operand1 Operand2}
    {_S1 : Satisfies Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_M1 : Matches Valuation (Operand1) (AppliedOperator' symbol Operand2) variable}
    {_TM1 : TryMatch Operand1 (AppliedOperator' symbol Operand2)}
    {_S2 : Satisfies Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_M2 : Matches Valuation ((AppliedOperator' symbol Operand1)) Operand2 variable}
    {_TM2 : TryMatch (AppliedOperator' symbol Operand1) Operand2}
:
    TryMatch (AppliedOperatorOr' symbol Operand1) (AppliedOperatorOr' symbol Operand2)
:= {|
    try_match := ApppliedOperatorOr'_try_match_AppliedOperatorOr' ;
    try_match_correct := _;
    try_match_complete := _;
|}.
Next Obligation.
    destruct a,b; simpl in *; unfold matchesb; simpl.
    {
        apply try_match_correct. apply H.
    }
    {
        apply try_match_correct. apply H.
    }
    {
        inversion H.
    }
    {
        apply try_match_correct. apply H.
    }
Qed.
Next Obligation.
    destruct a,b; simpl in *; unfold matchesb in *; simpl in *.
    {
        apply try_match_complete in H.
        assumption.
    }
    {
        apply try_match_complete in H.
        assumption.
    }
    {
        inversion H.
    }
    {
        apply try_match_complete in H.
        assumption.
    }
Qed.
Fail Next Obligation.


Definition builtin_value_try_match_BuiltinOrVar
    {Σ : Signature}
    :
    builtin_value -> BuiltinOrVar -> option Valuation :=
fun b bv =>
match bv with
| bov_builtin b' => if (decide (b = b')) then Some ∅ else None
| bov_variable x => Some (<[x := (aoo_operand _ _ b)]>∅)
end.


#[export]
Program Instance TryMatch__builtin__BoV
    {Σ : Signature}
:
    TryMatch builtin_value BuiltinOrVar
:= {|
    try_match := builtin_value_try_match_BuiltinOrVar ;
    try_match_correct := _;
    try_match_complete := _;
|}.
Next Obligation.
    destruct b; unfold matchesb; simpl in *.
    {
        unfold bool_decide.
        ltac1:(case_match).
        {
            apply bool_decide_eq_true in H0.
            inversion H; subst; clear H.
            ltac1:(case_match);try reflexivity; try ltac1:(contradiction).
        }
        {
            ltac1:(simplify_eq/=).
        }
    }
    {
        inversion H; subst; clear H.
        unfold Valuation in *.
        rewrite lookup_insert.
        apply bool_decide_eq_true.
        reflexivity.
    }
Qed.
Next Obligation.
    unfold Valuation in *.
    unfold matchesb in H; destruct b; simpl in H.
    {
        apply bool_decide_eq_true in H.
        subst. simpl.
        exists ∅.
        split.
        {
            unfold vars_of; simpl.
            unfold Valuation in *.
            rewrite dom_empty_L.
            reflexivity.
        }
        split.
        {
            apply map_empty_subseteq.
        }
        {
            ltac1:(case_match).
            {
                reflexivity.
            }
            {
                apply bool_decide_eq_false in H.
                ltac1:(contradiction).
            }
        }
    }
    {
        ltac1:(repeat case_match); subst; simpl.
        { inversion H. }
        {
            apply bool_decide_eq_true in H.
            subst.
            exists (<[x:=aoo_operand symbol builtin_value operand]> ∅).
            split.
            {
                unfold vars_of; simpl.
                unfold Valuation in *.
                rewrite dom_insert_L.
                ltac1:(set_solver).
            }
            split.
            {
                apply map_subseteq_spec.
                intros i x0 Hix0.
                destruct (decide (x = i)).
                {
                    subst.
                    rewrite lookup_insert in Hix0.
                    inversion Hix0; subst; clear Hix0.
                    assumption.
                }
                {
                    rewrite lookup_insert_ne in Hix0.
                    {
                        rewrite lookup_empty in Hix0.
                        inversion Hix0.
                    }
                    {
                        assumption.
                    }
                }
            }
            {
                reflexivity.
            }
        }
        {
            inversion H.
        }
    }
Qed.
Fail Next Obligation.

Definition pure_GroundTerm_try_match_BuiltinOrVar
    {Σ : Signature}
    :
    AppliedOperator' symbol builtin_value ->
    BuiltinOrVar ->
    option Valuation
:= fun t bov =>
match bov with
| bov_builtin b => None
| bov_variable x =>
    Some (<[x := (aoo_app _ _ t)]>∅)
end.

#[export]
Program Instance TryMatch__pure_GroundTerm__BoV
    {Σ : Signature}
:
    TryMatch (AppliedOperator' symbol builtin_value) BuiltinOrVar
:= {|
    try_match := pure_GroundTerm_try_match_BuiltinOrVar ;
    try_match_correct := _;
    try_match_complete := _;
|}.
Next Obligation.
    destruct b; unfold matchesb; simpl in *.
    { inversion H. }
    {
        inversion H; subst; clear H.
        apply bool_decide_eq_true.
        unfold Valuation in *.
        rewrite lookup_insert.
        reflexivity.
    }
Qed.
Next Obligation.
    unfold Valuation in *.
    destruct b; unfold matchesb in H; simpl in *.
    {
        inversion H.
    }
    {
        apply bool_decide_eq_true in H.
        exists (<[x:=aoo_app symbol builtin_value a]> ∅).
        split.
        {
            unfold vars_of; simpl.
            unfold Valuation in *.
            rewrite dom_insert_L.
            clear.
            ltac1:(set_solver).
        }
        split.
        {
            apply map_subseteq_spec.
            intros i x0 Hix0.
            destruct (decide (i = x)).
            {
                subst. 
                rewrite lookup_insert in Hix0.
                unfold Valuation in *.
                inversion Hix0; subst. clear Hix0.
                assumption.
            }
            {
                rewrite lookup_insert_ne in Hix0.
                {
                    rewrite lookup_empty in Hix0.
                    inversion Hix0.
                }
                {
                    ltac1:(congruence).
                }
            }
        }
        {
            reflexivity.
        }
    }
Qed.
Fail Next Obligation.

Set Typeclasses Debug.
#[export]
Program Instance TryMatch__builtin__AO'sB
    {Σ : Signature}
    {B : Type}
    {_VB : (VarsOf B variable) }
    {_V1 : VarsOf (AppliedOperator' symbol B) variable}
    :
    TryMatch builtin_value (AppliedOperator' symbol B)
:= {|
    try_match := fun _ _ => None ;
|}.
Fail Next Obligation.

#[export]
Instance TryMatch__GroundTerm__OpenTerm
    {Σ : Signature}
    {CΣ : ComputableSignature}
    :
    TryMatch GroundTerm OpenTerm
.
Proof.
    apply _.
Defined.

Arguments try_match : simpl never.