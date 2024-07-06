From Minuska Require Import
    prelude
    spec
    basic_properties
.


  Definition Valuation2_use_left
  {Σ : StaticModel}
  (og1 og2: option (TermOver builtin_value)): option (TermOver builtin_value) :=
  match og1, og2 with
  | None, None => None
  | Some g1, None => Some g1
  | None, Some g2 => Some g2
  | Some g1, Some g2 => Some g1
  end.

  Definition Valuation2_compatible_with
      {Σ : StaticModel}
      (ρ1 ρ2 : Valuation2) : bool
      := forallb (fun k => bool_decide (ρ1 !! k = ρ2 !! k)) (elements (dom ρ1 ∩ dom ρ2))
  .

Definition Valuation2_compatible_with_bound
    {Σ : StaticModel}
    (ρ1 ρ2 ρ : Valuation2)
    :
    ρ1 ⊆ ρ ->
    ρ2 ⊆ ρ ->
    Valuation2_compatible_with ρ1 ρ2 = true
.
Proof.
    intros H1 H2.
    unfold Valuation2_compatible_with.
    rewrite forallb_forall.
    intros x Hx.
    rewrite <- elem_of_list_In in Hx.
    rewrite elem_of_elements in Hx.
    rewrite elem_of_intersection in Hx.
    destruct Hx as [H1x H2x].
    unfold Valuation2 in *.
    rewrite elem_of_dom in H1x.
    rewrite elem_of_dom in H2x.
    destruct H1x as [y1 Hy1].
    destruct H2x as [y2 Hy2].
    rewrite bool_decide_eq_true.
    eapply lookup_weaken in Hy1 as Hy1'>[|apply H1].
    eapply lookup_weaken in Hy2 as Hy2'>[|apply H2].
    ltac1:(congruence).
Qed.

  Definition Valuation2_merge_with
      {Σ : StaticModel}
      (ρ1 ρ2 : Valuation2)
      : option Valuation2 :=
  if (Valuation2_compatible_with ρ1 ρ2)
  then
      Some (merge Valuation2_use_left ρ1 ρ2)
  else
      None
  .

Definition Valuation2_merge_list
    {Σ : StaticModel}
    (l : list Valuation2)
    : option Valuation2
:=
    foldr (fun ρ1 oρ2 =>
        ρ2 ← oρ2; Valuation2_merge_with ρ1 ρ2
     ) (Some ∅) l
.

Definition Valuation2_merge_olist
    {Σ : StaticModel}
    (l : list (option Valuation2))
    : option Valuation2
:=
    foldr (fun oρ1 oρ2 =>
        ρ1 ← oρ1; ρ2 ← oρ2; Valuation2_merge_with ρ1 ρ2
     ) (Some ∅) l
.



  Lemma Valuation2_merge_with_correct
      {Σ : StaticModel}
      (ρ1 ρ2 ρ : Valuation2):
      Valuation2_merge_with ρ1 ρ2 = Some ρ ->
      ρ1 ⊆ ρ /\
      ρ2 ⊆ ρ
  .
  Proof.
      unfold Valuation2 in *.
      unfold Valuation2_merge_with.
      unfold is_left.
      destruct ((Valuation2_compatible_with ρ1 ρ2)) eqn:Hcompat; intros H.
      {
          inversion H; subst; clear H.
          unfold Valuation2_compatible_with in Hcompat.
          unfold is_true in Hcompat.
          rewrite forallb_forall in Hcompat; cbn.
          ltac1:(setoid_rewrite <- elem_of_list_In in Hcompat).
          ltac1:(setoid_rewrite elem_of_elements in Hcompat).
          split; intros i;
              destruct (ρ1 !! i) eqn:Hρ1i;
              destruct (ρ2 !! i) eqn:Hρ2i;
              destruct (merge Valuation2_use_left ρ1 ρ2 !! i) eqn:Hmergei;
              simpl;
              try (exact I);
              ltac1:(rewrite lookup_merge in Hmergei);
              unfold diag_None in Hmergei;
              specialize (Hcompat i);
              ltac1:(rewrite Hρ1i in Hmergei);
              ltac1:(rewrite Hρ2i in Hmergei);
              unfold Valuation2_use_left in Hmergei;
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
          unfold Valuation2 in *.
          rewrite Hcompat in Hρ1i.
          rewrite Hρ1i in Hρ2i.
          ltac1:(congruence).
      }
      {
          inversion H.
      }
  Qed.


  Lemma merge_valuations_empty_r
    {Σ : StaticModel} x
  :
    Valuation2_merge_with x ∅ = Some x
  .
  Proof.
      unfold Valuation2_merge_with.
      ltac1:(case_match).
      {
          clear H.
          apply f_equal.
          rewrite <- merge_Some.
          intros i.
          unfold Valuation2_use_left.
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
          unfold Valuation2 in *.
          unfold Valuation2_compatible_with in H.
          rewrite <- not_true_iff_false in H.
          ltac1:(exfalso). apply H. clear H.
          rewrite forallb_forall.
          intros x0 Hx0.
          rewrite bool_decide_eq_true.
          rewrite <- elem_of_list_In in Hx0.
          rewrite elem_of_elements in Hx0.
          rewrite elem_of_intersection in Hx0.
          destruct Hx0 as [H1 H2].
          ltac1:(exfalso).
          ltac1:(rewrite dom_empty in H2).
          rewrite elem_of_empty in H2.
          inversion H2.
      }
  Qed.

  Lemma merge_valuations_empty_l
      {Σ : StaticModel} x:
      Valuation2_merge_with ∅ x = Some x
  .
  Proof.
      unfold Valuation2_merge_with.
      ltac1:(case_match).
      {
          clear H.
          apply f_equal.
          rewrite <- merge_Some.
          intros i.
          unfold Valuation2_use_left.
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
          unfold Valuation2 in *.
          unfold Valuation2_compatible_with in H.
          rewrite <- not_true_iff_false in H.
          ltac1:(exfalso). apply H. clear H.
          rewrite forallb_forall.
          intros x0 Hx0.
          rewrite bool_decide_eq_true.
          rewrite <- elem_of_list_In in Hx0.
          rewrite elem_of_elements in Hx0.
          rewrite elem_of_intersection in Hx0.
          destruct Hx0 as [H1 H2].
          ltac1:(exfalso).
          ltac1:(rewrite dom_empty in H1).
          rewrite elem_of_empty in H1.
          inversion H1.
      }
  Qed.

  Lemma merge_use_left_subseteq
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2):
    ρ1 ⊆ ρ2 ->
      merge Valuation2_use_left ρ1 ρ2 = ρ2
  .
  Proof.
      unfold subseteq. simpl.
      unfold Subseteq_Valuation2.
      unfold Valuation2 in *. simpl.
      unfold map_subseteq.
      unfold map_included.
      unfold map_relation.
      unfold option_relation.
      intros H.
      apply map_subseteq_po.
      {
          unfold Valuation2.
          rewrite map_subseteq_spec.
          intros i x Hix.
          rewrite lookup_merge in Hix.
          unfold diag_None in Hix.
          unfold Valuation2_use_left in Hix.
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
          unfold Valuation2.
          rewrite map_subseteq_spec.
          intros i x Hix.
          rewrite lookup_merge.
          unfold diag_None.
          unfold Valuation2_use_left.
          ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
          specialize (H i).
          rewrite H1 in H.
          rewrite H0 in H.
          subst.
          reflexivity.
      }
  Qed.

  Lemma merge_valuations_dom
    {Σ : StaticModel}
    (ρ1 ρ2 ρ : Valuation2):
    Valuation2_merge_with ρ1 ρ2 = Some ρ ->
    dom ρ = dom ρ1 ∪ dom ρ2
  .
  Proof.
      assert (Hm := Valuation2_merge_with_correct ρ1 ρ2 ρ).
      unfold Valuation2_merge_with in *.
      destruct ((Valuation2_compatible_with ρ1 ρ2)); simpl in *;
          intros H; inversion H; subst; clear H.
      apply leibniz_equiv.
      rewrite set_equiv_subseteq.
      split.
      {
          clear Hm.
          rewrite elem_of_subseteq.
          intros x Hx.
          unfold Valuation2 in *.
          rewrite elem_of_dom in Hx.
          rewrite elem_of_union.
          rewrite elem_of_dom.
          rewrite elem_of_dom.
          destruct Hx as [y Hy].
          rewrite lookup_merge in Hy.
          unfold diag_None, Valuation2_use_left in Hy.
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
          unfold Valuation2 in *.
          split; intros x Hx; rewrite elem_of_dom in Hx;
              destruct Hx as [y Hy]; rewrite elem_of_dom;
              exists y; eapply lookup_weaken>[apply Hy|];
              assumption.
      }
  Qed.

  Lemma Valuation2_merge_with_correct_2
      {Σ : StaticModel}
      (ρ1 ρ2 ρ : Valuation2):
      Valuation2_merge_with ρ1 ρ2 = Some ρ ->
      ∀ x g, ρ !! x = Some g ->
      (ρ1 !! x = Some g \/ ρ2 !! x = Some g)
  .
  Proof.
    intros.
    unfold Valuation2_merge_with in H.
    ltac1:(case_match); ltac1:(simplify_eq/=).
    ltac1:(rename H0 into H).
    ltac1:(rewrite lookup_merge in H).
    unfold diag_None in H.
    ltac1:(repeat (case_match; simpl in *; idtac; simplify_eq/=)).
    {
      left. assumption.
    }
    {
      left. assumption.
    }
    {
      right. assumption.
    }
  Qed.

#[global]
Instance option_Valuation2_vars_of
    {Σ : StaticModel}
    :
    VarsOf (option Valuation2) variable
:= {|
    vars_of := fun oρ => match oρ with None => ∅ | Some ρ => vars_of ρ end
|}.

Lemma Valuation2_merge_olist_vars_of
    {Σ : StaticModel}
    (l : list (option Valuation2))
    (ρ : Valuation2):
    Valuation2_merge_olist l = Some ρ ->
    vars_of ρ = vars_of l
.
Proof.
    unfold vars_of in *; simpl in *.
    revert ρ.
    induction l; simpl in *; intros ρ HH.
    {
        inversion HH; subst; clear HH.
        unfold vars_of; simpl.
        ltac1:(set_solver).
    }
    {
        rewrite bind_Some in HH.
        destruct HH as [ρ1 [HH1 HH2]].
        rewrite bind_Some in HH2.
        destruct HH2 as [ρ2 [HH2 HH3]].
        unfold vars_of; simpl.
        subst.
        specialize (IHl _ HH2).
        apply merge_valuations_dom in HH3.
        rewrite HH3. clear HH3.
        ltac1:(set_solver).
    }
Qed.




Lemma dom_merge_use_left
    {Σ : StaticModel}
    (ρ' ρ'' : Valuation2)
    :
    dom (merge Valuation2_use_left ρ' ρ'') = dom ρ'' ∪ dom ρ'
.
Proof.
    unfold Valuation2 in *.
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
            exists t0. assumption.
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
            exists t.
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
            exists t.
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
