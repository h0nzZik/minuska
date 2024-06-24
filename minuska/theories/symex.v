From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    minusl_syntax
    syntax_properties
    unification_interface
    symex_spec
.


Require Import Wellfounded.
From stdpp Require Import lexico well_founded.

Require Import Program.
From Coq Require Import Logic.Eqdep_dec.

From Equations Require Export Equations.

Module Implementation.

  Fixpoint toe_to_cpat
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
  :
    ((TermOver BuiltinOrVar)*(list SideCondition2))%type
  :=
  match t with
  | t_over e =>
      let x : variable := fresh avoid in
      (t_over (bov_variable x), [{|sc_left := (e_variable x); sc_right := e|}])
  | t_term s l =>
      let go' := (fix go' (avoid' : list variable) (ts : list (TermOver Expression2)) : ((list (TermOver BuiltinOrVar))*(list SideCondition2))%type :=
        match ts with
        | [] => ([], [])
        | t'::ts' =>
          let tmp := toe_to_cpat avoid' t' in
          let rest := go' (avoid' ++ elements (vars_of (tmp.2))) ts' in
          (tmp.1::rest.1, (tmp.2 ++ rest.2))
        end
      ) in
      let l' := go' avoid l in
      (t_term s (fst l'), snd l')
  end
  .

  Fixpoint toe_to_cpat_list
    {Σ : StaticModel}
    (avoid : list variable)
    (l : list (TermOver Expression2))
  : 
    ((list (TermOver BuiltinOrVar))*(list SideCondition2))%type
  :=
    match l with
    | [] => ([], [])
    | t'::ts' =>
      let tmp := toe_to_cpat avoid t' in
      let rest := toe_to_cpat_list (avoid ++ elements (vars_of (tmp.2))) ts' in
      (tmp.1::rest.1, (tmp.2 ++ rest.2))
    end
  .

  Lemma toe_to_cpat_list_equiv
    {Σ : StaticModel}
    (avoid : list variable)
    (l : list (TermOver Expression2))
    (s : symbol)
  :
    toe_to_cpat avoid (t_term s l) = ((t_term s ((toe_to_cpat_list avoid l).1)), ((toe_to_cpat_list avoid l).2))
  .    
  Proof.
    simpl.
    revert s avoid.
    induction l; intros s avoid.
    {
      simpl. reflexivity.
    }
    {
      simpl in *.
      specialize (IHl s (avoid ++ elements (vars_of (toe_to_cpat avoid a).2))).
      inversion IHl; subst; clear IHl.
      repeat f_equal.
    }
  Qed.

  Lemma length_toe_to_cpat_list
    {Σ : StaticModel}
    (avoid : list variable)
    (l : list (TermOver Expression2))
    :
    length (toe_to_cpat_list avoid l).1 = length l
  .
  Proof.
    revert avoid.
    induction l; intros avoid; simpl in *.
    { reflexivity. }
    {
      rewrite IHl. reflexivity.
    }
  Qed.

  Lemma elem_of_list_singleton_inv
    {A : Type}
    (x y : A)
    :
    x ∈ [y] -> x = y
  .
  Proof.
    intros H.
    rewrite elem_of_list_singleton in H.
    exact H.
  Qed.


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

  Lemma toe_to_cpat_good_side
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
  :
    vars_of (toe_to_cpat avoid t).2 ⊆ vars_of (toe_to_cpat avoid t).1 ∪ vars_of t
  .
  Proof.
    revert avoid.
    induction t; intros avoid.
    {
      simpl in *.
      unfold vars_of in *; simpl in *.
      unfold vars_of in *; simpl in *.
      unfold vars_of; simpl.
      ltac1:(set_solver).
    }
    {
      rewrite Forall_forall in H.
      unfold TermOver in *.
      rewrite vars_of_t_term_e.
      simpl in *.
      rewrite elem_of_subseteq.
      intros x Hx.
      unfold vars_of in Hx; simpl in Hx.
      rewrite elem_of_union_list in Hx.
      destruct Hx as [X [H1X H2X]].
      rewrite elem_of_list_fmap in H1X.
      destruct H1X as [y [H1y H2y]].
      subst X.
      unfold TermOver in *.
      rewrite vars_of_t_term.
      rewrite elem_of_union.
      rewrite elem_of_union_list.

      clear s.
      revert avoid x y H2X H2y H.
      induction l; intros avoid x y H2X H2y H.
      {
        simpl in *.
        rewrite elem_of_nil in H2y.
        destruct H2y.
      }
      {
        unfold TermOver in *.
        simpl in *.
        rewrite elem_of_app in H2y.
        destruct H2y as [H2y|H2y].
        {
          assert (Ha := H a).
          ltac1:(ospecialize (Ha _)).
          {
            rewrite elem_of_cons.
            left.
            reflexivity.
          }
          specialize (Ha avoid).
          rewrite elem_of_subseteq in Ha.
          specialize (Ha x).
          unfold vars_of in Ha at 1; simpl in Ha.
          rewrite elem_of_union_list in Ha.
          ltac1:(ospecialize (Ha _)).
          {
            exists (vars_of y).
            rewrite elem_of_list_fmap.
            split>[|exact H2X].
            exists y.
            split>[reflexivity|].
            exact H2y.
          }
          rewrite elem_of_union in Ha.
          destruct Ha as [Ha|Ha].
          {
            left.
            exists (vars_of (toe_to_cpat avoid a).1).
            rewrite elem_of_cons.
            split>[|exact Ha].
            left.
            reflexivity.
          }
          {
            right.
            rewrite elem_of_union.
            left.
            exact Ha.
          }
        }
        {
          specialize (IHl (avoid ++ elements (vars_of ((toe_to_cpat avoid a).2)))).
          specialize (IHl x y H2X).
          specialize (IHl H2y).
          ltac1:(ospecialize (IHl _)).
          {
            clear -H.
            intros.
            specialize (H x).
            rewrite elem_of_cons in H.
            specialize (H (or_intror H0)).
            apply H.
          }
          destruct IHl as [IHl|IHl].
          {
            destruct IHl as [Y [H1Y H2Y]].
            left.
            exists Y.
            split>[|apply H2Y].
            rewrite elem_of_cons.
            right.
            apply H1Y.
          }
          {
            right.
            rewrite elem_of_union.
            right.
            apply IHl.
          }
        }
      }
    }
  Qed.

  Lemma toe_to_cpat_list_good_side
    {Σ : StaticModel}
    (avoid : list variable)
    (l : list (TermOver Expression2))
  :
    vars_of (toe_to_cpat_list avoid l).2 ⊆ vars_of (toe_to_cpat_list avoid l).1 ∪ vars_of l
  .
  Proof.
    revert avoid.
    induction l; intros avoid; simpl in *.
    {
      unfold vars_of; simpl.
      ltac1:(set_solver).
    }
    {
      unfold vars_of; simpl.
      repeat (rewrite fmap_app).
      repeat (rewrite union_list_app).
      rewrite union_subseteq.
      split.
      {
        assert (Htmp := toe_to_cpat_good_side avoid a).
        unfold vars_of in Htmp at 1; simpl in Htmp.
        ltac1:(set_solver).
      }
      {
        specialize (IHl (avoid ++ elements (⋃ (vars_of <$> (toe_to_cpat avoid a).2))) ).
        ltac1:(set_solver).
      }
    }
  Qed.

  Lemma toe_to_cpat_good_side_2
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
  :
    vars_of (toe_to_cpat avoid t).1 ⊆ vars_of (toe_to_cpat avoid t).2
  .
  Proof.
    revert avoid.
    induction t; intros avoid; simpl in *.
    {
      unfold vars_of; simpl.
      unfold vars_of; simpl.
      unfold vars_of at 1; simpl.
      ltac1:(set_solver).
    }
    {
      unfold vars_of; simpl.
      clear s.
      revert avoid.
      induction l; intros avoid; simpl in *.
      {
        ltac1:(set_solver).
      }
      {
        rewrite Forall_cons in H.
        destruct H as [H1 H2].
        specialize (IHl H2). clear H2.
        rewrite union_subseteq.
        split.
        {
          rewrite fmap_app.
          rewrite union_list_app.
          ltac1:(set_solver).
        }
        {
          rewrite fmap_app.
          rewrite union_list_app.
          ltac1:(set_solver).
        }
      }
    }
  Qed.

  Lemma toe_to_cpat_list_good_side_2
    {Σ : StaticModel}
    (avoid : list variable)
    (l : list (TermOver Expression2))
  :
    vars_of (toe_to_cpat_list avoid l).1 ⊆ vars_of (toe_to_cpat_list avoid l).2
  .
  Proof.
    revert avoid.
    induction l; intros avoid; simpl in *.
    {
      unfold vars_of in *; simpl in *.
      ltac1:(set_solver).
    }
    {
      unfold vars_of; simpl.
      rewrite union_subseteq.
      split.
      {
        assert (Htmp := toe_to_cpat_good_side_2 avoid a).
        rewrite fmap_app.
        rewrite union_list_app.
        ltac1:(set_solver).
      }
      {
        rewrite fmap_app.
        rewrite union_list_app.
        ltac1:(set_solver).
      }
    }
  Qed.

  (*
  Lemma toe_to_cpat_list_good_side
    {Σ : StaticModel}
    (avoid : list variable)
    (l : list (TermOver Expression2))
  :
    vars_of (toe_to_cpat_list avoid l).2 ⊆ vars_of (toe_to_cpat_list avoid l).1 ∪ vars_of l
  .
  Proof.
    revert avoid.
    induction l; intros avoid; simpl in *.
    {
      unfold vars_of; simpl. ltac1:(set_solver).
    }
    {
      unfold vars_of; simpl.
      repeat (rewrite fmap_app).
      repeat (rewrite union_list_app).
      specialize (IHl (avoid ++ elements (⋃ (vars_of <$> (toe_to_cpat avoid a).2)))).
      assert (Hbase := toe_to_cpat_good_side avoid a).
      ltac1:(set_solver).
    }
  Qed.*)

  Lemma toe_to_cpat_avoid
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
  :
    forall x,
      x ∈ vars_of (toe_to_cpat avoid t).1 ->
      x ∉ avoid
  .
  Proof.
    revert avoid.
    induction t; intros avoid x Htoe.
    {
      unfold vars_of in Htoe; simpl in Htoe.
      unfold vars_of in Htoe; simpl in Htoe.
      rewrite elem_of_singleton in Htoe.
      subst.
      apply infinite_is_fresh.
    }
    {
      rewrite Forall_forall in H.
      simpl in Htoe.
      unfold TermOver in *.
      rewrite vars_of_t_term in Htoe.
      rewrite elem_of_union_list in Htoe.
      destruct Htoe as [X [H1X H2X]].
      rewrite elem_of_list_fmap in H1X.
      destruct H1X as [y [H1y H2y]].
      subst X.

      clear s.
      revert x y avoid H2y H2X H.
      induction l; intros x y avoid H2y H2X H.
      {
        simpl in H2y.
        rewrite elem_of_nil in H2y.
        destruct H2y.
      }
      {
        simpl in *.
        rewrite elem_of_cons in H2y.
        destruct H2y as [H2y|H2y].
        {
          subst.
          apply (H a).
          {
            rewrite elem_of_cons.
            left.
            reflexivity.
          }
          {
            apply H2X.
          }
        }
        {
          specialize (IHl _ _ _ H2y H2X).
          ltac1:(ospecialize (IHl _)).
          {
            intros.
            simpl in *.
            apply (H x0).
            {
              rewrite elem_of_cons.
              right.
              assumption.
            }
            {
              apply H1.
            }
          }
          clear - IHl.
          ltac1:(set_solver).
        }
      }
    }
  Qed.


  Lemma toe_to_cpat_list_avoid
    {Σ : StaticModel}
    (avoid : list variable)
    (l : list (TermOver Expression2))
  :
    forall x,
      x ∈ vars_of (toe_to_cpat_list avoid l).1 ->
      x ∉ avoid
  .
  Proof.
    revert avoid.
    induction l; intros avoid x Hx; simpl in *.
    {
      unfold vars_of in Hx; simpl in Hx.
      ltac1:(set_solver).
    }
    {
      unfold vars_of in Hx; simpl in Hx.
      rewrite elem_of_union in Hx.
      destruct Hx as [Hx|Hx].
      {
        apply toe_to_cpat_avoid in Hx.
        exact Hx.
      }
      {
        specialize (IHl _ _ Hx).
        ltac1:(set_solver).
      }
    }
  Qed.
  
  Lemma toe_to_cpat_correct_1
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
    (g : TermOver builtin_value)
  :
    elements (vars_of t) ⊆ avoid ->
    forall (ρ' : Valuation2),
      satisfies ρ' g t ->
      ({ ρ : Valuation2 &
        (
          (satisfies ρ g ((toe_to_cpat avoid t).1))
          *
          (satisfies ρ tt ((toe_to_cpat avoid t).2))
          (* *
          (vars_of ρ ⊆ vars_of ((toe_to_cpat avoid t).1) ∪ vars_of ((toe_to_cpat avoid t).2)) *)
          *
          ((filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ avoid) ρ') = filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ avoid) ρ)
        )%type
      })
  .
  Proof.
    revert g avoid.
    ltac1:(induction t using TermOver_rect; intros g avoid Havoid ρ' H2ρ').
    {
      inversion H2ρ'; clear H2ρ'.
      simpl.
      unfold satisfies; simpl.
      exists (<[(fresh avoid) := g]>((filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ avoid) ρ'))).
      split.
      split.
      (* split. *)
      {
        ltac1:(simp sat2B).
        unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar.
        unfold Valuation2 in *.
        apply lookup_insert.
      }
      {
        intros x Hx.
        apply elem_of_list_singleton_inv in Hx.
        subst x.
        unfold satisfies; simpl.
        unfold Valuation2 in *.
        ltac1:(rewrite lookup_insert).
        unfold isSome.
        split>[|reflexivity].
        {
          apply Expression2_evalute_strip in H0.
          symmetry.
          eapply Expression2_evaluate_extensive_Some>[|apply H0].
          ltac1:(rewrite map_subseteq_spec).
          intros i x Hix.
          ltac1:(rewrite map_lookup_filter in Hix).
          rewrite bind_Some in Hix.
          destruct Hix as [x0 [H1x0 H2x0]].
          rewrite bind_Some in H2x0.
          simpl in H2x0.
          destruct H2x0 as [x1 [H1x1 H2x1]].
          ltac1:(simplify_option_eq).
          rewrite lookup_insert_ne.
          {
            rewrite map_lookup_filter.
            rewrite bind_Some.
            exists x.
            split>[exact H1x0|].
            rewrite bind_Some.
            simpl.
            unfold vars_of in Havoid; simpl in Havoid.
            ltac1:(rewrite elem_of_subseteq in Havoid).
            specialize (Havoid i).
            rewrite elem_of_elements in Havoid.
            specialize (Havoid x1).
            exists Havoid.
            split>[|reflexivity].
            ltac1:(simplify_option_eq).
            apply f_equal.
            apply proof_irrelevance.
            ltac1:(contradiction H2).
            ltac1:(contradiction H1).
          }
          {
            intros HContra.
            subst i.
            unfold vars_of in Havoid; simpl in Havoid.
            assert (fresh avoid ∉ avoid) by (apply infinite_is_fresh).
            ltac1:(set_solver).
          }
        }
      }
      (*
      {
        unfold Valuation2 in *.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        ltac1:(rewrite dom_insert).
        rewrite elem_of_subseteq.
        intros x Hx.
        rewrite elem_of_union in Hx.
        destruct Hx.
        {
          ltac1:(set_solver).
        }
        {
          rewrite elem_of_dom in H.
          destruct H as [y Hy].
          unfold Valuation2,TermOver in *.
          rewrite map_lookup_filter in Hy.
          ltac1:(simplify_option_eq).
          apply Expression2_evaluate_Some_enough in H0.
          unfold vars_of in Havoid; simpl in Havoid.
          unfold vars_of in Havoid; simpl in Havoid.
          ltac1:(set_solver).
        }
      }
      *)
      {
        unfold Valuation2 in *.
        apply map_eq.
        intros i.
        repeat (rewrite map_lookup_filter).
        ltac1:(simplify_option_eq).
        destruct (ρ' !! i) eqn:Hρ'i; simpl in *;
          ltac1:(simplify_option_eq).
        {
          symmetry.
          repeat (rewrite bind_Some).
          exists t.
          split>[|reflexivity].
          rewrite lookup_insert_ne.
          {
            rewrite map_lookup_filter.
            rewrite Hρ'i.
            simpl.
            ltac1:(simplify_option_eq).
            reflexivity.
          }
          {
            intros HContra. subst i.
            assert (fresh avoid ∉ avoid) by (apply infinite_is_fresh).
            ltac1:(contradiction).
          }
        }
        {
          symmetry.
          rewrite bind_None.
          left.
          rewrite lookup_insert_ne.
          {
            rewrite map_lookup_filter.
            rewrite Hρ'i.
            simpl.
            ltac1:(simplify_option_eq).
            reflexivity.
          }
          {
            intros HContra. subst i.
            assert (fresh avoid ∉ avoid) by (apply infinite_is_fresh).
            ltac1:(contradiction).
          }
        }
        {
          symmetry.
          destruct (decide (fresh avoid = i)).
          {
            subst.
            rewrite lookup_insert.
            simpl.
            symmetry.
            rewrite bind_None.
            destruct (ρ' !! fresh avoid); simpl in *.
            {
              right. exists t. split; reflexivity.
            }
            {
              left. reflexivity.
            }
          }
          {
            rewrite lookup_insert_ne>[|assumption].
            rewrite map_lookup_filter.
            ltac1:(simplify_option_eq).
            destruct (ρ' !! i) eqn:Heq; simpl in *;
              reflexivity.
          }
        }
      }
    }
    {
      destruct g.
      { inversion H2ρ'. }
      unfold satisfies in H2ρ'; simpl in H2ρ'.
      ltac1:(simp sat2E in H2ρ').
      destruct H2ρ' as [HH1 [HH2 HH3]].
      subst b.
      rewrite toe_to_cpat_list_equiv.
      revert ρ' avoid X l0 HH2 HH3 Havoid.
      induction l; intros ρ' avoid X l0 HH2 HH3 Havoid.
      {
        simpl in *.
        apply nil_length_inv in HH2.
        subst l0.
        clear HH3.
        exists ρ'.
        (*exists ∅.*)
        split.
        {
          ltac1:(simp sat2B).
          (repeat split).
          {
            clear.
            ltac1:(set_solver).
          }
          {
            rewrite elem_of_nil in H.
            inversion H.
          }
          {
            rewrite elem_of_nil in H.
            inversion H.
          }
        }
        {
          reflexivity.
        }
      }
      {
        unfold Valuation2 in *.
        unfold TermOver in *.
        destruct l0; simpl in *.
        {
          ltac1:(lia).
        }
        (*++ elements (vars_of ((toe_to_cpat avoid a).2)) *)
        rewrite vars_of_t_term_e in Havoid.
        rewrite fmap_cons in Havoid.
        rewrite union_list_cons in Havoid.
        rewrite vars_of_t_term_e in IHl.
        (* specialize (IHl ltac:(set_solver)). *)
        remember (filter (fun kv : (variable*(TermOver builtin_value))%type => kv.1 ∈ avoid) ρ') as ρ'2. 
        specialize (IHl ρ').
        specialize (IHl (avoid ++ elements (vars_of ((toe_to_cpat avoid a).2)))).
        ltac1:(ospecialize (IHl _ l0)).
        {
          clear IHl.
          intros.
          apply X.
          {
            rewrite elem_of_cons.
            right. assumption.
          }
          {
            assumption.
          }
          {
            assumption.
          }
        }
        ltac1:(specialize (IHl ltac:(lia))).
        simpl in *.
        ltac1:(ospecialize (IHl _)).
        {
          clear IHl X.
          intros.
          eapply HH3 with (i := (S i)).
          simpl.
          assumption.
          simpl.
          assumption.
        }
        ltac1:(ospecialize (IHl _)).
        {
          clear IHl.
          ltac1:(set_solver).
        }
        destruct IHl as [ρ3 [[H1ρ3 H2ρ3] H3ρ3]].
        assert (Xa := X a).
        ltac1:(ospecialize (Xa _)).
        {
          rewrite elem_of_cons.
          left.
          reflexivity.
        }
        
        assert (HH3a := HH3 0 t a erefl erefl).
        apply TermOverExpression2_satisfies_strip in HH3a as HH3a'.
        specialize (Xa t (avoid) ltac:(set_solver)).
        specialize (Xa _ HH3a).
        destruct Xa as [ρ4 [[H1ρ4 H2ρ4] H3ρ4]].
        
        (* FIXME I have no idea what to write here*)
        remember (Valuation2_merge_with
          (filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid ++ elements ((vars_of (toe_to_cpat_list (avoid ++ elements (vars_of ((toe_to_cpat avoid a).2))) l).1 ∪ vars_of (toe_to_cpat_list (avoid ++ elements (vars_of ((toe_to_cpat avoid a).2))) l).2))) ρ3)
          (filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid ++ elements ((vars_of (toe_to_cpat avoid a).1 ∪ vars_of (toe_to_cpat avoid a).2))) ρ4)) as oρm.
        
        (*
        remember (
          Valuation2_merge_with ρ4 ρ3
        ) as oρm.
        *)
        destruct oρm.
        {
          symmetry in Heqoρm.
          apply Valuation2_merge_with_correct in Heqoρm as Hcor.
          destruct Hcor as [Hcor1 Hcor2].
          
          exists v.
          unfold satisfies at 1; simpl.
          ltac1:(simp sat2B).
          split.
          split.
          split.
          { reflexivity. }
          split.
          {
            simpl.
            ltac1:(rewrite length_toe_to_cpat_list).
            apply HH2.
          }          
          {
            intros.
            destruct i; simpl in *.
            {
              ltac1:(simplify_eq/=).
              apply TermOverBoV_satisfies_strip in H1ρ4.
              eapply TermOverBoV_satisfies_extensive>[|apply H1ρ4].
              ltac1:(rewrite map_subseteq_spec).
              intros i x Hix.
              ltac1:(rewrite map_lookup_filter in Hix).
              rewrite bind_Some in Hix.
              destruct Hix as [x0 [H1x0 H2x0]].
              rewrite bind_Some in H2x0.
              destruct H2x0 as [x1 [H1x1 H2x1]].
              simpl in *.
              ltac1:(simplify_eq/=).
              ltac1:(rewrite map_subseteq_spec in Hcor2).
              specialize (Hcor2 i x).
              ltac1:(ospecialize (Hcor2 _)).
              {
                clear Hcor2.
                ltac1:(rewrite map_lookup_filter).
                rewrite bind_Some.
                exists x.
                split>[apply H1x0|].
                rewrite bind_Some.
                simpl.
                ltac1:(simplify_option_eq).
                {
                  exists H1.
                  (repeat split).
                }
                {
                  ltac1:(contradiction).
                }
                {
                  ltac1:(exfalso; set_solver).
                }
              }
              exact Hcor2.
            }
            {
              unfold satisfies in H1ρ3; simpl in H1ρ3.
              ltac1:(simp sat2B in H1ρ3).
              destruct H1ρ3 as [H11ρ3 [H12ρ3 H13ρ3]].
              specialize (H13ρ3 _ _ _ pf1 pf2).
              apply TermOverBoV_satisfies_strip in H13ρ3.
              eapply TermOverBoV_satisfies_extensive>[|apply H13ρ3].
              clear - Hcor1 pf1.
              ltac1:(rewrite map_subseteq_spec).
              ltac1:(rewrite map_subseteq_spec in Hcor1).
              intros j x Hjx.
              specialize (Hcor1 j x).
              ltac1:(rewrite map_lookup_filter in Hjx).
              rewrite bind_Some in Hjx.
              destruct Hjx as [x0 [H1x0 H2x0]].
              rewrite bind_Some in H2x0.
              simpl in *.
              destruct H2x0 as [x1 [H1x1 H2x1]].
              ltac1:(simplify_option_eq).
              apply Hcor1. clear Hcor1.
              rewrite map_lookup_filter.
              rewrite bind_Some.
              exists x.
              split>[assumption|].
              simpl.
              rewrite bind_Some.
              simpl.
              ltac1:(unshelve(eexists)).
              {
                apply take_drop_middle in pf1.
                ltac1:(rewrite <- pf1).
                unfold vars_of; simpl.
                rewrite fmap_app.
                rewrite union_list_app.
                rewrite fmap_cons.
                rewrite union_list_cons.
                ltac1:(set_solver).
              }
              {
                ltac1:(simplify_option_eq).
                split>[|reflexivity].
                ltac1:(apply f_equal).
                apply proof_irrelevance.
                ltac1:(contradiction).
                ltac1:(exfalso).

                apply take_drop_middle in pf1.
                ltac1:(rewrite <- pf1 in H0).
                unfold vars_of in H0; simpl in H0.
                rewrite fmap_app in H0.
                rewrite union_list_app in H0.
                rewrite fmap_cons in H0.
                rewrite union_list_cons in H0.
                ltac1:(set_solver).
              }
            }
          }
          {
            unfold satisfies; simpl.
            intros c Hc.
            rewrite elem_of_app in Hc.
            destruct (decide (c ∈ (toe_to_cpat avoid a).2)).
            {
              clear Hc.
              unfold satisfies in H2ρ4; simpl in H2ρ4.
              specialize (H2ρ4 c ltac:(assumption)).


              apply SideCondition_satisfies_strip in H2ρ4.
              eapply SideCondition_satisfies_extensive>[|apply H2ρ4].
              ltac1:(rewrite map_subseteq_spec).
              intros i x Hix.
              ltac1:(rewrite map_lookup_filter in Hix).
              rewrite bind_Some in Hix.
              destruct Hix as [x0 [H1x0 H2x0]].
              rewrite bind_Some in H2x0.
              destruct H2x0 as [x1 [H1x1 H2x1]].
              simpl in *.
              ltac1:(simplify_eq/=).
              ltac1:(rewrite map_subseteq_spec in Hcor2).
              specialize (Hcor2 i x).
              ltac1:(ospecialize (Hcor2 _)).
              {
                clear Hcor2.
                ltac1:(rewrite map_lookup_filter).
                rewrite bind_Some.
                exists x.
                split>[apply H1x0|].
                rewrite bind_Some.
                simpl.
                ltac1:(simplify_option_eq).
                {
                  exists H1.
                  (repeat split).
                }
                {
                  ltac1:(contradiction).
                }
                {
                  ltac1:(exfalso).
                  rewrite elem_of_list_lookup in e.
                  destruct e as [i0 Hi0].
                  apply take_drop_middle in Hi0.
                  apply H0. clear H0.
                  rewrite <- Hi0.
                  rewrite elem_of_app.
                  right.
                  rewrite elem_of_elements.
                  rewrite elem_of_union.
                  right.
                  unfold vars_of; simpl.
                  rewrite fmap_app.
                  rewrite union_list_app.
                  rewrite fmap_cons.
                  rewrite union_list_cons.
                  clear -x1.
                  ltac1:(set_solver).
                }
              }
              exact Hcor2.
            }
            {
              assert (c ∈ (toe_to_cpat_list (avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) l).2).
              {
                ltac1:(set_solver).
              }
              unfold satisfies in H2ρ3; simpl in H2ρ3.
              specialize (H2ρ3 c ltac:(assumption)).


              apply SideCondition_satisfies_strip in H2ρ3.
              eapply SideCondition_satisfies_extensive>[|apply H2ρ3].
              ltac1:(rewrite map_subseteq_spec).
              intros i x Hix.
              ltac1:(rewrite map_lookup_filter in Hix).
              rewrite bind_Some in Hix.
              destruct Hix as [x0 [H1x0 H2x0]].
              rewrite bind_Some in H2x0.
              destruct H2x0 as [x1 [H1x1 H2x1]].
              simpl in *.
              ltac1:(simplify_eq/=).
              ltac1:(rewrite map_subseteq_spec in Hcor1).
              specialize (Hcor1 i x).
              ltac1:(ospecialize (Hcor1 _)).
              {
                clear Hcor1.
                ltac1:(rewrite map_lookup_filter).
                rewrite bind_Some.
                exists x.
                split>[apply H1x0|].
                rewrite bind_Some.
                simpl.
                ltac1:(simplify_option_eq).
                {
                  exists H2.
                  (repeat split).
                }
                {
                  ltac1:(contradiction).
                }
                {
                  ltac1:(exfalso).
                  ltac1:(rewrite elem_of_list_lookup in H).
                  destruct H as [i0 Hi0].
                  apply take_drop_middle in Hi0.
                  apply H1. clear H1.
                  rewrite <- Hi0.
                  rewrite elem_of_app.
                  right.
                  rewrite elem_of_elements.
                  rewrite elem_of_union.
                  right.
                  unfold vars_of; simpl.
                  rewrite fmap_app.
                  rewrite union_list_app.
                  rewrite fmap_cons.
                  rewrite union_list_cons.
                  clear -x1.
                  ltac1:(set_solver).
                }
              }
              exact Hcor1.
            }
          }
          {
            assert(Helper1: filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid) ρ' =
              filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid) ρ3).
            {
              clear -H3ρ3.
              apply map_eq.
              intros i.
              rewrite map_lookup_filter.
              rewrite map_lookup_filter.
              destruct (ρ' !! i) eqn:Heq1, (ρ3 !! i) eqn:Heq2;
                simpl in *; ltac1:(simplify_option_eq; try congruence).
              {
                assert (Htmp: filter
                  (λ kv : variable * TermOver' builtin_value,
                  kv.1 ∈ avoid ++ elements (vars_of (toe_to_cpat avoid a).2))
                  ρ' !! i = Some t).
                {
                  rewrite map_lookup_filter.
                  rewrite bind_Some.
                  exists t.
                  split>[assumption|].
                  ltac1:(simplify_option_eq).
                  reflexivity.
                  ltac1:(set_solver).
                }
                rewrite H3ρ3 in Htmp.
                rewrite map_lookup_filter in Htmp.
                rewrite bind_Some in Htmp.
                destruct Htmp as [x [H1x H2x]].
                rewrite bind_Some in H2x.
                destruct H2x as [x0 [H1x0 H2x0]].
                simpl in *.
                ltac1:(simplify_option_eq).
                reflexivity.
              }
              {
                assert (Htmp: filter
                  (λ kv : variable * TermOver' builtin_value,
                  kv.1 ∈ avoid ++ elements (vars_of (toe_to_cpat avoid a).2))
                  ρ' !! i = Some t).
                {
                  rewrite map_lookup_filter.
                  rewrite bind_Some.
                  exists t.
                  split>[assumption|].
                  ltac1:(simplify_option_eq).
                  reflexivity.
                  ltac1:(set_solver).
                }
                rewrite H3ρ3 in Htmp.
                rewrite map_lookup_filter in Htmp.
                rewrite bind_Some in Htmp.
                destruct Htmp as [x [H1x H2x]].
                ltac1:(simplify_eq/=).
              }
              {
                assert (Htmp: filter
                  (λ kv : variable * TermOver' builtin_value,
                  kv.1 ∈ avoid ++ elements (vars_of (toe_to_cpat avoid a).2))
                  ρ3 !! i = Some t).
                {
                  rewrite map_lookup_filter.
                  rewrite bind_Some.
                  exists t.
                  split>[assumption|].
                  ltac1:(simplify_option_eq).
                  reflexivity.
                  ltac1:(set_solver).
                }
                rewrite <- H3ρ3 in Htmp.
                rewrite map_lookup_filter in Htmp.
                rewrite bind_Some in Htmp.
                destruct Htmp as [x [H1x H2x]].
                ltac1:(simplify_eq/=).
              }
            }

            (* FIXME this is too weak. *)
            assert (Hmdom := merge_valuations_dom _ _ _ Heqoρm).
            apply map_subseteq_po.
            {
              rewrite map_subseteq_spec.
              intros x g.
              rewrite map_lookup_filter.
              rewrite map_lookup_filter.
              intros HHxg.
              rewrite bind_Some in HHxg.
              destruct HHxg as [y [H1y H2y]].
              rewrite bind_Some.
              exists y.
              rewrite bind_Some in H2y.
              destruct H2y as [pf1 [H1pf1 H2pf1]].
              simpl in *.
              inversion H2pf1; subst; clear H2pf1.
              assert (Htmp0 : filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid) ρ' !! x = Some g).
              {
                rewrite map_lookup_filter.
                rewrite bind_Some.
                exists g.
                split>[apply H1y|].
                rewrite bind_Some.
                simpl.
                exists pf1.
                split>[assumption|reflexivity].
              }
              rewrite Helper1 in Htmp0.
              ltac1:(rewrite map_subseteq_spec in Hcor1).
              specialize (Hcor1 x g).
              ltac1:(ospecialize (Hcor1 _)).
              {
                rewrite map_lookup_filter.
                rewrite bind_Some.
                
                rewrite map_lookup_filter in Htmp0.
                rewrite bind_Some in Htmp0.
                destruct Htmp0 as [g0 [H1g0 H2g0]].
                exists g0. simpl in *.
                split>[apply H1g0|].
                rewrite bind_Some.
                ltac1:(unshelve(eexists)).
                {
                  rewrite elem_of_app.
                  left.
                  assumption.
                }
                assert(g0 = g).
                {
                  ltac1:(simplify_option_eq).
                  reflexivity.
                }
                subst g0.
                split>[|reflexivity].
                ltac1:(simplify_option_eq).
                {
                  apply f_equal.
                  apply proof_irrelevance.
                }
                {
                  ltac1:(contradiction).
                }
                {
                  ltac1:(exfalso; set_solver).
                }
              }
              split>[exact Hcor1|].
              ltac1:(simplify_option_eq).
              reflexivity.
            }
            {
              rewrite map_subseteq_spec.
              intros x g Hxg.
              rewrite map_lookup_filter in Hxg.
              rewrite map_lookup_filter.
              rewrite bind_Some in Hxg.
              rewrite bind_Some.
              destruct Hxg as [g' [H1g' H2g']].
              assert (g = g').
              {
                ltac1:(simplify_option_eq).
                reflexivity.
              }
              subst g'.
              rewrite bind_Some in H2g'.
              simpl in H2g'.
              destruct H2g' as [Hxavoid _].
              clear H2g'.
              assert (Hxdomv : x ∈ dom v).
              {
                ltac1:(rewrite elem_of_dom).
                exists g. exact H1g'. 
              }
              rewrite Hmdom in Hxdomv.
              clear Hmdom.
              rewrite elem_of_union in Hxdomv.
              destruct Hxdomv as [Hxdomv|Hxdomv].
              {
                ltac1:(rewrite elem_of_dom in Hxdomv).
                destruct Hxdomv as [g' Hg'].
                rewrite map_lookup_filter in Hg'.
                rewrite bind_Some in Hg'.
                destruct Hg' as [g'' [H1g'' H2g'']].
                simpl in H2g''.
                rewrite bind_Some in H2g''.
                destruct H2g'' as [pf1 [H1pf1 H2pf1]].
                inversion H2pf1; subst g''; clear H2pf1.
                clear H1pf1. clear pf1.

                assert (g = g').
                {
                  
                }
                rewrite elem_of_app in pf1.
                destruct pf1 as [pf1|pf1].
                {
                  admit.
                }
                {
                  simpl.
                }
              }
              {

              }

            }
            clear - H3ρ4 H3ρ3 Hcor1 Hcor2 Hmdom.
            apply map_eq.
            intros i.
            rewrite map_lookup_filter.
            rewrite map_lookup_filter.
            destruct (ρ' !! i) eqn:Hρ'i, (v !! i) eqn:Hvi;
              simpl in *; ltac1:(simplify_option_eq; try congruence).
            {
              apply f_equal.
              assert (Htmp1: filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid) ρ' !! i = Some t).
              {
                rewrite map_lookup_filter.
                rewrite Hρ'i. simpl.
                ltac1:(simplify_option_eq).
                reflexivity.
              }

              assert (Htmp2: filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) ρ' !! i = Some t).
              {
                rewrite map_lookup_filter.
                rewrite Hρ'i. simpl.
                ltac1:(simplify_option_eq).
                reflexivity.
                ltac1:(set_solver).
              }
              
            }
            ltac1:(congruence).
          }
        }
        {
          ltac1:(exfalso).
          unfold Valuation2_merge_with in Heqoρm.
          ltac1:(case_match; simplify_eq/=).
          clear Heqoρm.
          unfold Valuation2_compatible_with in H.
          rewrite <- not_true_iff_false in H.
          apply H. clear H.
          rewrite forallb_forall.
          intros x Hx.
          rewrite <- elem_of_list_In in Hx.
          rewrite elem_of_elements in Hx.
          rewrite elem_of_intersection in Hx.
          destruct Hx as [H1x H2x].
          unfold TermOver in *.
          ltac1:(rewrite elem_of_dom in H1x).
          ltac1:(rewrite elem_of_dom in H2x).
          destruct H1x as [y1 Hy1].
          destruct H2x as [y2 Hy2].
          ltac1:(rewrite Hy1).
          ltac1:(rewrite Hy2).
          rewrite bool_decide_eq_true.
          apply f_equal.
          rewrite map_lookup_filter in Hy1.
          rewrite map_lookup_filter in Hy2.
          rewrite bind_Some in Hy1.
          rewrite bind_Some in Hy2.
          destruct Hy1 as [g1 [H1g1 H2g1]].
          destruct Hy2 as [g2 [H1g2 H2g2]].
          ltac1:(simplify_option_eq).
          assert (Hgood1 := toe_to_cpat_good_side avoid a).
          assert (Hgood2 := toe_to_cpat_list_good_side (avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) l).
          destruct (decide (x ∈ vars_of a)).
          {
            assert (Hxavoid: x ∈ avoid).
            {
              ltac1:(set_solver).
            }
            assert (Hρ'x: ρ' !! x = Some y1).
            {
              clear - Hxavoid H1g1 H3ρ3.
              ltac1:(cut(filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) ρ' !! x = Some y1)).
              {
                intros HH.
                rewrite map_lookup_filter in HH.
                rewrite bind_Some in HH.
                destruct HH as [x0 [HH1 HH2]].
                ltac1:(simplify_option_eq).
                apply HH1.
              }
              ltac1:(rewrite H3ρ3).
              rewrite map_lookup_filter.
              rewrite bind_Some.
              exists y1.
              split>[apply H1g1|].
              ltac1:(simplify_option_eq).
              reflexivity.
              ltac1:(set_solver).
            }
            assert (Hρ4x: ρ4 !! x = Some y1).
            {
              clear - Hxavoid Hρ'x H3ρ4 a.
              ltac1:(cut(filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid) ρ4 !! x = Some y1)).
              {
                intros HH.
                rewrite map_lookup_filter in HH.
                rewrite bind_Some in HH.
                destruct HH as [x0 [HH1 HH2]].
                ltac1:(simplify_option_eq).
                apply HH1.
              }
              ltac1:(rewrite <- H3ρ4).
              rewrite map_lookup_filter.
              rewrite bind_Some.
              exists y1.
              split>[apply Hρ'x|].
              simpl.
              ltac1:(simplify_option_eq).
              reflexivity.
            }
            ltac1:(congruence).
          }
          {
            assert (x ∈ vars_of (toe_to_cpat avoid a).1) by ltac1:(clear X; set_solver).
            assert (Havoid3 := toe_to_cpat_list_avoid ((avoid ++ elements (vars_of (toe_to_cpat avoid a).2))) l x).
            assert (Havoid3' := contraPnot Havoid3). clear Havoid3.
            assert (Havoid4 := toe_to_cpat_good_side_2 avoid a).
            specialize (Havoid3' ltac:(set_solver)).
            assert (Hgood3 := toe_to_cpat_list_good_side (avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) l).
            assert (Hdil: x ∈ vars_of (toe_to_cpat_list (avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) l).1 ∪ vars_of l).
            {
              ltac1:(set_solver).
            }
            rewrite elem_of_union in Hdil.
            destruct Hdil as [Hdil|Hdil].
            {
              ltac1:(contradiction).
            }
            {  
              assert (Hxavoid: x ∈ avoid).
              {
                ltac1:(set_solver).
              }
              assert (Hρ'x: ρ' !! x = Some y1).
              {
                clear - Hxavoid H1g1 H3ρ3.
                ltac1:(cut(filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) ρ' !! x = Some y1)).
                {
                  intros HH.
                  rewrite map_lookup_filter in HH.
                  rewrite bind_Some in HH.
                  destruct HH as [x0 [HH1 HH2]].
                  ltac1:(simplify_option_eq).
                  apply HH1.
                }
                ltac1:(rewrite H3ρ3).
                rewrite map_lookup_filter.
                rewrite bind_Some.
                exists y1.
                split>[apply H1g1|].
                ltac1:(simplify_option_eq).
                reflexivity.
                ltac1:(set_solver).
              }
              assert (Hρ4x: ρ4 !! x = Some y1).
              {
                clear - Hxavoid Hρ'x H3ρ4 a.
                ltac1:(cut(filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid) ρ4 !! x = Some y1)).
                {
                  intros HH.
                  rewrite map_lookup_filter in HH.
                  rewrite bind_Some in HH.
                  destruct HH as [x0 [HH1 HH2]].
                  ltac1:(simplify_option_eq).
                  apply HH1.
                }
                ltac1:(rewrite <- H3ρ4).
                rewrite map_lookup_filter.
                rewrite bind_Some.
                exists y1.
                split>[apply Hρ'x|].
                simpl.
                ltac1:(simplify_option_eq).
                reflexivity.
              }
              ltac1:(congruence).
            }
          }
        }
          
        (*
        
        
        {
          
          
          
          assert (x ∈ vars_of (toe_to_cpat avoid a).1 ∪ vars_of (toe_to_cpat avoid a).2).
          {
            apply elem_of_dom_2 in Hy2.
            unfold vars_of in H3ρ4 at 1; simpl in H3ρ4.
            ltac1:(set_solver).
          }
          rewrite elem_of_subseteq in H3ρ3.
          specialize (H3ρ3 x).
          unfold vars_of in H3ρ3 at 1; simpl in H3ρ3.
          apply elem_of_dom_2 in Hy1 as Hy1'.
          specialize (H3ρ3 Hy1').
          clear Hy1'.
          lazy_match! Constr.type (&H) with
          | x ∈ vars_of (toe_to_cpat ?avoid ?t).1 ∪ vars_of (toe_to_cpat ?avoid ?t).2 =>
            Message.print (Message.of_constr (avoid));
            assert(Hw1 := toe_to_cpat_good_side $avoid $t)
          end.
          assert (Hxx: x ∈ vars_of (toe_to_cpat avoid a).1 \/ x ∈ vars_of a).
          {
            ltac1:(set_solver).
          }
          destruct Hxx as [Hxx|Hxx].
          {
            admit.
          }
          {
            assert (Hxρ': x ∈ dom ρ').
            {
              apply Expression2Term_matches_enough in HH3a.
              unfold vars_of in HH3a at 2; simpl in HH3a.
              clear -Hxx HH3a.
              ltac1:(set_solver).
            }
            rewrite elem_of_dom in Hxρ'.
            destruct Hxρ' as [y Hy].
            
            ltac1:(rewrite map_subseteq_spec in H4ρ4).
            specialize (H4ρ4 x y).
            rewrite map_lookup_filter in H4ρ4.
            rewrite bind_Some in H4ρ4.
            ltac1:(ospecialize (H4ρ4 _)).
            {
              exists y.
              split>[assumption|].
              ltac1:(simplify_option_eq).
              reflexivity.
              reflexivity.
            }
            assert (x ∈ avoid).
            {
              ltac1:(set_solver).
            }
            Search l.
            (* HERE *)
            ltac1:(rewrite map_subseteq_spec in H4ρ3).
            specialize (H4ρ3 x y).
            rewrite map_lookup_filter in H4ρ3.
            rewrite bind_Some in H4ρ3.
            ltac1:(ospecialize (H4ρ3 _)).
            {
              exists y.
              split.
              {
                rewrite map_lookup_filter.
                rewrite bind_Some.
                exists y.
                split>[assumption|].
                rewrite bind_Some.
                simpl.
                reflexivity.
              }
              {

              }
              split>[|reflexivity].
              
              
              reflexivity.
            }
          }
        }
        *)
        Check map_filter_filter_l.
        (*
        *)
        (*
        remember (Valuation2_merge_with (filter
  (λ kv : variable * TermOver builtin_value, kv.1 ∈ vars_of a) ρ') ρ3) as oρ4.
        destruct oρ4.
        {
          admit.
        }
        {
          ltac1:(exfalso).
          unfold Valuation2_merge_with in Heqoρ4.
          ltac1:(case_match; simplify_eq/=).
          clear Heqoρ4.
          unfold Valuation2_compatible_with in H.
          rewrite <- not_true_iff_false in H.
          apply H. clear H.
          rewrite forallb_forall.
          intros x Hx.
          rewrite <- elem_of_list_In in Hx.
          rewrite elem_of_elements in Hx.
          rewrite elem_of_intersection in Hx.
          destruct Hx as [H1x H2x].
          unfold TermOver in *.
          ltac1:(rewrite elem_of_dom in H1x).
          ltac1:(rewrite elem_of_dom in H2x).
          destruct H1x as [y1 Hy1].
          destruct H2x as [y2 Hy2].
          ltac1:(rewrite Hy1).
          ltac1:(rewrite Hy2).
          rewrite bool_decide_eq_true.
          apply f_equal.
          assert (Hgood := toe_to_cpat_good_side avoid a).
          rewrite map_lookup_filter in Hy1.
          rewrite bind_Some in Hy1.
          destruct Hy1 as [g [H1g H2g]].
          ltac1:(simplify_option_eq).
        }
        *)
      }
    }
  Qed.

  Definition keep_data (A : Type) (l : list (option A)) : list A
  :=
    fold_right (fun b a => match b with Some b' => b'::a | None => a end) [] l
  .

(*
  Definition sym_step
    {Σ : StaticModel}
    {UA : UnificationAlgorithm}
    {Act : Set}
    (Γ : RewritingTheory2 Act)
    (s : TermOver BuiltinOrVar)
    :
    list (TermOver BuiltinOrVar)
  :=
    let l'' := (fun r => (ur ← ua_unify s (r.(r_from)); Some (ur, r))) <$> Γ in
    let l' := filter (fun x => x <> None) l'' in
    let l := keep_data l' in
    (fun ur => sub_app_e ur.1 (ur.2.(r_to))) <$> l
  .
*)

End Implementation.

