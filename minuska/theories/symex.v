From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    minusl_syntax
    syntax_properties
    unification_interface
    symex_spec
    valuation_merge
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
          unfold vars_of in Ha ; simpl in Ha.
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
        unfold vars_of in Htmp ; simpl in Htmp.
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
      unfold vars_of; simpl.
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
    forall (ρ' : Valuation2) (nv : NondetValue),
      satisfies ρ' (nv,g) t ->
      ({ ρ : Valuation2 &
        (
          (satisfies ρ g ((toe_to_cpat avoid t).1))
          *
          (satisfies ρ nv ((toe_to_cpat avoid t).2))
          (* *
          (vars_of ρ ⊆ vars_of ((toe_to_cpat avoid t).1) ∪ vars_of ((toe_to_cpat avoid t).2)) *)
          *
          ((filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ avoid) ρ') = filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ avoid) ρ)
        )%type
      })
  .
  Proof.
    revert g avoid.
    ltac1:(induction t using TermOver_rect; intros g avoid Havoid ρ' nv H2ρ').
    {
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
        unfold satisfies in H2ρ'; simpl in H2ρ'.
        ltac1:(simp sat2E in H2ρ').
        destruct (Expression2_evaluate ρ' a) eqn:H2ρ''>[|ltac1:(contradiction)].
        subst g.
        apply Expression2_evalute_strip in H2ρ''.
        eapply Expression2_evaluate_extensive_Some in H2ρ''.
        rewrite H2ρ''.
        { reflexivity. }
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
          ltac1:(contradiction).
          ltac1:(contradiction).
        }
        {
          intros HContra.
          subst i.
          unfold vars_of in Havoid; simpl in Havoid.
          assert (fresh avoid ∉ avoid) by (apply infinite_is_fresh).
          ltac1:(set_solver).
        }
      }
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
          unfold satisfies; simpl.
          ltac1:(simp sat2B).
          (repeat split).
          {
            clear.
            ltac1:(set_solver).
          }
          {
            intros x Hx.
            rewrite elem_of_nil in Hx.
            inversion Hx.
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
        specialize (Xa _ nv HH3a).
        destruct Xa as [ρ4 [[H1ρ4 H2ρ4] H3ρ4]].
        
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
          unfold satisfies; simpl.
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

            assert (Hmc2 := Valuation2_merge_with_correct_2 _ _ _ Heqoρm).
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
              specialize (Hmc2 _ _ H1g').
              destruct Hmc2 as [Hmc2|Hmc2].
              {
                ltac1:(rewrite map_lookup_filter in Hmc2).
                ltac1:(simplify_option_eq).
                assert (Htmp: filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid) ρ' !! x = Some g).
                {
                  rewrite Helper1.
                  rewrite map_lookup_filter.
                  rewrite bind_Some.
                  exists g.
                  split>[assumption|].
                  ltac1:(simplify_option_eq).
                  reflexivity.
                }
                exists g.
                split>[|reflexivity].
                rewrite map_lookup_filter in Htmp.
                rewrite bind_Some in Htmp.
                destruct Htmp as [x0 [H1x0 H2x0]].
                ltac1:(simplify_option_eq).
                assumption.
              }
              {
                ltac1:(rewrite map_lookup_filter in Hmc2).
                ltac1:(simplify_option_eq).
                assert (Htmp: filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ avoid) ρ' !! x = Some g).
                {
                  rewrite H3ρ4.
                  rewrite map_lookup_filter.
                  rewrite bind_Some.
                  exists g.
                  split>[assumption|].
                  ltac1:(simplify_option_eq).
                  reflexivity.
                }
                exists g.
                split>[|reflexivity].
                rewrite map_lookup_filter in Htmp.
                rewrite bind_Some in Htmp.
                destruct Htmp as [x0 [H1x0 H2x0]].
                ltac1:(simplify_option_eq).
                assumption.
              }
            }
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
            assert (Happ: x ∈ avoid ++ elements (vars_of (toe_to_cpat avoid a).1)) by ltac1:(clear -n Hgood1 H; set_solver).
            rewrite elem_of_app in Happ.
            destruct (decide (x ∈ avoid)) as [Hxavoid|Hxavoid].
            {
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
              assert (Hxel: x ∈ elements (vars_of (toe_to_cpat avoid a).1)) by ltac1:(clear - Happ Hxavoid; set_solver).
              assert (Havoid3 := toe_to_cpat_list_avoid ((avoid ++ elements (vars_of (toe_to_cpat avoid a).2))) l x).
              assert (Havoid3' := contraPnot Havoid3). clear Havoid3.
              assert (Havoid4 := toe_to_cpat_good_side_2 avoid a).
              specialize (Havoid3' ltac:(clear - Havoid4 Happ; set_solver)).
              assert (Hgood3 := toe_to_cpat_list_good_side (avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) l).
              assert (Hdil: x ∈ vars_of (toe_to_cpat_list (avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) l).1 ∪ vars_of l).
              {
                clear - Hxel H0 Hgood3 Hxavoid.
                ltac1:(set_solver).
              }
              rewrite elem_of_union in Hdil.
              destruct Hdil as [Hdil|Hdil].
              {
                ltac1:(contradiction).
              }
              {  
                assert (Hxavoid': x ∈ avoid).
                {
                  ltac1:(set_solver).
                }
                ltac1:(contradiction Hxavoid).
              }
            }
          }
        }
      }
    }
  Qed.

  Lemma toe_to_cpat_correct_2
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
    (g : TermOver builtin_value)
  :
    elements (vars_of t) ⊆ avoid ->
    forall (ρ : Valuation2) (nv : NondetValue),
      (satisfies ρ g ((toe_to_cpat avoid t).1)) ->
      (satisfies ρ nv ((toe_to_cpat avoid t).2)) ->
      satisfies ρ (nv,g) t
  .
  Proof.
    revert avoid g.
    ltac1:(induction t using TermOver_rect; intros avoid g Havoid ρ nv Hsat1 Hsat2).
    {
      simpl in *.
      unfold satisfies in *; simpl in *.
      ltac1:(simp sat2B in Hsat1).
      ltac1:(simp sat2E).
      specialize(Hsat2 ({| sc_left := e_variable (fresh avoid); sc_right := a |})).
      specialize (Hsat2 ltac:(set_solver)).
      unfold satisfies in Hsat2; simpl in Hsat2.
      unfold isSome in *.
      destruct (ρ !! fresh avoid) eqn:Hρfr.
      {
        destruct (Expression2_evaluate ρ a) eqn:Heq>[|ltac1:(contradiction)].
        subst.
        simpl in *.
        ltac1:(simplify_eq/=).
        reflexivity.
      }
      {
        destruct (Expression2_evaluate ρ a) eqn:Heq>[|ltac1:(contradiction)].
        destruct Hsat2.
      }
    }
    {
      unfold satisfies; simpl.
      rewrite toe_to_cpat_list_equiv in Hsat1.
      rewrite toe_to_cpat_list_equiv in Hsat2.
      unfold satisfies in Hsat1, Hsat2. simpl in Hsat1, Hsat2.
      destruct g; ltac1:(simp sat2B in Hsat1).
      { destruct Hsat1. }
      ltac1:(simp sat2E).
      destruct Hsat1 as [HH1 [HH2 HH3]].
      subst b.
      split>[reflexivity|].
      ltac1:(rewrite length_toe_to_cpat_list in HH2).
      split>[assumption|].

      revert l0 avoid HH2 HH3 X Havoid Hsat2.
      induction l; intros l0 avoid HH2 HH3 X Havoid Hsat2.
      {
        destruct l0; simpl in *; try ltac1:(lia).
        intros.
        rewrite lookup_nil in pf1. inversion pf1.
      }
      {
        destruct l0; simpl in *; try ltac1:(lia).
        intros i t' φ' H1i H2i.
        destruct i.
        {
          simpl in *.
          ltac1:(simplify_eq/=).
          eapply X with (avoid := avoid).
          {
            rewrite elem_of_cons.
            left.
            reflexivity.
          }
          {
            ltac1:(rewrite vars_of_t_term_e in Havoid).
            rewrite fmap_cons in Havoid.
            rewrite union_list_cons in Havoid.
            ltac1:(set_solver).
          }
          {
            specialize (HH3 0). simpl in HH3.
            apply HH3.
            { reflexivity. }
            { reflexivity. }
          }
          {
            unfold satisfies; simpl.
            intros c Hc.
            apply Hsat2.
            { ltac1:(set_solver). }
          }
        }
        {
          simpl in *.
          ltac1:(ospecialize (IHl l0 (avoid ++ elements (vars_of (toe_to_cpat avoid a).2)) _ _ _ _ _)).
          {
            ltac1:(lia).
          }
          {
            intros i0 t'0 φ'0 H'1 H'2.
            apply HH3 with (i := (S i0)).
            simpl. exact H'1.
            simpl. exact H'2.
          }
          {
            intros.
            apply X with (avoid := (avoid0 (* ++ elements (vars_of (toe_to_cpat avoid0 φ').2) *))).
            { rewrite elem_of_cons. right. assumption. }
            { ltac1:(set_solver). }
            { assumption. }
            { assumption. }
          }
          {
            ltac1:(rewrite vars_of_t_term_e in Havoid).
            rewrite fmap_cons in Havoid.
            rewrite union_list_cons in Havoid.
            ltac1:(rewrite vars_of_t_term_e).
            ltac1:(set_solver).
          }
          {
            intros c Hc.
            apply Hsat2.
            { ltac1:(set_solver). }
          }
          eapply IHl.
          { apply H1i. }
          { apply H2i. }
        }
      }
    }
  Qed.

  Definition keep_data {A : Type} (l : list (option A)) : list A
  :=
    fold_right (fun b a => match b with Some b' => b'::a | None => a end) [] l
  .

  Lemma keep_data_iff {A : Type} (ol : list (option A))
    :
    forall x,
    x ∈ keep_data ol <-> (Some x) ∈ ol
  .
  Proof.
    induction ol; intros x; simpl.
    {
      split; intros H; rewrite elem_of_nil in H; destruct H.
    }
    {
      destruct a.
      {
        rewrite elem_of_cons.
        rewrite elem_of_cons.
        ltac1:(naive_solver).
      }
      {
        rewrite elem_of_cons.
        ltac1:(naive_solver).
      }
    }
  Qed.


  Definition sym_step
    {Σ : StaticModel}
    {UA : UnificationAlgorithm}
    {Act : Set}
    (Γ : RewritingTheory2 Act)
    (s : (TermOver BuiltinOrVar)*(list SideCondition2))
    :
    list ((TermOver BuiltinOrVar)*(list SideCondition2))%type
  :=
    (* Unify the symbolic state with all left-sides *)
    let l'' := (fun r => (ur ← ua_unify s.1 (r.(r_from)); Some (ur, r))) <$> Γ in
    (* Keep only the successful results *)
    let l' := filter (fun x => x <> None) l'' in
    let l : list (((SubT)*(RewritingRule2 Act))%type) := keep_data l' in
    
    let rhss : list (TermOver Expression2) := (fun ur => sub_app_e ur.1 (ur.2.(r_to))) <$> l in
    let rhss' := (fun x => toe_to_cpat (elements (vars_of x)) x) <$> rhss in
    (fun r => (r.1, s.2 ++ r.2))<$> rhss'
  .

  Definition State_interp {Σ : StaticModel} :
    ((TermOver BuiltinOrVar)*(list SideCondition2))%type ->
    (TermOver builtin_value) ->
    Type
  :=
    fun s g =>
    {
      ρ : Valuation2 & ((satisfies ρ g s.1)
      * (forall (nv : NondetValue), satisfies ρ nv s.2))%type
    }
  .

  Lemma vars_of_sub_app_sub
    {Σ : StaticModel} (sub : @SubT Σ) x:
    vars_of (sub_app sub x) ⊆ union_list ((@vars_of (TermOver BuiltinOrVar) variable _ _ (VarsOf_TermOver_BuiltinOrVar)) <$> (fmap snd sub)) ∪ (vars_of x)
  .
  Proof.
    revert x;
    induction sub; simpl; intros x.
    {
      ltac1:(set_solver).
    }
    {
      destruct a as [x' t']; simpl in *.
      eapply transitivity. apply IHsub. clear IHsub.
      assert (Htmp2 := vars_of_TermOverBoV_subst__approx).
      unfold fmap; simpl.
      ltac1:(set_solver).
    }
  Qed.

  Lemma vars_of_sub_app_e_sub
    {Σ : StaticModel} (sub : @SubT Σ) x:
    vars_of (sub_app_e sub x) ⊆ union_list ((@vars_of (TermOver BuiltinOrVar) variable _ _ (VarsOf_TermOver_BuiltinOrVar)) <$> (fmap snd sub)) ∪ (vars_of x)
  .
  Proof.
    revert x;
    induction sub; simpl; intros x.
    {
      ltac1:(set_solver).
    }
    {
      destruct a as [x' t']; simpl in *.
      eapply transitivity. apply IHsub. clear IHsub.
      assert (Htmp2 := vars_of_TermOverBoV_subst_e2__approx).
      unfold fmap; simpl.
      ltac1:(set_solver).
    }
  Qed.

  Lemma vars_of_sub_app_sub_3
      {Σ : StaticModel} (sub : @SubT Σ) x y:
      y ∈ vars_of (sub_app sub x) ->
      y ∉ union_list ((@vars_of (TermOver BuiltinOrVar) variable _ _ (VarsOf_TermOver_BuiltinOrVar)) <$> (fmap snd sub)) ->
      y ∉ vars_of_sub sub ->
      y ∈ (vars_of x)
    .
    Proof.
      revert x y.
      induction sub; intros x y H1 H1' H2; simpl in *.
      {
        assumption.
      }
      {
        destruct a as [y' t'].
        apply not_elem_of_union in H2.
        destruct H2 as [H2 H3].
        rewrite elem_of_singleton in H2.
        apply not_elem_of_union in H1'.
        destruct H1' as [H4 H5].
        specialize (IHsub _ _ H1 H5 H3).
        simpl in *.
        destruct (decide (y' ∈ vars_of x)) as [Hin|Hnotin].
        {
          assert (Htmp := vars_of_TermOverBoV_subst x t' y' Hin).
          rewrite Htmp in IHsub. clear Htmp.
          ltac1:(set_solver).
        }
        {
          rewrite subst_notin2 in IHsub>[|assumption].
          exact IHsub.
        }
      }
  Qed.
  
  #[global]
  Instance TermOverBuiltin_to_TermOverBoV_inj
    {Σ : StaticModel}
   : Inj (=) (=) TermOverBuiltin_to_TermOverBoV
  .
  Proof.
    unfold Inj.
    intros x.
    induction x; intros y Hxy; destruct y; simpl in *.
    {
      unfold TermOverBuiltin_to_TermOverBoV in Hxy.
      simpl in Hxy.
      ltac1:(simplify_eq/=).
      reflexivity.
    }
    {
      unfold TermOverBuiltin_to_TermOverBoV in Hxy.
      simpl in Hxy.
      ltac1:(simplify_eq/=).
    }
    {
      unfold TermOverBuiltin_to_TermOverBoV in Hxy.
      simpl in Hxy.
      ltac1:(simplify_eq/=).
    }
    {
      unfold TermOverBuiltin_to_TermOverBoV in Hxy.
      simpl in Hxy.
      ltac1:(simplify_eq/=).
      revert l0 H0.
      induction l; intros l0 H0; destruct l0; simpl in *.
      {
        reflexivity.
      }
      {
        inversion H0.
      }
      {
        inversion H0.
      }
      {
        inversion H0; subst; clear H0.
        rewrite Forall_cons in H.
        destruct H as [HH1 HH2].
        specialize (IHl HH2).
        specialize (HH1 _ H2).
        specialize (IHl _ H3).
        inversion IHl; subst; clear IHl.
        reflexivity.
      }
    }
  Qed.

  Definition Valuation2_to_SubT
    {Σ : StaticModel}
    (ρ : Valuation2)
    : SubT
  :=
    let l := map_to_list ρ in
    fmap (fun x => (x.1, (TermOverBuiltin_to_TermOverBoV x.2))) l
  .
  
  Lemma Valuation2_to_SubT__NoDup
    {Σ : StaticModel}
    (ρ : Valuation2)
  :
    NoDup (Valuation2_to_SubT ρ)
  .
  Proof.
    unfold Valuation2_to_SubT.
    rewrite NoDup_fmap.
    {
      unfold Valuation2 in *.
      apply NoDup_map_to_list.
    }
    {
      intros x y Hxy.
      inversion Hxy; subst; clear Hxy.
      destruct x,y.
      simpl in *.
      subst v0.
      apply TermOverBuiltin_to_TermOverBoV_inj in H1.
      subst t0.
      reflexivity.
    }
  Qed.
    
    
  Lemma Valuation2_to_SubT__NoDup_1
    {Σ : StaticModel}
    (ρ : Valuation2)
  :
    NoDup (fmap fst (Valuation2_to_SubT ρ))
  .
  Proof.
    unfold Valuation2_to_SubT.
    Search NoDup fmap.
    apply NoDup_fmap_fst.
    {
      intros.
      assert (Htmp := NoDup_fst_map_to_list ρ).
      rewrite elem_of_list_fmap in H.
      rewrite elem_of_list_fmap in H0.
      destruct H as [t1 [H1t1 H2t1]].
      destruct H0 as [t2 [H1t2 H2t2]].
      ltac1:(simplify_eq/=).
      destruct t1 as [x1 t1].
      destruct t2 as [x2 t2].
      simpl in *.
      subst x2.
      ltac1:(rewrite elem_of_map_to_list in H2t1).
      ltac1:(rewrite elem_of_map_to_list in H2t2).
      ltac1:(simplify_eq/=).
      reflexivity.
    }
    rewrite NoDup_fmap.
    {
      unfold Valuation2 in *.
      apply NoDup_map_to_list.
    }
    {
      intros x y Hxy.
      inversion Hxy; subst; clear Hxy.
      destruct x,y.
      simpl in *.
      subst v0.
      apply TermOverBuiltin_to_TermOverBoV_inj in H1.
      subst t0.
      reflexivity.
    }
  Qed.


  Definition TermOverBoV_to_TermOverBuiltin
    {Σ : StaticModel} (φ : TermOver BuiltinOrVar) (pf : vars_of φ ⊆ vars_of ∅)
  :=
    TermOverBoV_eval ∅ φ pf
  .


  (*
    1. sub = [], ρ = { x ↦ 3 } ==> { x ↦ 3 }
    2. sub = [(x, y + 3)], ρ = { y ↦ 4 } ==> { x ↦ 4 + 3, y ↦ 4 }
    3. sub = [(x, y + 3)], ρ = { x ↦ 4 } ==> { x ↦ 4 } ??? IGNORE
    Basically, I want to extend `ρ` with new variables found in the lhs of `sub`.
  *)

  #[local]
  Obligation Tactic := idtac.
  Program Fixpoint extend_val_with_sub
    {Σ : StaticModel}
    (ρ : Valuation2)
    (sub : SubT)
    (d : TermOver builtin_value)
    : Valuation2
  :=
    match sub with
    | [] => ρ
    | (x,t)::sub' =>
      let ρ' := extend_val_with_sub ρ sub' d in
      let sub'' := Valuation2_to_SubT ρ' in
      let t_filled := sub_app sub'' t in
      match (decide (vars_of t_filled = ∅)) with
      | left _ =>
        let t_filled_coerced := TermOverBoV_to_TermOverBuiltin t_filled _ in
        <[x := t_filled_coerced]>ρ'
      | right _ => 
        (* cannot coerce t_filled to a ground term => use a default value *)
        <[x := d]>ρ'
      end
    end
  .
  Next Obligation.
    abstract(
    intros; subst;
    rewrite wildcard';
    apply empty_subseteq).
  Defined.
  Fail Next Obligation.

  Lemma extend_val_with_sub__vars
    {Σ : StaticModel}
    (ρ : Valuation2)
    (sub : SubT)
    (d : TermOver builtin_value)
  :
    vars_of (extend_val_with_sub ρ sub d) = vars_of ρ ∪ vars_of_sub sub
  .
  Proof.
    induction sub; simpl in *.
    {
      ltac1:(set_solver).
    }
    {
      ltac1:(repeat case_match); subst; simpl in *.
      {
        clear H0. ltac1:(rename e into H1).
        unfold vars_of; simpl.
        unfold Valuation2 in *.
        rewrite dom_insert_L.
        ltac1:(set_solver).
      }
      {
        clear H0. ltac1:(rename n into H1).
        unfold vars_of; simpl.
        unfold Valuation2 in *.
        ltac1:(set_solver).
      }
    }
  Qed.

  Lemma vars_of_sub_eq
    {Σ : StaticModel}
    (sub : SubT)
  :
    vars_of_sub sub = list_to_set (sub.*1)
  .
  Proof.
    induction sub; simpl.
    {
      reflexivity.
    }
    { 
      destruct a as [x t]. simpl in *.
      rewrite IHsub.
      reflexivity.
    }
  Qed.

  Lemma extend_val_with_sub__extends
    {Σ : StaticModel}
    (ρ : Valuation2)
    (sub : SubT)
    (d : TermOver builtin_value)
  :
    NoDup sub.*1 ->
    vars_of_sub sub ## vars_of ρ ->
    ρ ⊆ extend_val_with_sub ρ sub d
  .
  Proof.
    revert ρ.
    induction sub; intros ρ Hnd Hvars.
    {
      apply map_subseteq_po.
    }
    {
      ltac1:(ospecialize (IHsub ρ _ _)).
      {
        clear -Hnd.
        inversion Hnd; subst; clear Hnd.
        assumption.
      }
      {
        destruct a as [x t]; simpl in *.
        ltac1:(set_solver).
      }
      assert(Htmp := extend_val_with_sub__vars ρ (sub) d).
      destruct a as [x t]. simpl in *.
      ltac1:(case_match).
      {
        clear H. ltac1:(rename e into H1).
        unfold Valuation2 in *.
        eapply transitivity>[|apply insert_subseteq].
        exact IHsub.
        apply not_elem_of_dom_1.
        intros HContra.
        inversion Hnd; subst; clear Hnd.
        assert(HContra' : x ∈ vars_of ρ \/ x ∈ vars_of_sub sub) by ltac1:(set_solver).
        destruct HContra' as [HContra'|HContra'].
        {
          ltac1:(set_solver).
        }
        {
          rewrite vars_of_sub_eq in HContra'.
          rewrite elem_of_list_to_set in HContra'.
          apply H2. apply HContra'.
        }
      }
      {
        clear H. ltac1:(rename n into H1).
        unfold Valuation2 in *.
        eapply transitivity>[|apply insert_subseteq].
        exact IHsub.
        apply not_elem_of_dom_1.
        intros HContra.
        inversion Hnd; subst; clear Hnd.
        assert(HContra' : x ∈ vars_of ρ \/ x ∈ vars_of_sub sub) by ltac1:(set_solver).
        destruct HContra' as [HContra'|HContra'].
        {
          ltac1:(set_solver).
        }
        {
          rewrite vars_of_sub_eq in HContra'.
          rewrite elem_of_list_to_set in HContra'.
          apply H2. apply HContra'.
        }
      }
    }
  Qed.

  Lemma vars_of__toe_to_cpat
    {Σ : StaticModel}
    (et : TermOver Expression2)
    avoid
    :
    vars_of et ⊆ vars_of (toe_to_cpat avoid et).1 ∪ vars_of (toe_to_cpat avoid et).2
  .
  Proof.
    revert avoid.
    induction et; intros avoid.
    {
      simpl in *.
      unfold vars_of in *; simpl in *.
      unfold vars_of in *; simpl in *.
      ltac1:(set_solver).
    }
    {
      rewrite toe_to_cpat_list_equiv.
      rewrite vars_of_t_term_e.
      rewrite elem_of_subseteq.
      intros x Hx.
      rewrite elem_of_union_list in Hx.
      rewrite elem_of_union.
      destruct Hx as [X [H1X H2X]].
      rewrite elem_of_list_fmap in H1X.
      destruct H1X as [y [H1y H2y]].
      subst X.
      rewrite Forall_forall in H.

      revert avoid H H2y H2X.
      induction l; intros avoid H H2y H2X.
      {
        rewrite elem_of_nil in H2y.
        destruct H2y.
      }
      {
        rewrite elem_of_cons in H2y.
        destruct H2y as [H2y|H2y].
        {
          subst a.
          simpl.
          rewrite vars_of_t_term.
          rewrite fmap_cons.
          rewrite union_list_cons.
          rewrite elem_of_union.
          (*specialize (H y ltac:(set_solver) (avoid ++ elements (vars_of (toe_to_cpat avoid y).2))). *)
          specialize (H y ltac:(set_solver) (avoid)).
          rewrite elem_of_subseteq in H.
          specialize (H _ H2X).
          rewrite elem_of_union in H.
          destruct H as [H|H].
          {
            left. left. exact H.
          }
          {
            right. unfold vars_of; simpl.
            rewrite fmap_app.
            rewrite union_list_app.
            rewrite elem_of_union.
            left. exact H.
          }
        }
        {
          simpl.
          specialize (IHl (avoid ++ elements (vars_of (toe_to_cpat avoid a).2))).
          ltac1:(ospecialize (IHl _)).
          {
            intros. apply H. rewrite elem_of_cons. right. assumption.
          }
          specialize (IHl H2y H2X).
          destruct IHl as [IHl|IHl].
          {
            left.
            rewrite vars_of_t_term.
            rewrite fmap_cons.
            rewrite union_list_cons.
            rewrite elem_of_union.
            right.
            simpl in IHl.
            apply IHl.
          }
          {
            right.
            unfold vars_of; simpl. 
            rewrite fmap_app.
            rewrite union_list_app.
            simpl in IHl.
            rewrite elem_of_union.
            right.
            apply IHl.
          }
        }
      }
    }
  Qed.

  Lemma vars_of_sub_app_sub_2
    {Σ : StaticModel} (sub : SubT) (t : TermOver BuiltinOrVar)
    (x : variable):
    x ∈ vars_of t ->
    x ∉ vars_of_sub sub ->
    x ∈ vars_of (sub_app sub t)
  .
  Proof.
    revert x t.
    induction sub; intros x t H1 H2.
    {
      simpl. exact H1.
    }
    {
      destruct a as [x' t'].
      simpl in *.
      rewrite not_elem_of_union in H2.
      destruct H2 as [H2 H3].
      rewrite elem_of_singleton in H2.
      apply IHsub.
      {
        destruct (decide (x' ∈ vars_of t)) as [Hin|Hnotin].
        {
          clear IHsub.
          rewrite vars_of_TermOverBoV_subst.
          {
            ltac1:(set_solver).
          }
          {
            exact Hin.
          }
        }
        {
          rewrite subst_notin2.
          { assumption. }
          {
            assumption.
          }
        }
      }
      {
        assumption.
      }
    }
  Qed.

  Fixpoint set_default_variables
    {Σ : StaticModel}
    (ρ : Valuation2)
    (xs : list variable)
    (d : TermOver builtin_value)
    : Valuation2
  :=
    match xs with
    | [] => ρ
    | x::xs' => 
      let ρ' := set_default_variables ρ xs' d in
      <[x:=d]>ρ'
    end
  .

  Lemma set_default_variables_works
    {Σ : StaticModel}
    (ρ : Valuation2)
    (xs : list variable)
    (d : TermOver builtin_value)
    (x : variable)
  :
    x ∈ xs ->
    x ∈ vars_of (set_default_variables ρ xs d)
  .
  Proof.
    revert x.
    induction xs; simpl; intros x HH.
    {
      rewrite elem_of_nil in HH. destruct HH.
    }
    {
      rewrite elem_of_cons in HH.
      destruct HH as [HH|HH].
      {
        subst.
        unfold vars_of; simpl.
        unfold Valuation2 in *.
        rewrite dom_insert_L.
        ltac1:(set_solver).
      }
      {
        specialize (IHxs _ HH).
        unfold vars_of; simpl.
        unfold Valuation2 in *.
        rewrite dom_insert_L.
        unfold vars_of in IHxs; simpl in IHxs.
        ltac1:(set_solver).
      }
    }
  Qed.


  Lemma set_default_variables_works_2
    {Σ : StaticModel}
    (ρ : Valuation2)
    (xs : list variable)
    (d : TermOver builtin_value)
  :
    (vars_of ρ) ## (list_to_set xs) ->
    vars_of (set_default_variables ρ xs d) = union (vars_of ρ) (list_to_set xs)
  .
  Proof.
    revert ρ.
    induction xs; intros ρ HH; simpl.
    {
      ltac1:(set_solver).
    }
    {
      specialize (IHxs ρ ltac:(set_solver)).
      unfold vars_of; simpl.
      unfold Valuation2 in *.
      rewrite dom_insert_L.
      ltac1:(set_solver).
    }
  Qed.


  Lemma set_default_variables_works_2'
    {Σ : StaticModel}
    (ρ : Valuation2)
    (xs : list variable)
    (d : TermOver builtin_value)
    x g
  :
    (vars_of ρ) ## (list_to_set xs) ->
    x ∉ xs ->
    (set_default_variables ρ xs d) !! x = Some g ->
    ρ !! x = Some g
  .
  Proof.
    revert ρ.
    induction xs; intros ρ HH1 HH2 HH3; simpl.
    {
      ltac1:(set_solver).
    }
    {
      specialize (IHxs ρ ltac:(set_solver) ltac:(set_solver)).
      simpl in HH3.
      unfold Valuation2 in *.
      rewrite lookup_insert_Some in HH3.
      destruct HH3 as [HH3 | HH3].
      {
        destruct HH3.
        subst.
        ltac1:(set_solver).
      }
      {
        apply IHxs.
        apply HH3.
      }
    }
  Qed.


  Lemma set_default_variables_ext
    {Σ : StaticModel}
    (ρ : Valuation2)
    (xs : list variable)
    (d : TermOver builtin_value)
    :
    NoDup xs ->
    (vars_of ρ) ## (list_to_set xs) ->
    ρ ⊆ set_default_variables ρ xs d
  .
  Proof.
    revert d.
    induction xs; intros d Hnd Hd; simpl in *.
    {
      apply map_subseteq_po.
    }
    {
      inversion Hnd; subst; clear Hnd.
      specialize (IHxs d ltac:(assumption) ltac:(set_solver)).
      unfold Valuation2 in *.
      eapply transitivity>[apply IHxs|].
      apply insert_subseteq.
      unfold Valuation2 in *.
      apply not_elem_of_dom_1.
      assert (Htmp := set_default_variables_works_2 ρ xs d ltac:(set_solver)).
      unfold vars_of in Htmp; simpl in Htmp.
      ltac1:(rewrite Htmp).
      ltac1:(set_solver).
    }
  Qed.

  Lemma set_default_variables_mono
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (xs : list variable)
    (d : TermOver builtin_value)
    :
    ρ1 ⊆ ρ2 ->
    set_default_variables ρ1 xs d ⊆ set_default_variables ρ2 xs d
  .
  Proof.
    induction xs; intros Hsub; simpl in *.
    {
      exact Hsub.
    }
    {
      specialize(IHxs Hsub).
      unfold Valuation2 in *.
      apply insert_mono.
      exact IHxs.
    }
  Qed.

  Lemma sub_app_builtin
    {Σ : StaticModel}
    (sub : SubT)
    (b : builtin_value):
    (sub_app sub (t_over (bov_builtin b))) = t_over (bov_builtin b)
  .
  Proof.
    induction sub; simpl.
    { reflexivity. }
    {
      destruct a; simpl.
      apply IHsub.
    }
  Qed.

  (*
  Lemma vars_of_sub_app_empty
    {Σ : StaticModel}
    (sub : SubT)
    φ
    :
    vars_of (sub_app sub φ) = ∅*)


  (*
  Lemma TermOverBoV_to_TermOverBuiltin_iff
    {Σ : StaticModel}
    φ pf1 pf2
    :
    TermOverBoV_to_TermOverBuiltin φ pf1 = TermOverBoV_eval ∅ φ pf2
  .
  Proof.
    ltac1:(funelim (TermOverBoV_eval _ _ _)).
    {
      simpl.
      ltac1:(simp TermOverBoV_eval).
      reflexivity.
    }
    {
      ltac1:(simp TermOverBoV_eval).
      clear Heqcall.
      ltac1:(move: ((TermOverBoV_eval_obligation_2 Σ ∅ s l pf))).
      revert pf1 pf H0.
      intros pf1 pf2 pf3 pf4.
      clear pf3.
      clear pf2.
      revert pf1 pf4 H.
      induction l; intros pf1 pf4 H.
      {
        reflexivity.
      }
      {
        simpl.
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_to_TermOverBuiltin.
        ltac1:(f_equal).
        ltac1:(f_equal).
        {
          specialize (H a).
          ltac1:(ospecialize (H _)).
          {
            rewrite elem_of_cons.
            left.
            reflexivity.
          }
          specialize (H Σ ∅ a).
          assert (pf1' := pf1).
          rewrite vars_of_t_term in pf1'.
          rewrite fmap_cons in pf1'.
          rewrite union_list_cons in pf1'.
          assert (Harg: vars_of a ⊆ vars_of ∅).
          {
            abstract( 
              clear - pf1';
              unfold vars_of; simpl;
              unfold vars_of in pf1'; simpl in pf1';
              ltac1:(set_solver)
            ).
          }
          specialize(H Harg).
          simpl in H.
          specialize(H ltac:(lia)).
          specialize (H Σ).
          ltac1:(unshelve(eapply (H))).
          {
            (repeat f_equal); apply proof_irrelevance.
          }
          {
            unfold eq_rect, eq_trans; simpl.
            unfold f_equal.
            ltac1:(case_match).
            reflexivity.
          }
        }
        {
          assert (pf1' := pf1).
          rewrite vars_of_t_term in pf1'.
          rewrite fmap_cons in pf1'.
          rewrite union_list_cons in pf1'.
          assert(pf1'': vars_of (t_term s l) = ∅).
          {
            rewrite vars_of_t_term.
            ltac1:(set_solver).
          }
          specialize (IHl pf1'').
          assert(pf4': (∀ (x : StaticModel) (x0 : Valuation2) (x1 : TermOver BuiltinOrVar),
            vars_of x1 ⊆ vars_of x0 ->
            TermOver_size x1 < TermOver_size (t_term s l) ->
            TermOver builtin_value)
            ->
            ∀ φ' : TermOver' BuiltinOrVar,
            φ' ∈ l → vars_of φ' ⊆ vars_of ∅
          ).
          {
            abstract(
              intros;
              clear - pf1' H0;
              rewrite elem_of_list_lookup in H0;
              destruct H0 as [i Hi];
              apply take_drop_middle in Hi;
              rewrite <- Hi in pf1';
              rewrite fmap_app in pf1';
              rewrite fmap_cons in pf1';
              unfold TermOver in *;
              rewrite union_list_app_L in pf1';
              rewrite union_list_cons in pf1';
              ltac1:(set_solver)
            ).
          }
          specialize (IHl pf4').
          ltac1:(ospecialize (IHl _)).
          {
            intros.
            assert(pf'' := pf').
            rewrite elem_of_list_lookup in pf''.
            destruct pf'' as [i Hi].
            apply take_drop_middle in Hi.
            assert (Harg': φ' ∈ a :: l).
            {
              rewrite <- Hi.
              clear.
              ltac1:(set_solver).
            }
            assert(Harg'': TermOver_size φ' < TermOver_size (t_term s (a :: l))).
            {
              simpl.

              assert(pf'' := pf').
              rewrite elem_of_list_lookup in pf''.
              destruct pf'' as [i' Hi'];
              apply take_drop_middle in Hi'.
              rewrite <- Hi'.
              rewrite sum_list_with_app.
              simpl.
              ltac1:(lia).
            }
            assert(Harg''': vars_of φ' ⊆ vars_of ∅).
            {
              intros.
              rewrite elem_of_list_lookup in pf';
              destruct pf' as [i' Hi'];
              apply take_drop_middle in Hi';
              rewrite <- Hi' in pf1';
              rewrite fmap_app in pf1';
              rewrite fmap_cons in pf1';
              unfold TermOver in *;
              rewrite union_list_app_L in pf1';
              rewrite union_list_cons in pf1';
              ltac1:(set_solver).
            }
            ltac1:(unshelve(eapply (H φ' Harg' Σ ∅ φ' Harg''' Harg''))).
            {
              (repeat f_equal).
              (* SOMETHING IS TERRIBLY WRONG BECAUSE WE HAVE MULTIPLE STATIC MODELS *)
            }
          }
          eapply IHl.
        }
        {
          apply IHl.
        }
      }
      ltac1:(case_match).
    }
  Qed.
  *)

  (*
  Lemma vars_of_sub_app_under_empty
    {Σ : StaticModel}
    (sub : SubT)
    (φ : TermOver BuiltinOrVar)
    :
    subseteq (vars_of (sub_app sub φ)) empty ->
    sub_app sub φ = empty
  .*)

  Lemma TermOverBoV_eval_empty_eq
    {Σ : StaticModel}
    phi1 phi2 pf1 pf2
    :
    phi1 = phi2 ->
    TermOverBoV_eval empty phi1 pf1 = TermOverBoV_eval empty phi2 pf2
  .
  Proof.
    ltac1:(funelim(TermOverBoV_eval empty phi1 pf1)); intros HH.
    {
      subst.
      ltac1:(simp TermOverBoV_eval).
      reflexivity.
    }
    {
      subst.
      ltac1:(simp TermOverBoV_eval).
      apply f_equal.
      revert pf2. clear H0 Heqcall. revert pf.
      intros pf1 pf2.
      assert (Hpf: pf1 = pf2) by (apply proof_irrelevance).
      rewrite Hpf.
      reflexivity.
    }
    {
      subst.
      ltac1:(simp TermOverBoV_eval).
      apply f_equal.
      apply proof_irrelevance.
    }
    {
     subst.
     ltac1:(simp TermOverBoV_eval).
     apply f_equal.
     apply proof_irrelevance.
   }
  Qed.
  
  (*
  Lemma fmap_fst_Valuation2_to_SubT
    {Σ : StaticModel}
    (ρ : Valuation2)
    :    
    fmap fst (Valuation2_to_SubT ρ) ⊆ (elements (dom ρ))
  .
  Proof.
    unfold Valuation2_to_SubT.
    unfold Valuation2 in *.
    ltac1:(induction ρ using map_ind).
    {
      rewrite map_fold_empty.
      simpl.
      rewrite dom_empty_L.
      rewrite elements_empty.
      reflexivity.
    }
    {
      apply not_elem_of_dom_2 in H.
      rewrite dom_insert_L.
      rewrite map_fold_insert.
      {
        simpl.
        ltac1:(set_solver).
      }
      {
        apply _.
      }
      {
        intros. apply _.
      }
      ltac1:(set_solver).
    }
  Qed.*)
  
  Lemma sub_app_nodup_perm
    {Σ : StaticModel}
    (sub1 sub2 : SubT)
    (φ : TermOver BuiltinOrVar)
  :
    NoDup (fst <$> sub1) ->
    sub1 ≡ₚ sub2 ->
    sub_app sub1 φ = sub_app sub2 φ
  .
  Proof.
    
    intros Hnd H. revert φ. induction H; intros φ.
    {
      simpl. reflexivity.
    }
    {
      simpl.
      destruct x as [i t].
      rewrite IHPermutation.
      reflexivity.
      inversion Hnd; assumption.
    }
    {
      simpl.
      destruct x as [i1 t1].
      destruct y as [i2 t2].
      inversion Hnd; subst; clear Hnd.
      inversion H2; subst; clear H2.
      apply not_elem_of_cons in H1.
      destruct H1 as [H1 H2].
    }
  Qed.
  
  Lemma sub_similar
    {Σ : StaticModel}
    (sub : SubT)
    (x0 : variable)
    (ρ0 : Valuation2)
    (d : TermOver builtin_value)
  :
    x0 ∉ dom ρ0 ->
    sub_app (Valuation2_to_SubT (extend_val_with_sub ρ0 sub d)) (t_over (bov_variable x0)) = sub_app sub (t_over (bov_variable x0))
  .
  Proof.
    induction sub; intros HH; simpl in *.
    {
      unfold Valuation2 in *.
          
      
      revert x0 d HH.
      ltac1:(induction ρ0 using map_ind); intros x0 d HH.
      {
        unfold Valuation2_to_SubT.
        ltac1:(rewrite map_to_list_empty).
        simpl.
        reflexivity.
      }
      {
        
        rewrite dom_insert in HH.
        rewrite not_elem_of_union in HH.
        destruct HH as [HH1 HH2].
        specialize (IHρ0 x0 d HH2).
        unfold Valuation2_to_SubT in *.
        rewrite not_elem_of_singleton in HH1.
        Search map_to_list.
        About map_to_list_insert.
        assert (Hperm := map_to_list_insert m i x H).
        ltac1:(rewrite map_to_list_insert).
      }
      
      
      
      
      revert HH.
      revert x0.
      revert d.
      unfold Valuation2_to_SubT.
      Check map_fold_ind.
      apply (map_fold_ind (fun (b : TermOver builtin_value) (m : gmap variable (TermOver builtin_value)) =>
        forall d x0, x0 ∉ dom m -> sub_app (Valuation2_to_SubT ρ0) (t_over (bov_variable x0)) = t_over (bov_variable x0) )).
      {
        intros. admit.
      }
      {
        admit.
      }
      {
        intros.
      }
      ltac1:(induction ρ0 using map_fold_ind); intros HH.
      {
        unfold Valuation2_to_SubT.
        ltac1:(rewrite map_fold_empty).
        simpl.
        reflexivity.
      }
      {
        rewrite dom_insert in HH.
        rewrite not_elem_of_union in HH.
        destruct HH as [HH1 HH2].
        specialize (IHρ0 HH2).
        unfold Valuation2_to_SubT in *.
        rewrite not_elem_of_singleton in HH1.
        Search map_fold insert.
        Check map_fold_insert_L.
        ltac1:(rewrite map_fold_insert); try assumption.
        {
          intros.
          unfold Valuation2 in *.
          ltac1:(rewrite lookup_insert in H1).
        }
      }
    }
  Qed.


  Lemma wonderful_lemma
    {Σ : StaticModel}
    (φ : TermOver BuiltinOrVar)
    (ρ : Valuation2)
    (sub : SubT)
    (d : TermOver builtin_value)
    pf
  :
    (forall x, x ∈ vars_of φ -> ~(x ∈ vars_of ρ <-> x ∈ vars_of_sub sub)) ->
  sat2B 
    (extend_val_with_sub ρ sub d)
    (
      TermOverBoV_eval
      (
        set_default_variables
        (extend_val_with_sub ρ sub d)
        (elements
          (vars_of (sub_app sub φ) ∖ vars_of (extend_val_with_sub ρ sub d)))
        d
      )
      (sub_app sub φ)
      pf
    )
    φ
  .
  Proof.
    ltac1:(funelim (sat2B _ _ _)).
    {
      destruct bv;
        simpl; ltac1:(simp sat2B);
        unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar.
      {
        revert pf.
        ltac1:(rewrite {2 3} sub_app_builtin).
        ltac1:(rewrite {1 2} sub_app_builtin).
        intros pf; simpl.
        ltac1:(simp TermOverBoV_eval).
        reflexivity.
      }
      {
        revert ρ0 x d pf.
        induction sub; intros ρ0 x d pf Hdisj; simpl in *.
        {
          ltac1:(simp TermOverBoV_eval).
          unfold TermOverBoV_eval_unfold_clause_2.
          destruct (inspect
            (set_default_variables ρ0
            (elements (vars_of (t_over (bov_variable x)) ∖ vars_of ρ0)) d
            !! x)
          ).
          destruct x0.
          {
            eapply set_default_variables_works_2'>[()|()|apply e].
            ltac1:(set_solver).
            specialize (Hdisj x).
            unfold vars_of in Hdisj; simpl in Hdisj.
            unfold vars_of in Hdisj; simpl in Hdisj.
            specialize(Hdisj ltac:(set_solver)).
            intros HContra.
            ltac1:(set_solver).
          }
          {
            unfold TermOverBoV_eval_obligation_1; simpl.
            ltac1:(exfalso).
            unfold vars_of in pf; simpl in pf.
            unfold vars_of in pf; simpl in pf.
            unfold vars_of in e; simpl in e.
            unfold vars_of in e; simpl in e.
            unfold Valuation2 in *.
            apply not_elem_of_dom_2 in e.
            ltac1:(set_solver).
          }
        }
        {
          ltac1:(repeat case_match).
          {
            subst; simpl in *.
            unfold Valuation2 in *.
            rewrite lookup_insert.
            clear H1.
            ltac1:(rename e0 into H1).
            clear H0.
            specialize (IHsub ρ0 x d).
            assert (Hdisj1 := Hdisj x).
            unfold vars_of in Hdisj1; simpl in Hdisj1.
            unfold vars_of in Hdisj1; simpl in Hdisj1.
            specialize (Hdisj1 ltac:(set_solver)).
            unfold Valuation2 in *.
            rewrite elem_of_union in Hdisj1.
            rewrite elem_of_singleton in Hdisj1.
            assert (Hx'rho0: x ∉ dom ρ0) by ltac1:(set_solver).
            clear Hdisj1.
            unfold Valuation2 in *.
            
            destruct t; simpl.
            {
              destruct a; simpl.
              {
                apply f_equal.
                revert pf.
                ltac1:(move: extend_val_with_sub_obligation_1).
                ltac1:(rewrite sub_app_builtin).
                simpl. intros pf1 pf2.
                ltac1:(simp TermOverBoV_eval).
                ltac1:(move: (pf1 (@extend_val_with_sub) Σ ρ0 d (t_over (bov_builtin b)) sub H1)).
                ltac1:(rewrite {1 2} sub_app_builtin).
                intros pf0.
                simpl.
                reflexivity.
              }
              {
                

                erewrite <- TermOverBoV_eval__varsofindependent_2 with (ρ1 := (<[x:=TermOverBoV_to_TermOverBuiltin
          (sub_app (Valuation2_to_SubT (extend_val_with_sub ρ0 sub d)) (t_over (bov_variable x0)))
          (extend_val_with_sub_obligation_1 (@extend_val_with_sub) Σ ρ0 d (t_over (bov_variable x0)) sub H1)]>
     (extend_val_with_sub ρ0 sub d))).
                {
                  unfold TermOverBoV_to_TermOverBuiltin.
                  apply f_equal.
                  assert (H1' := H1).
                  assert (pf' := pf).
                  revert H1' pf'.
                  set (Valuation2_to_SubT (extend_val_with_sub ρ0 sub d)) as wsub.
                  set (sub_app wsub (t_over (bov_variable x0))) as x0_result.
                  set (extend_val_with_sub_obligation_1 (@extend_val_with_sub)  Σ ρ0 d (t_over (bov_variable x0)) sub H1) as some_t.
                  set (sub_app sub (t_over (bov_variable x0))) as x0_old_result.
                  intros H1' pf'.
                  (*
                    It would come handy now if [x0_old_result = t_over (bov_variable x)].
                    Since [x] is not in rho0, wsub  behaves with respect to x in the same way [sub] does.
                    
                  *)
                  destruct (decide (x0 ∈ dom ρ0)) as [Hin1|Hnin1].
                  {
                    admit.
                  }
                  {
                    ltac1:(exfalso).
                    assert ((sub_app wsub (t_over (bov_variable x0))) = (sub_app sub (t_over (bov_variable x0)))).
                    {
                      ltac1:(unfold wsub).
                      Search Valuation2_to_SubT.
                    }
                    Search sub_app.
                  }
                  ltac1:(move: (extend_val_with_sub_obligation_1 _ _ _ _ _ _ _)).



                  epose (Htmp := TermOverBoV_eval__insert (extend_val_with_sub ρ0 sub d) x (TermOverBoV_eval ∅ (sub_app (Valuation2_to_SubT (extend_val_with_sub ρ0 sub d)) (t_over (bov_variable x0)))
                  (extend_val_with_sub_obligation_1 (@extend_val_with_sub) Σ ρ0 d (sub_app sub (t_over (bov_variable x0))) sub _))).
                  erewrite Htmp.

                  ltac1:(shelve).
                }
                {
                  apply set_default_variables_ext.
                  { apply NoDup_elements. }
                  { ltac1:(set_solver). }
                }
                erewrite <- TermOverBoV_eval__varsofindependent_2 with (ρ1 := empty).
                {
                  unfold TermOverBoV_to_TermOverBuiltin.
                  (repeat f_equal).
                  ltac1:(move:(extend_val_with_sub_obligation_1 _ _ _ _ _ _ _)).
                  intros pf2.
                  apply TermOverBoV_eval_empty_eq.
                  ltac1:(f_equal).
                  admit.
                }
                {
                  unfold Valuation2 in *.
                  unfold TermOver in *.
                  unfold Subseteq_Valuation2 in *.
                  rewrite map_subseteq_spec.
                  intros i x1 Hx1.
                  rewrite lookup_empty in Hx1.
                  inversion Hx1.
                }
                Search TermOverBoV_eval.
                rewrite <- IHsub.
              }
            }
            {

            }

            







            assert (Htmp0:
              vars_of (sub_app sub (t_over (bov_variable x)))
                ⊆ vars_of
                  (set_default_variables (extend_val_with_sub ρ0 sub d)
                  (elements
                  (vars_of (sub_app sub (t_over (bov_variable x)))
                ∖ vars_of (extend_val_with_sub ρ0 sub d)))
                  d)
            ).
            {
              rewrite elem_of_subseteq.
              intros x' Hx'.
              rewrite set_default_variables_works_2.
              rewrite elem_of_union.
              destruct (decide (x' ∈ vars_of (extend_val_with_sub ρ0 sub d))).
              {
                left.
                assumption.
              }
              {
                right.
                rewrite elem_of_list_to_set.
                rewrite elem_of_elements.
                rewrite elem_of_difference.
                split>[|assumption].
                rewrite extend_val_with_sub__vars in n.
                rewrite not_elem_of_union in n.
                destruct n as [H11 H22].
                apply vars_of_sub_app_sub_2.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                rewrite elem_of_singleton.
                reflexivity.
                assumption.
              }
              ltac1:(set_solver).
            }
            assert (Htmp:
              x ∈ vars_of (set_default_variables (extend_val_with_sub ρ0 sub d)
              (elements (vars_of (sub_app sub (t_over (bov_variable x))) ∖ vars_of (extend_val_with_sub ρ0 sub d)))   d)
            ).
            {
              rewrite set_default_variables_works_2.
              rewrite elem_of_union.
              destruct (decide (x ∈ vars_of (extend_val_with_sub ρ0 sub d))).
              {
                left.
                assumption.
              }
              {
                right.
                rewrite elem_of_list_to_set.
                rewrite elem_of_elements.
                rewrite elem_of_difference.
                split>[|assumption].
                rewrite extend_val_with_sub__vars in n.
                rewrite not_elem_of_union in n.
                destruct n as [H11 H22].
                apply vars_of_sub_app_sub_2.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                rewrite elem_of_singleton.
                reflexivity.
                assumption.
              }
              ltac1:(set_solver).
            }
            
            specialize (IHsub ). (* by Htmp *)

            assert(x ∉ vars_of_sub sub).
            {
              Search vars_of sub_app.
              
            }
            ltac1:(rewrite IHsub).
            apply f_equal.
            lazy_match! goal with
            | [ |- (TermOverBoV_to_TermOverBuiltin _ ?pf1) = _ ] =>
              remember $pf1
            end.

            remember (
                (elements
                (vars_of (sub_app sub t)
              ∖ vars_of
                (<[x:=TermOverBoV_to_TermOverBuiltin
                (sub_app
                (Valuation2_to_SubT
                (extend_val_with_sub ρ0 sub d))
                t)
                e]>
                (extend_val_with_sub ρ0 sub d))))
            ) as els.
            unfold Valuation2 in *.
            ltac1:(rewrite <- Heqels).
          }
          {

          }
          {

          }
          {

          }
        }
      }
    }
    {

    }
    {

    }
  Qed.

  Lemma sym_step_sim_1
    {Σ : StaticModel}
    {UA : UnificationAlgorithm}
    (*
    {Act : Set}
    {_EA : EqDecision Act}
    *)
    {_Inh : Inhabited NondetValue}
    {_Inh2 : Inhabited symbol}
    (Γ : RewritingTheory2 unit)
    (wfΓ : RewritingTheory2_wf_alt Γ)
    (s s' : (TermOver BuiltinOrVar)*(list SideCondition2))
    :
    s' ∈ sym_step Γ s ->
    ∀ (g' : TermOver builtin_value) (nv : NondetValue),
      State_interp s' g' ->
      {
        g : TermOver builtin_value &
        ((State_interp s g)*(rewriting_relation Γ nv g g'))%type
      }
  .
  Proof.
    intros Hss' g' nv Hs'g'.
    unfold sym_step in Hss'.
    apply elem_of_list_fmap_T_1 in Hss'.
    destruct Hss' as [[y1 y2] [Htmp Hs']].
    subst s'. simpl in *.
    apply elem_of_list_fmap_T_1 in Hs'.
    destruct Hs' as [z [Htmp Hs']].
    apply elem_of_list_fmap_T_1 in Hs'.
    destruct Hs' as [y [H1y H2y]].
    subst z.
    rewrite keep_data_iff in H2y.
    rewrite elem_of_list_filter in H2y.
    destruct H2y as [_ H2y].
    apply elem_of_list_fmap_T_1 in H2y.
    destruct H2y as [y0 [H1y0 H2y0]].
    ltac1:(simplify_option_eq).
    ltac1:(rename H into sub).
    ltac1:(rename y0 into r).
    unfold State_interp in Hs'g'.
    destruct Hs'g' as [ρ [H1s'g' H2s'g']].
    simpl in H1s'g'.
    assert (Hcor1 := toe_to_cpat_correct_2 (elements (vars_of (sub_app_e sub (r_to r))))).
    simpl in *.
    specialize (Hcor1 (sub_app_e sub (r_to r)) g' ltac:(clear; set_solver) ρ).
    specialize (H2s'g' nv).
    specialize (Hcor1 nv).
    rewrite <- Htmp in Hcor1.
    simpl in Hcor1.
    specialize (Hcor1 H1s'g').
    ltac1:(ospecialize (Hcor1 _)).
    {
      unfold satisfies; simpl.
      unfold satisfies in H2s'g'; simpl in H2s'g'.
      intros sc Hsc.
      ltac1:(specialize (H2s'g' sc ltac:(set_solver))).
      exact H2s'g'.
    }
    (*unfold rewriting_relation.*)
    unfold State_interp.
    remember (sub_app sub (r_from r)) as from'.
    remember (r_from r) as fr.
    remember (r_to r) as to.

    assert (H2s'g'': forall x, x ∈ s.2 ++ y2 -> vars_of x ⊆ vars_of ρ).
    {
      intros x Hx.
      specialize (H2s'g' x Hx).
      destruct x as [x1 x2]; simpl in *.
      unfold satisfies in H2s'g'; simpl in H2s'g'.
      destruct (Expression2_evaluate ρ x1) as [t1|] eqn:He1,
        (Expression2_evaluate ρ x2) as [t2|] eqn:He2;
        try (ltac1:(contradiction)).
      apply Expression2_evaluate_Some_enough in He1.
      apply Expression2_evaluate_Some_enough in He2.
        
      unfold vars_of; simpl.
      rewrite union_subseteq.
      
      split.
      {
        apply He1.
      }
      {
        apply He2.
      }
    }
    pose(ρ' := @extend_val_with_sub Σ ρ sub (t_term (@inhabitant _ _Inh2) [])).
    epose(ρ'' := @set_default_variables Σ ρ' (elements ((@vars_of (TermOver BuiltinOrVar) variable _ _ _ (from')) ∖ (@vars_of Valuation2 variable _ _ (@VarsOf_Valuation2 Σ) ρ'))) (t_term (@inhabitant _ _Inh2) [])).
    unfold Valuation2 in *.
    
    assert (Hmytmp: vars_of from' ⊆ vars_of ρ'').
    {
      subst from'.
      apply Expression2Term_matches_enough in Hcor1.
      apply vars_of_sat_tobov in H1s'g'.
      unfold satisfies in H2s'g'; simpl in H2s'g'.
      apply ua_unify_oota in Heqo as Hnoota.
      rewrite union_subseteq in Hnoota.
      destruct Hnoota as [Hsub1 Hsub2].
      
      ltac1:(unfold ρ'').
      rewrite elem_of_subseteq.
      intros x Hx.
      rewrite set_default_variables_works_2.
      {
        ltac1:(unfold ρ').
        rewrite extend_val_with_sub__vars.
        rewrite elem_of_union.
        rewrite elem_of_list_to_set.
        rewrite elem_of_elements.
        rewrite elem_of_difference.
        subst.
        destruct (decide (x ∈ vars_of ρ ∪ vars_of_sub sub)) as [Hin|Hnotin].
        {
          unfold Valuation2 in *.
          left.
          exact Hin.
        }
        {
          right.
          split.
          { apply Hx. }
          {
            apply Hnotin.
          }
        }
      }
      {
        rewrite elem_of_disjoint.
        intros x0 Hx0.
        rewrite elem_of_list_to_set.
        rewrite elem_of_elements.
        intros H1x0.
        rewrite elem_of_difference in H1x0.
        destruct H1x0 as [H1x0 H2x0].
        apply H2x0.
        apply Hx0.
      }
    }
    (* For some reason, plain `pose` does not work well with typeclasses :-( )*)
    pose(coerced := @TermOverBoV_eval Σ ρ'' from' Hmytmp).
    exists coerced.
    split.
    {
      exists ρ''.
      split.
      {
        ltac1:(unfold ρ'').
        eapply TermOverBoV_satisfies_extensive.
        {
          apply set_default_variables_ext.
          apply NoDup_elements.
          ltac1:(set_solver).
        }
        ltac1:(unfold ρ').
        ltac1:(unfold coerced).
        ltac1:(unfold ρ'').
        subst from'.
        unfold satisfies; simpl.
        apply ua_unify_sound in Heqo as Hsound.
        destruct Hsound as [Hsnd _].
        clear coerced.
        revert Hmytmp.
        ltac1:(rewrite - {1 3} Hsnd).
        intros Hmytmp.
        apply (f_equal vars_of) in Hsnd as Hsnd'.
        assert (Htmp6 : (elements (vars_of (sub_app sub fr) ∖ vars_of ρ')) = (elements (vars_of (sub_app sub s.1) ∖ vars_of ρ'))).
        {
          ltac1:(congruence).
        }
        ltac1:(unfold ρ'' in *; idtac).
        clear ρ''.
        revert Hmytmp.
        ltac1:(rewrite {1 2} Htmp6).
        intros Hmytmp.
        ltac1:(unfold ρ' in *; idtac).
        (* Time to use [wonderful_lemma] *)
        apply Expression2Term_matches_enough in Hcor1.



        (*
        (erewrite <- TermOverBoV_eval__varsofindependent_2>[|(
              apply set_default_variables_ext
            )])>[()|apply NoDup_elements|(ltac1:(set_solver))].
            Unshelve.
        {

        }
        {
          rewrite elem_of_subseteq.
          intros x Hx.
          assert (Htmp1 := vars_of_sub_app_sub sub s.1).
          rewrite elem_of_subseteq in Htmp1.
          specialize (Htmp1 x Hx).
          rewrite elem_of_union in Htmp1.
          rewrite extend_val_with_sub__vars.
          rewrite elem_of_union.
          clear Hmytmp.
          clear Htmp6.
        }
        *)


      }
      {

      }
    }
    {
      unfold rewriting_relation.
      exists r.
      exists ().
      split>[assumption|].
      unfold rewrites_to.
      exists ρ''.
    }
    
      (*assert (Hse := vars_of_sub_app_e_sub sub (r_to r)).*)
      About vars_of_sub_app_sub.
      Search vars_of sub_app.
      

      (* apply ua_unify_oota in Heqo as Hoota. *)
      Search ua_unify.
      (* I think I would need to feed the coercion a valuation that uses `sub`*)
      Search s.
      (*eapply transitivity>[apply ua_unify_vars_of|].*)
      Check ua_unify_vars_of.
      (*
      Search ua_unify.
      (* THIS IS WEIRD *)
      eapply transitivity>[|apply Hcor1]. *)
      (* Look at `HCor1`!*)
      
      Check ua_unify_vars_of.
      Check vars_of_sub_app_sub.
      Print sub_app.
      
      
      Search satisfies vars_of.
      Search vars_of sub_app.
    }
    Search toe_to_cpat.
    (*
      s.1    --r-->  toe_to_cpat (to sub)  ---- (to sub)
       |                     |
       | sub                 | ρ
       |                     |
      fr sub                 g'

    *)
    Search TermOver BuiltinOrVar builtin_value.
    Search SubT.
  Qed.

(*
  (* Hey this is not true. Because this says that any two concrete states that are somehow related symbolically are connected concretely also,
  but consider the system `x => x +Int 1` and s={1,2} and s'={2,3}:
  There is no transition from 1 to 3.*)
  Lemma sym_step_correct_1
    {Σ : StaticModel}
    {UA : UnificationAlgorithm}
    {Act : Set}
    {_EA : EqDecision Act}
    {_Inh : Inhabited NondetValue}
    (Γ : RewritingTheory2 Act)
    (s s' : (TermOver BuiltinOrVar)*(list SideCondition2))
    :
    s' ∈ sym_step Γ s ->
    ∀ (g g' : TermOver builtin_value),
      State_interp s g ->
      State_interp s' g' ->
      { nv : NondetValue & rewriting_relation Γ nv g g' }
  .
  Proof.
    intros Hs' g g' Hg Hg'.
    unfold State_interp in Hg,Hg'.
    destruct Hg as [ρ [H1g H2g]].
    destruct Hg' as [ρ' [H1g' H2g']].
    unfold sym_step in Hs'.
    apply elem_of_list_fmap_T_1 in Hs'.
    destruct Hs' as [[y1 y2] [Htmp Hs']].
    subst s'. simpl in *.
    apply elem_of_list_fmap_T_1 in Hs'.
    destruct Hs' as [z [Htmp Hs']].
    assert(Hcor' := toe_to_cpat_correct_2 (elements (vars_of z)) z g').
    specialize(Hcor' ltac:(3; set_solver)).
    specialize (Hcor' ρ').
    assert(Hcor: ∀ nv, satisfies ρ' (nv, g') z).
    {
      intros nv.
      apply (Hcor' nv).
      {
        rewrite <- Htmp.
        simpl.
        exact H1g'.
      }
      {
        rewrite <- Htmp.
        simpl.
        unfold satisfies; simpl.
        unfold satisfies in H2g'; simpl in H2g'.
        intros x Hx.
        apply H2g'.
        { clear -Hx; ltac1:(set_solver). }
      }
    }
    clear Hcor'.
    apply elem_of_list_fmap_T_1 in Hs'.
    destruct Hs' as [[sub r] [Htmp' Hs']].
    subst z. simpl in *.
    rewrite keep_data_iff in Hs'.
    rewrite elem_of_list_filter in Hs'.
    destruct Hs' as [_ Hs'].
    Set Typeclasses Debug.
    apply elem_of_list_fmap_T_1 in Hs'.
    destruct Hs' as [r' [H1 H2]].
    symmetry in H1.
    apply bind_Some_T_1 in H1.
    destruct H1 as [sub' [H1sub' H2sub']].
    inversion H2sub'; subst; clear H2sub'.
    exists inhabitant.
    unfold rewriting_relation; simpl.
    exists r.
    exists (r_act r).
    split>[exact H2|].
    unfold rewrites_to; simpl.
    unfold rewrites_in_valuation_under_to; simpl.
    destruct s as [φ scs]. simpl in *.
    exists ρ.
    (repeat split).
    {

    }
    {

    }
    {
      unfold satisfies; simpl.
      unfold satisfies in H2g; simpl in H2g.
      intros x Hx.
      apply (H2g _ x).
      
    }
    
  Qed.
*)
End Implementation.

