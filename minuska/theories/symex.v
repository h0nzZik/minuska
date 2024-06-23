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

  Lemma toe_to_cpat_correct_1
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
    (g : TermOver builtin_value)
  :
    elements (vars_of t) ⊆ avoid ->
    ({ ρ : Valuation2 & ((vars_of ρ ⊆ vars_of t) * satisfies ρ g t)%type }) ->
    ({ ρ : Valuation2 &
      (
        (satisfies ρ g ((toe_to_cpat avoid t).1))
        *
        (satisfies ρ tt ((toe_to_cpat avoid t).2))
        *
        (vars_of ρ ⊆ vars_of ((toe_to_cpat avoid t).1) ∪ vars_of ((toe_to_cpat avoid t).2))
      )%type
    })
  .
  Proof.
    revert g avoid.
    ltac1:(induction t using TermOver_rect; intros g avoid Havoid [ρ [Hρ1 Hρ2]]).
    {
      inversion Hρ2; clear Hρ2.
      simpl.
      unfold satisfies; simpl.
      exists (<[(fresh avoid) := g]>ρ).
      split.
      split.
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
          apply Expression2_evaluate_extensive_Some with (ρ2 := <[fresh avoid := g]>ρ) in H0.
          {
            rewrite H0.
            reflexivity.
          }
          apply insert_subseteq.
          apply not_elem_of_dom_1.
          assert (Hfr: fresh avoid ∉ avoid).
          {
            apply infinite_is_fresh.
          }
          intros HContra.
          apply Hfr. clear Hfr.
          ltac1:(set_solver).
        }
      }
      {
        unfold Valuation2 in *.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        ltac1:(rewrite dom_insert).
        ltac1:(set_solver).
      }
    }
    {
      destruct g.
      { inversion Hρ2. }
      unfold satisfies in Hρ2; simpl in Hρ2.
      ltac1:(simp sat2E in Hρ2).
      destruct Hρ2 as [HH1 [HH2 HH3]].
      subst b.
      revert ρ X l0 Hρ1 HH2 HH3.
      induction l; intros ρ X l0 Hρ1 HH2 HH3.
      {
        simpl in *.
        unfold vars_of in Hρ1; simpl in Hρ1.
        apply nil_length_inv in HH2.
        subst l0.
        assert (Hempty : dom ρ = ∅) by ltac1:(set_solver).
        unfold Valuation2 in *.
        apply dom_empty_inv_L in Hempty.
        subst ρ. clear Hρ1 Hρ2.
        unfold satisfies; simpl.
        exists ∅.
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
          unfold vars_of; simpl.
          ltac1:(clear; set_solver).
        }
      }
      {
        unfold Valuation2 in *.
        unfold TermOver in *.
        destruct l0; simpl in *.
        {
          ltac1:(lia).
        }
        rewrite vars_of_t_term_e in Havoid.
        rewrite fmap_cons in Havoid.
        rewrite union_list_cons in Havoid.
        rewrite vars_of_t_term_e in IHl.
        specialize (IHl ltac:(set_solver)).
        remember (filter (fun kv : (variable*(TermOver builtin_value))%type => kv.1 ∈ vars_of l) ρ) as ρ'. 
        specialize (IHl ρ').
        ltac1:(ospecialize (IHl _ l0 _)).
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
        {
          unfold Valuation2 in *.
          unfold TermOver in *.
          subst ρ'.
          ltac1:(cut(vars_of
            (filter (λ kv : variable * TermOver' builtin_value, kv.1 ∈ vars_of l) ρ)
            = vars_of l)).
          {
            intros HHH. rewrite HHH. apply reflexivity.
          }
          unfold vars_of at 1; simpl.
          unfold Valuation2 in *.
          apply dom_filter_L.
          intros x.
          simpl.
          split; intros Hx.
          {
            ltac1:(cut (x ∈ dom ρ)).
            {
              intros Hxρ.
              rewrite elem_of_dom in Hxρ.
              unfold is_Some in Hxρ.
              destruct Hxρ as [x0 Hx0].
              exists x0.
              split>[apply Hx0|].
              unfold vars_of; simpl.
              rewrite elem_of_union_list.
              
              unfold vars_of in Hx; simpl in Hx.
              rewrite elem_of_union_list in Hx.
              destruct Hx as [X0 [H1X0 H2X0]].
              rewrite elem_of_list_fmap in H1X0.
              destruct H1X0 as [t' [H1t' H2t']].
              exists (vars_of t').
              split.
              {
                rewrite elem_of_list_fmap.
                exists t'.
                split>[reflexivity|exact H2t'].
              }
              {
                subst X0.
                exact H2X0.
              }
            }
            unfold vars_of in Hx; simpl in Hx.
            rewrite elem_of_union_list in Hx.
            destruct Hx as [X0 [H1X0 H2X0]].
            rewrite elem_of_list_fmap in H1X0.
            destruct H1X0 as [t' [H1t' H2t']].
            subst X0.
            rewrite elem_of_list_lookup in H2t'.
            destruct H2t' as [i Hi].
            specialize (HH3 (S i)).
            remember (l0 !! i) as l0i.
            destruct l0i.
            {
              symmetry in Heql0i.
              specialize (HH3 t0 _ Hi).
              specialize (HH3 Heql0i).
              apply Expression2Term_matches_enough in HH3.
              clear IHl X.
              ltac1:(set_solver).
            }
            {
              symmetry in Heql0i.
              apply lookup_ge_None in Heql0i.
              simpl in HH2.
              apply lookup_lt_Some in Hi.
              ltac1:(lia).
            }
          }
          {
            destruct Hx as [x0 [H1x0 H2x0]].
            simpl in *.
            unfold vars_of in H2x0; simpl in H2x0.
            exact H2x0.
          }
        }
        simpl in HH2.
        specialize (IHl ltac:(lia)).

        ltac1:(ospecialize (IHl _)).
        {
          clear IHl.
          intros.
          (* assert (HH3old := HH3).*)
          specialize (HH3 (S i) t' φ' pf1 pf2).
          apply Expression2Term_matches_enough in HH3 as HH3'.
          assert (HH4 : vars_of φ' ⊆ vars_of ρ' ).
          {
            subst ρ'.
            unfold vars_of at 2; simpl.
            rewrite elem_of_subseteq.
            intros x Hx.
            assert (Hx' : x ∈ vars_of ρ) by ltac1:(clear -Hx HH3'; set_solver).
            destruct (ρ !! x) eqn:Heqρx.
            {
              unfold Valuation2,TermOver in *.
              rewrite elem_of_dom.
              exists t0.
              rewrite map_lookup_filter.
              rewrite bind_Some.
              simpl.
              exists t0.
              split>[exact Heqρx|].
              ltac1:(simplify_option_eq).
              reflexivity.
              ltac1:(exfalso).
              apply H; clear H.
              unfold vars_of; simpl.
              rewrite elem_of_union_list.
              exists (vars_of φ').
              split>[|exact Hx].
              rewrite elem_of_list_fmap.
              exists φ'.
              split>[reflexivity|].
              rewrite elem_of_list_lookup.
              exists i.
              exact pf1.
            }
            {
              unfold Valuation2,TermOver in *.
              ltac1:(rewrite <- not_elem_of_dom in Heqρx).
              unfold vars_of in Hx'; simpl in Hx'.
              ltac1:(exfalso; contradiction Heqρx).
            }
          }

          assert (Htot2 := TermOverExpression2_evalute_total_2 φ' ρ' HH4).
          destruct Htot2 as [t'' Ht''].
          assert (Ht'2: sat2E ρ t'' φ').
          {
            eapply TermOverExpression2_satisfies_extensive>[|apply Ht''].
            subst ρ'.
            apply map_filter_subseteq.
          }
          assert(Hinj := TermOverExpression2_satisfies_injective ρ φ' t' t'' HH3 Ht'2).
          subst t''.
          exact Ht''.
        }
        destruct IHl as [ρ0 Hρ0].
        destruct Hρ0 as [[Hρ01 Hρ02] Hρ03].
        assert (Xa := X a ltac:(set_solver) t avoid ltac:(set_solver)).
        ltac1:(ospecialize (Xa _)).
        {
          clear Xa.
          exists (filter (fun kv : (variable*(TermOver builtin_value))%type => kv.1 ∈ vars_of a) ρ).
          split.
          {
            rewrite elem_of_subseteq.
            intros x Hx.
            unfold vars_of in Hx; simpl in Hx.
            unfold Valuation2 in *.
            rewrite elem_of_dom in Hx.
            unfold is_Some in Hx.
            destruct Hx as [x0 Hx0].
            rewrite map_lookup_filter in Hx0.
            rewrite bind_Some in Hx0.
            destruct Hx0 as [x1 [H1x2 H2x1]].
            ltac1:(simplify_option_eq).
            apply H.
          }
          {
            specialize (HH3 0 t a erefl erefl).
            apply Expression2Term_matches_enough in HH3 as HH3'.
            assert (HH3'' : vars_of a ⊆ vars_of ((filter (λ kv : variable * TermOver builtin_value, kv.1 ∈ vars_of a) ρ))).
            {
              rewrite elem_of_subseteq.
              intros x Hx.
              unfold vars_of at 1; simpl.
              unfold Valuation2 in *.
              rewrite elem_of_dom.
              unfold is_Some.
              destruct (ρ !! x) eqn:Hρx.
              {
                exists t0.
                rewrite map_lookup_filter.
                rewrite bind_Some.
                exists t0.
                split>[exact Hρx|].
                ltac1:(simplify_option_eq).
                reflexivity.
              }
              {
                ltac1:(exfalso).
                clear -Hx HH3' Hρx.
                unfold vars_of in HH3' at 2; simpl in HH3'.
                rewrite elem_of_subseteq in HH3'.
                specialize (HH3' x Hx).
                ltac1:(rewrite elem_of_dom in HH3').
                destruct HH3' as [y Hy].
                ltac1:(rewrite Hy in Hρx).
                inversion Hρx.
              }
            }
            apply TermOverExpression2_evalute_total_2 in HH3''.
            destruct HH3'' as [e He].
            eapply TermOverExpression2_satisfies_extensive in He as He'
              >[|apply map_filter_subseteq].
            
            unfold satisfies in He'; simpl in He'.
            assert(Hinj := TermOverExpression2_satisfies_injective _ _ _ _ HH3 He').
            subst e.
            apply He.
          }
        }
        destruct Xa as [ρ1 H1ρ1].
        destruct H1ρ1 as [H1ρ1 H2ρ1].
        destruct H1ρ1 as [H1ρ1 H3ρ1].
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

