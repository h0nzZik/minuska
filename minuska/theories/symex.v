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
            eapply TermOverExpression2_satisfies_extensive.
            Search satisfies Expression2.
            Check sat2E.
          }
          (*
          assert (Htot1 := Expression2_evalute_total_1).
          
          Search sat2E.
          eapply HH3.
          *)
        }
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

