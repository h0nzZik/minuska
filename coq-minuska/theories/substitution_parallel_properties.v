From Minuska Require Import
    prelude
    spec
    substitution_parallel
    basic_properties
    termoverbov_subst
    termoverbov_subst_properties
.

From Coq Require Import Logic.Classical_Prop.

Definition subtmm_closed {Σ : StaticModel} (s : SubP) :=
    forall k v, s !! k = Some v -> vars_of v = ∅
.

Lemma subp_app_empty
    {Σ : StaticModel}
    (φ : TermOver BuiltinOrVar)
    :
    subp_app ∅ φ = φ
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        { reflexivity. }
        {
            ltac1:(case_match).
            { ltac1:(rewrite lookup_empty in H). inversion H. }
            {
                reflexivity.
            }
        }
    }
    {
        apply f_equal.
        revert H.
        induction l; intros H; simpl in *.
        {
            reflexivity.
        }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            specialize (IHl H2).
            clear H2.
            rewrite H1.
            rewrite IHl.
            reflexivity.
        }
    }
Qed.


Lemma subp_app_closed
    {Σ : StaticModel}
    (sub_mm : SubP)
    (φ : TermOver BuiltinOrVar)
    :
    vars_of φ = ∅ ->
    subp_app sub_mm φ = φ
.
Proof.
    induction φ; intros HH; simpl in *.
    {
        destruct a; simpl in *.
        { reflexivity. }
        {
            unfold vars_of in HH; simpl in HH.
            unfold vars_of in HH; simpl in HH.
            ltac1:(set_solver).
        }
    }
    {
        apply f_equal.
        revert HH H.
        induction l; intros HH H; simpl in *.
        { reflexivity. }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            rewrite vars_of_t_term in HH.
            rewrite fmap_cons in HH.
            rewrite union_list_cons in HH.
            specialize (IHl ltac:(set_solver)).
            specialize (H1 ltac:(set_solver)).
            rewrite H1.
            rewrite (IHl H2).
            reflexivity.
        }
    }
Qed.

Lemma subp_app_almost_closed
    {Σ : StaticModel}
    (s : SubP)
    (φ : TermOver BuiltinOrVar)
    :
    vars_of φ ## subp_dom s ->
    subp_app s φ = φ
.
Proof.
    unfold SubP in *.
    revert s.
    induction φ; intros ss HH; simpl in *.
    {
        destruct a; simpl in *.
        { reflexivity. }
        {
            unfold vars_of in HH; simpl in HH.
            unfold vars_of in HH; simpl in HH.
            rewrite disjoint_singleton_l in HH.
            unfold subp_dom in HH.
            destruct (ss !! x) eqn:Heq.
            {
                apply elem_of_dom_2 in Heq.
                ltac1:(contradiction HH).
            }
            {
                ltac1:(rewrite Heq).
                reflexivity.
            }
        }
    }
    {
        apply f_equal.
        revert HH H.
        induction l; intros HH H; simpl in *.
        { reflexivity. }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            rewrite vars_of_t_term in HH.
            rewrite fmap_cons in HH.
            rewrite union_list_cons in HH.
            specialize (IHl ltac:(set_solver)).
            specialize (H1 ltac:(set_solver)).
            rewrite H1.
            rewrite (IHl H2).
            reflexivity.
            ltac1:(set_solver).
        }
    }
Qed.

Lemma subp_app_empty'
    {Σ : StaticModel}
    :
    subp_app ∅ = id
.
Proof.
    apply functional_extensionality.
    apply subp_app_empty.
Qed.

Lemma subp_app_insert0
    {Σ : StaticModel}
    (s : SubP)
    (x : variable)
    (v : TermOver BuiltinOrVar)
    :
    vars_of v ## subp_dom s ->
    subp_app (<[x:=v]>s)
    = (subp_app s) ∘ (fun φ => TermOverBoV_subst φ x v)
.
Proof.
    unfold SubP in *.
    intros HH.
    apply functional_extensionality.
    intros φ.
    revert s x v HH.
    induction φ; intros ss x v HH; simpl.
    {
        destruct a; simpl.
        {
            reflexivity.
        }
        {
            destruct (decide (x = x0)).
            {
                subst.
                ltac1:(rewrite lookup_insert).
                symmetry.
                apply subp_app_almost_closed.
                exact HH.
            }
            {
                ltac1:(rewrite lookup_insert_ne).
                {
                    ltac1:(congruence).
                }
                {
                    ltac1:(case_match).
                    {
                        simpl.
                        ltac1:(rewrite H).
                        reflexivity.
                    }
                    {
                        rewrite subp_app_almost_closed.
                        reflexivity.
                        unfold vars_of; simpl.
                        unfold vars_of; simpl.
                        unfold subp_dom.
                        apply not_elem_of_dom_2 in H.
                        ltac1:(set_solver).
                    }
                }
            }
        }
    }
    {
        apply f_equal.
        revert H.
        induction l; intros H; simpl in *.
        { reflexivity. }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            rewrite (IHl H2).
            rewrite H1.
            reflexivity.
            assumption.
        }
    }
Qed.

Lemma subp_app_singleton
    {Σ : StaticModel}
    x p
    :
    subp_app {[x:=p]} = (fun q => TermOverBoV_subst q x p)
.
Proof.
    ltac1:(rewrite - insert_empty).
    ltac1:(rewrite subp_app_insert0).
    unfold subp_dom.
    ltac1:(rewrite dom_empty_L).
    ltac1:(set_solver).
    ltac1:(rewrite subp_app_empty').
    unfold compose.
    apply functional_extensionality.
    intros y.
    reflexivity.
Qed.

Lemma subp_app_union_comm
    {Σ : StaticModel}
    (a b : gmap variable (TermOver BuiltinOrVar))
    :
    subp_dom a ## subp_dom b ->
    subp_app (a ∪ b) = subp_app (b ∪ a)
.
Proof.
    intros HH0.
    apply functional_extensionality.
    intros phi.
    revert a b HH0.
    induction phi; intros aa bb HH0; simpl in *.
    {
        destruct a.
        { reflexivity. }
        {
            ltac1:(repeat case_match).
            {
                ltac1:(rewrite lookup_union in H).
                ltac1:(rewrite lookup_union in H0).
                destruct (aa !! x) eqn:Hax,
                  (bb !! x) eqn:Hbx.
                {
                    inversion H; subst; clear H.
                    inversion H0; subst; clear H0.
                    ltac1:(apply elem_of_dom_2 in Hax).
                    ltac1:(apply elem_of_dom_2 in Hbx).
                    unfold subp_dom in *.
                    unfold subp_codom in *.
                    ltac1:(set_solver).
                }
                {
                    inversion H; subst; clear H.
                    inversion H0; subst; clear H0.
                    ltac1:(apply elem_of_dom_2 in Hax).
                    unfold subp_dom in *.
                    unfold subp_codom in *.
                    ltac1:(set_solver).
                }
                {
                    inversion H; subst; clear H.
                    inversion H0; subst; clear H0.
                    ltac1:(apply elem_of_dom_2 in Hbx).
                    unfold subp_dom in *.
                    unfold subp_codom in *.
                    ltac1:(set_solver).
                }
                {
                    inversion H.
                }
            }
            {
                ltac1:(rewrite lookup_union in H).
                ltac1:(rewrite lookup_union in H0).
                destruct (aa !! x) eqn:Hax,
                  (bb !! x) eqn:Hbx.
                {
                    inversion H; subst; clear H.
                    inversion H0; subst; clear H0.
                }
                {
                    inversion H; subst; clear H.
                    inversion H0; subst; clear H0.
                }
                {
                    inversion H; subst; clear H.
                    inversion H0; subst; clear H0.
                }
                {
                    inversion H.
                }
            }
            {
                ltac1:(rewrite lookup_union in H).
                ltac1:(rewrite lookup_union in H0).
                destruct (aa !! x) eqn:Hax,
                  (bb !! x) eqn:Hbx.
                {
                    inversion H; subst; clear H.
                }
                {
                    inversion H; subst; clear H.
                }
                {
                    inversion H; subst; clear H.
                }
                {
                    inversion H0.
                }
            }
            {
                reflexivity.
            }
        }
    }
    {
        apply f_equal.
        apply map_ext_Forall.
        rewrite Forall_forall in H.
        rewrite Forall_forall.
        intros x Hx.
        specialize (H x Hx).
        apply H.
        apply HH0.
    }
Qed.

Lemma subp_compose_helper_1
    {Σ : StaticModel}
    (b c : SubP)
    :
    subp_codom b ## subp_dom c ->
    subp_app c <$> b = b
.
Proof.
    intros Hdisj.
    apply map_eq_iff.
    intros i.
    destruct (b !! i) eqn:Hbi.
    {
        rewrite lookup_fmap.
        ltac1:(rewrite Hbi).
        simpl.
        apply f_equal.
        apply subp_app_almost_closed.
        unfold SubP in *.
        ltac1:(assert(vars_of t ⊆ subp_codom b)).
        {
            unfold subp_codom.
            rewrite elem_of_subseteq.
            intros x Hx.
            rewrite elem_of_union_list.
            exists (vars_of t).
            split>[|exact Hx].
            rewrite elem_of_list_fmap.
            exists t.
            split>[reflexivity|].
            rewrite elem_of_elements.
            ltac1:(rewrite elem_of_map_img).
            exists i.
            exact Hbi.
        }
        ltac1:(set_solver).
    }
    {
        rewrite lookup_fmap.
        ltac1:(rewrite Hbi).
        reflexivity.
    }
Qed.

Lemma subp_app_union
    {Σ : StaticModel}
    (b c : gmap variable (TermOver BuiltinOrVar))
    :
    subp_codom b ## subp_dom c ->
    subp_app (b ∪ c) = (subp_app c) ∘ (subp_app b)
.
Proof.
    intros HH.
    apply functional_extensionality.
    intros phi.
    revert b c HH.
    induction phi; intros b c HH.
    {
        simpl.
        ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
        {
            unfold SubP in *.
            ltac1:(erewrite lookup_union_Some_l in H0)>[|apply H1].
            apply (inj Some) in H0.
            subst.
            symmetry.
            apply subp_app_almost_closed.
            (* ltac1:(eapply lookup_union_Some_l in H1). *)
            ltac1:(assert(vars_of t ⊆ subp_codom b)).
            {
                unfold subp_codom.
                rewrite elem_of_subseteq.
                intros y Hy.
                rewrite elem_of_union_list.
                exists (vars_of t).
                split>[|exact Hy].
                rewrite elem_of_list_fmap.
                exists t.
                split>[reflexivity|].
                rewrite elem_of_elements.
                ltac1:(rewrite elem_of_map_img).
                exists x.
                exact H1.
            }
            ltac1:(set_solver).
        }
        {
            ltac1:(rewrite lookup_union_r in H0).
            exact H1.
            ltac1:(rewrite H0).
            reflexivity.
        }
        {
            ltac1:(exfalso).
            unfold SubP in *.
            rewrite lookup_union in H0.
            rewrite H1 in H0.
            unfold union,option_union,union_with,option_union_with in H0.
            ltac1:(case_match; simplify_eq/=).
        }
        {
            unfold SubP in *.
            rewrite lookup_union in H0.
            rewrite H1 in H0.
            unfold union,option_union,union_with,option_union_with in H0.
            ltac1:(case_match; simplify_eq/=).
            reflexivity.
        }
    }
    {
        simpl.
        f_equal.
        clear s.
        ltac1:(replace (map) with (@fmap list list_fmap) by reflexivity).
        rewrite <- list_fmap_compose.
        apply list_fmap_ext.
        intros i x Hix.
        rewrite Forall_forall in H.
        specialize (H x).
        ltac1:(ospecialize (H _)).
        {
            rewrite elem_of_list_lookup.
            exists i.
            exact Hix.
        }
        specialize (H _ _ HH).
        exact H.
    }
Qed.

(* 
(* 1. a={(y,0)}, b={(x,f(y))} ==> {(x, f(0))} *)
Example subp_compose_ex1
  {Σ : StaticModel}
  (x y : variable)
  (f : symbol)
  (t : TermOver BuiltinOrVar)
  :
  t <> t_over (bov_variable y) ->
  subp_compose ({[y := t]}) ({[x := t_term f [t_over (bov_variable y)]]})
  = {[x := t_term f [t]; y := t]}
.
Proof.
  unfold subp_compose.
  unfold SubP in *.
  intros Hne0.
  repeat (rewrite <- insert_empty).
  repeat (rewrite fmap_insert).
  repeat (rewrite fmap_empty).
  ltac1:(rewrite subp_app_insert0).
  {
    unfold vars_of; simpl.
    unfold vars_of; simpl.
    unfold subp_dom.
    ltac1:(rewrite dom_empty_L).
    apply disjoint_empty_r.
  }
  ltac1:(rewrite subp_app_empty').
  unfold compose.
  simpl.
  (* ltac1:(rewrite lookup_insert). *)
  rewrite map_filter_insert.
  simpl.
  rewrite map_filter_empty.
  ltac1:(case_match).
  {
    clear H.
    ltac1:(rename n into H).
    unfold subp_dom in H.
    ltac1:(rewrite not_elem_of_dom in H).
    destruct (decide (x = y)).
    {
        subst.
        rewrite lookup_insert in H.
        inversion H.
    }
    {
        rewrite lookup_insert_ne in H.
        {
            clear H.
            rewrite decide_True.
            {
                rewrite insert_union_singleton_l.
                repeat (rewrite insert_empty).
                (* ltac1:(rewrite <- assoc). *)
                rewrite (right_id ∅).
                {
                    rewrite map_filter_union.
                    {
                        rewrite map_filter_singleton.
                        simpl.
                        rewrite map_filter_singleton.
                        simpl.
                        ltac1:(case_match).
                        {
                            rewrite insert_union_singleton_l.
                            apply map_union_comm.
                            rewrite map_disjoint_singleton_l.
                            rewrite <- insert_empty.
                            rewrite lookup_insert_ne.
                            rewrite lookup_empty.
                            reflexivity.
                            ltac1:(congruence).
                        }
                        {
                            rewrite (left_id empty)>[|apply _].
                            clear H.
                            apply dec_stable in n0.
                            subst t.
                            ltac1:(contradiction Hne0).
                            reflexivity.
                        }
                    }
                    {
                        apply map_disjoint_spec.
                        intros.
                        destruct (decide (i = y)).
                        {
                            subst i.
                            rewrite <- insert_empty in H.
                            rewrite lookup_insert in H.
                            ltac1:(simplify_eq/=).
                            rewrite <- insert_empty in H0.
                            rewrite lookup_insert_ne in H0.
                            rewrite lookup_empty in H0.
                            inversion H0.
                            assumption.
                        }
                        {
                            rewrite <- insert_empty in H.
                            rewrite lookup_insert_ne in H.
                            rewrite lookup_empty in H.
                            inversion H.
                            ltac1:(congruence).
                        }
                        
                    }
                }
                {
                    apply _.
                }
            }
            {
                reflexivity.
            }
        }
        {
            ltac1:(congruence).
        }
    }
  }
  {
    clear H.
    ltac1:(rename n into H).
    apply dec_stable in H.
    unfold subp_dom in H.
    ltac1:(rewrite elem_of_dom in H).
    destruct H as [x' Hx'].
    destruct (decide (x = y)).
    {
        subst.
        rewrite lookup_insert in Hx'.
        ltac1:(simplify_eq/=).
        rewrite delete_empty.
        ltac1:(rewrite map_filter_empty).
        rewrite (left_id ∅).
        {
            rewrite decide_True.
            {
                rewrite insert_insert.
                rewrite map_filter_insert.
                simpl.
                rewrite map_filter_empty.
                reflexivity.
            }
            {
                reflexivity.
            }
        }
        {
            apply _.
        }
    }
    {
        subst.
        rewrite lookup_insert_ne in Hx'.
        {
            rewrite lookup_empty in Hx'.
            inversion Hx'.
        }
        {
            ltac1:(congruence).
        }
    }
  }
Qed.

(* 2. a={(x,f(y))}, b={(y,t)} ==> {(x,f(y)), (y, t[f(y)/x])} *)
Example subp_compose_ex2
  {Σ : StaticModel}
  (x y : variable)
  (f : symbol)
  (t : TermOver BuiltinOrVar)
  :
  t <> t_over (bov_variable x) ->
  x <> y ->
  subp_compose ({[x := t_term f [t_over (bov_variable y)]]}) ({[y := t]})
  = {[x := t_term f [t_over (bov_variable y)]; y := TermOverBoV_subst t x (t_term f [t_over (bov_variable y)])]}
.
Proof.
    unfold subp_compose.
    unfold SubP in *.
    intros Htx Hxy.
    repeat (rewrite <- insert_empty).
    do 1 (rewrite fmap_insert).
    ltac1:(rewrite subp_app_insert0).
    {
        unfold subp_dom.
        ltac1:(rewrite dom_empty_L).
        ltac1:(set_solver).
    }
    {
        ltac1:(rewrite subp_app_empty').
        unfold compose.
        rewrite map_filter_insert.
        simpl.
        ltac1:(case_match).
        {
            rewrite map_filter_empty.
            rewrite fmap_empty.
            simpl.
            repeat (rewrite insert_empty).
            rewrite insert_union_singleton_l.
            rewrite map_filter_union.
            {
                rewrite map_filter_singleton.
                simpl.
                rewrite map_filter_singleton.
                simpl.
                ltac1:(case_match); try
                reflexivity.
                clear H0.
                apply dec_stable in n0.
                rewrite (right_id empty union).
                clear H n.
                (* Search TermOverBoV_subst bov_variable. *)
            }
            {
                apply map_disjoint_spec.
                intros.
                destrict (decide (i = x)).
                {

                }
            }
            
        }
        {
            clear H.
            apply dec_stable in n.
            unfold subp_dom in n.
            ltac1:(rewrite elem_of_dom in n).
            destruct n as [x' Hx'].
            apply lookup_insert_Some in Hx'.
            destruct Hx' as [[H1 H2]|[H3 H4]].
            {
                subst.
                ltac1:(contradiction Hxy).
                reflexivity.
            }
            {
                rewrite lookup_empty in H4.
                inversion H4.
            }
        }
    }
Qed.
*)
Lemma subp_compose_correct
    {Σ : StaticModel}
    (a b : SubP)
    :
    subp_app (subp_compose a b) = (subp_app a) ∘ (subp_app b)
.
Proof.
    unfold subp_compose.
    unfold compose.
    apply functional_extensionality.
    intros p.
    revert a b.
    induction p; intros aa bb; simpl.
    {
        destruct a; simpl in *.
        { reflexivity. }
        {
            unfold subp_normalize.
            rewrite map_filter_union.
            {
              ltac1:(rewrite lookup_union).
              ltac1:(rewrite map_lookup_filter).
              unfold SubP in *.
              ltac1:(rewrite map_lookup_filter).
              ltac1:(rewrite map_lookup_filter).
              ltac1:(rewrite lookup_fmap).
              destruct (bb!!x) eqn:Hbx.
              {
                simpl.
                destruct (aa !! x) eqn:Hax.
                {
                  simpl.
                  rewrite option_guard_False.
                  { simpl.
                    destruct (decide (t_over (bov_variable x) = subp_app aa t)).
                    {
                      rewrite option_guard_False.
                      { simpl. ltac1:(congruence). }
                      { simpl. ltac1:(congruence). }
                    }
                    { rewrite option_guard_True.
                      simpl. reflexivity.
                      ltac1:(congruence).
                    }
                  }
                  {
                    intros HContra.
                    apply HContra.
                    unfold subp_dom.
                    ltac1:(rewrite elem_of_dom).
                    rewrite Hbx.
                    eexists.
                    reflexivity.
                  }
              }
              {
                simpl.
                destruct (decide (t_over (bov_variable x) = subp_app aa t)).
                {
                  rewrite option_guard_False.
                  { simpl. ltac1:(congruence). }
                  { simpl. ltac1:(congruence). }
                }
                {
                  rewrite option_guard_True.
                  { simpl. reflexivity. }
                  { ltac1:(congruence). }
                }
              }
              }
              {
                simpl.
                destruct (aa!!x) eqn:Hax.
                { 
                  ltac1:(rewrite Hax).
                  simpl.
                  rewrite option_guard_True.
                  {
                    simpl.
                    destruct (decide (t = t_over (bov_variable x))).
                    {
                      subst.
                      rewrite option_guard_False.
                      { simpl. reflexivity. }
                      { ltac1:(congruence). }
                    }
                    {
                      rewrite option_guard_True.
                      { simpl. reflexivity. }
                      { ltac1:(congruence). }
                    }
                  }
                  {
                    unfold subp_dom.
                    ltac1:(rewrite elem_of_dom).
                    rewrite Hbx.
                    intros [? H].
                    inversion H.
                  }
                }
                {
                  simpl.
                  ltac1:(rewrite Hax).
                  reflexivity.
                }
              }
            }
            {
              apply map_disjoint_spec.
              intros i x' y' Hx' Hy'.
              rewrite map_lookup_filter in Hx'.
              rewrite lookup_fmap in Hy'.
              destruct (aa !! i) eqn:Hai.
              {
                simpl in *.             
                destruct (bb !! i) eqn:Hbi.
                {
                  simpl in *.
                  ltac1:(rewrite Hai in Hx').
                  simpl in *.
                  ltac1:(rewrite Hbi in Hy').
                  simpl in *.
                  ltac1:(simplify_eq/=).
                  ltac1:(simplify_option_eq).
                  unfold subp_dom in *.
                  apply H.
                  ltac1:(rewrite elem_of_dom).
                  ltac1:(rewrite Hbi).
                  eexists.
                  reflexivity.
                }
                {
                  ltac1:(rewrite Hai in Hx').
                  simpl in Hx'.
                  ltac1:(rewrite Hbi in Hy').
                  simpl in Hy'.
                  inversion Hy'.
                }
              }
              {
                ltac1:(rewrite Hai in Hx').
                simpl in Hx'.
                inversion Hx'.
              }
            }
         }
    }
    {
        apply f_equal.
        ltac1:(replace (map) with (@fmap list list_fmap) by reflexivity).
        rewrite Forall_forall in H.
        rewrite <- list_fmap_compose.
        apply list_fmap_ext.
        intros i x Hix.
        apply H.
        rewrite elem_of_list_lookup.
        exists i.
        exact Hix.
    }
Qed.

Lemma subp_compose_assoc
  {Σ : StaticModel}
  (a b c : SubP)
:
    subp_is_normal a ->
    subp_is_normal b ->
    subp_is_normal c ->
    subp_compose (subp_compose a b) c = subp_compose a (subp_compose b c)
.
Proof.
    intros Hnormala.
    intros Hnormalb.
    intros Hnormalc.
    unfold SubP in *.
    unfold subp_compose.
    unfold subp_dom.
    unfold SubP in *.
    unfold subp_normalize.
    
    
    apply map_eq.
    {
      intros i.
      lazy_match! goal with
      | [|- ?l = _] =>
        destruct ($l) eqn:Heql
      end.
      {
        symmetry.
        ltac1:(rewrite map_lookup_filter in Heql).
        rewrite bind_Some in Heql.
        destruct Heql as [t' [H1t' H2t']].
        simpl in *.
        rewrite map_lookup_filter.
        rewrite bind_Some.
        simpl in *.
        ltac1:(simplify_option_eq).
        exists t.
        split.
        {
          rewrite lookup_union in H1t'.
          rewrite union_Some in H1t'.
          rewrite lookup_union.
          rewrite union_Some.
          rewrite map_lookup_filter in H1t'.
          rewrite map_lookup_filter.
          rewrite bind_Some in H1t'.
          rewrite bind_Some.
          simpl in *.
          destruct H1t' as [H1t|H1t].
          {
            destruct H1t as [x [H1x H2x]].
            rewrite map_lookup_filter in H1x.
            rewrite bind_Some in H1x.
            destruct H1x as [y [H1y H2y]].
            rewrite bind_Some in H2y.
            destruct H2y as [pf [_ ?]].
            simpl in *.
            apply (inj Some) in H1.
            subst y.
            rewrite lookup_union in H1y.
            rewrite map_lookup_filter in H1y.
            rewrite lookup_fmap in H1y.
            rewrite union_Some in H1y.
            simpl in *.
            destruct (a !! i) eqn:Hai.
            {
              rewrite bind_Some in H2x.
              destruct H2x as [? [_ Hxt]].
              apply (inj Some) in Hxt.
              subst x.
              simpl.
              setoid_rewrite bind_Some.
              lazy_match! Constr.type (Control.hyp @H1y) with
              | (_ \/ ?rr) => destruct (classic $rr) as [Hyes|Hno]
              end.
              {              
                destruct H1y as [H1y|H1y].
                {
                  rewrite bind_Some in H1y.
                  destruct H1y as [? [_ Htmp]].
                  rewrite bind_Some in Htmp.
                  destruct Htmp as [? [_ Htmp]].
                  apply (inj Some) in Htmp.
                  subst t.
                  apply not_elem_of_dom_1 in x1 as Hb.
                  apply not_elem_of_dom_1 in x0 as Hc.
                  rewrite lookup_fmap.
                  rewrite map_lookup_filter.
                  setoid_rewrite bind_Some.
                  setoid_rewrite bind_Some.
                  simpl.
                  setoid_rewrite lookup_union.
                  setoid_rewrite map_lookup_filter.
                  rewrite Hb.
                  simpl.
                  setoid_rewrite lookup_fmap.
                  rewrite Hc.
                  simpl.
                  destruct Hyes as [H1y H2y].
                  simpl in *.
                  clear H1y.
                  rewrite Hb in H2y.
                  simpl in H2y.
                  inversion H2y.
               }
               {
                  destruct H1y as [H1 Htmp].
                  simpl in H1.
                  clear H1.
                  ltac1:(setoid_rewrite bind_None).
                  destruct (b !! i) eqn:Hbi.
                  {
                    simpl in *.
                    ltac1:(simplify_eq/=).
                    destruct Hyes as [H1 H2].
                    clear H1 H2.
                      apply not_elem_of_dom_1 in x0 as Hci.
                      setoid_rewrite lookup_fmap.
                      setoid_rewrite map_lookup_filter.
                      setoid_rewrite bind_Some.
                      setoid_rewrite bind_Some.
                      setoid_rewrite bind_Some.
                      setoid_rewrite lookup_union.
                      setoid_rewrite lookup_fmap.
                      setoid_rewrite Hci.
                      simpl.
                      setoid_rewrite (right_id None union).
                      setoid_rewrite map_lookup_filter.
                      setoid_rewrite bind_Some.
                      setoid_rewrite bind_Some.
                      setoid_rewrite Hbi.
                    simpl.
                    right.
                    split.
                    left.
                    unfold guard_or.
                    ltac1:(case_match; try reflexivity).
                    ltac1:(exfalso; clear H1; rename n into H1).
                    rewrite elem_of_dom in H1.
                    rewrite map_lookup_filter in H1.
                    rewrite lookup_union in H1.
                    rewrite lookup_fmap in H1.
                    rewrite Hci in H1.
                    simpl in H1.
                    rewrite map_lookup_filter in H1.
                    rewrite Hbi in H1.
                    simpl in H1.
                    apply H1.
                    eexists.
                    rewrite bind_Some.
                    eexists.
                    rewrite bind_Some.
                    rewrite (right_id None union).
                    split.
                    {
                      erewrite option_guard_True_pi. 
                      { reflexivity. }
                      { intros pfa pfb. apply proof_irrelevance. }
                    }
                    {
                      ltac1:(unshelve(eexists)).
                      {
                        unfold subp_is_normal in Hnormalb.
                        rewrite <- Hnormalb in Hbi.
                        unfold subp_normalize in Hbi.
                        rewrite map_lookup_filter in Hbi.
                        rewrite bind_Some in Hbi.
                        destruct Hbi as [bv [H1bv H2bv]].
                        rewrite bind_Some in H2bv.
                        simpl in H2bv.
                        destruct H2bv as [? [_ ?]].
                        ltac1:(congruence).
                      }
                      {
                        split>[|reflexivity].
                        apply option_guard_True_pi.
                        intros pfa pfb.
                        apply proof_irrelevance.
                      }
                    }
                    {
                      exists t1.
                      split>[|reflexivity].
                      exists t1.
                      (repeat split); try reflexivity.
                      {
                        exists t1.
                        split>[reflexivity|].
                        exists x0.
                        split>[|reflexivity].
                        apply option_guard_True_pi.
                        intros pfa pfb.
                        apply proof_irrelevance.
                      }
                      {
                        ltac1:(unshelve(eexists)).  
                        {
                          intros HContra.
                          subst t1.
                          unfold subp_is_normal in Hnormalb.
                          rewrite <- Hnormalb in Hbi.
                          unfold subp_normalize in Hbi.
                          rewrite map_lookup_filter in Hbi.
                          rewrite bind_Some in Hbi.
                          destruct Hbi as [p [H1p H2p]].
                          rewrite bind_Some in H2p.
                          simpl in H2p.
                          destruct H2p as [? [_ ?]].
                          ltac1:(simplify_eq/=).
                        }
                        {
                          split>[|reflexivity].
                          apply option_guard_True_pi.
                          intros pfa pfb.
                          apply proof_irrelevance.
                        }
                      }
                    } 
                  }
                  {
                    destruct Hyes as [H1 H2].
                    inversion H2.
                  }
                }
              }
              {
                apply not_and_or in Hno.
                destruct (b !! i) eqn:Hbi.
                {
                  simpl in *.
                  destruct H1y as [H1y|H1y].
                  {
                    rewrite bind_Some in H1y.
                    destruct H1y as [? [_ ?]].
                    apply not_elem_of_dom_1 in x.
                    ltac1:(congruence).
                  }
                  {
                    destruct H1y as [H1y Heq].
                    ltac1:(simplify_eq/=).
                    clear H1y.
                    destruct Hno as [Hno|Hno].
                    {
                      apply not_eq_None_Some in Hno.
                      destruct Hno as [q Hq].
                      rewrite bind_Some in Hq.
                      destruct Hq as [? [_ Htmp]].
                      ltac1:(simplify_eq/=).
                      apply not_elem_of_dom_1 in x.
                      ltac1:(congruence).
                    }
                    {
                      ltac1:(contradiction Hno).
                      reflexivity.
                    }
                  }
                }
                {
                  simpl in *.
                  destruct H1y as [H1y|H1y],
                      Hno as [Hno|Hno].
                  {
                    rewrite bind_Some in H1y.
                    destruct H1y as [? [_ Htmp]].
                    ltac1:(simplify_eq/=).
                    apply not_eq_None_Some in Hno.
                    destruct Hno as [q Hq].
                    rewrite bind_Some in Hq.
                    destruct Hq as [? [_ ?]].
                    ltac1:(simplify_eq/=).
                    apply not_elem_of_dom_1 in x0 as Hci.
                    setoid_rewrite lookup_fmap.
                    setoid_rewrite map_lookup_filter.
                    simpl.
                    setoid_rewrite bind_Some.
                    setoid_rewrite bind_Some.
                    setoid_rewrite lookup_union.
                    setoid_rewrite lookup_fmap.
                    rewrite Hci.
                    simpl.
                    left.
                    exists q.
                    split>[reflexivity|].
                    ltac1:(unshelve(eexists)).
                    {
                      rewrite elem_of_dom.
                      rewrite map_lookup_filter.
                      intros [p Hp].
                      rewrite bind_Some in Hp.
                      destruct Hp as [o Ho].
                      rewrite lookup_union in Ho.
                      rewrite lookup_fmap in Ho.
                      destruct Ho as [H1o H2o].
                      rewrite map_lookup_filter in H1o.
                      rewrite Hci in H1o.
                      simpl in *.
                      rewrite Hbi in H1o.
                      simpl in H1o.
                      inversion H1o.
                    }
                    {
                      split>[|reflexivity].
                      apply option_guard_True_pi.
                      intros pfa pfb.
                      apply proof_irrelevance.
                    }
                  }
                  {
                    rewrite bind_Some in H1y.
                    clear Hno.
                    destruct H1y as [? [_ ?]].
                    ltac1:(simplify_eq/=).
                    apply not_elem_of_dom_1 in x0 as Hci.
                    setoid_rewrite lookup_fmap.
                    setoid_rewrite map_lookup_filter.
                    setoid_rewrite bind_Some.
                    setoid_rewrite bind_Some.
                    setoid_rewrite bind_Some.
                    setoid_rewrite bind_None.
                    setoid_rewrite lookup_union.
                    setoid_rewrite lookup_fmap.
                    rewrite Hci.
                    simpl.
                    setoid_rewrite map_lookup_filter.
                    rewrite Hbi.
                    simpl.
                    left.
                    exists t.
                    split>[reflexivity|].
                    ltac1:(unshelve(eexists)).
                    {
                      apply not_elem_of_dom_2.
                      rewrite map_lookup_filter_None.
                      rewrite lookup_union.
                      rewrite lookup_fmap.
                      rewrite Hci.
                      simpl.
                      rewrite (right_id None union).
                      setoid_rewrite (right_id None union).
                      rewrite map_lookup_filter.
                      rewrite Hbi.
                      simpl.
                      left.
                      reflexivity.
                    }
                    {
                      split>[|reflexivity].
                      apply option_guard_True_pi.
                      intros pfa pfb.
                      apply proof_irrelevance.
                    }
                  }
                  {
                    destruct H1y as [? H1y].
                    inversion H1y.
                  }
                  {
                    destruct H1y as [? H1y].
                    inversion H1y.
                  }
                }
              }
            }
            {
              simpl in *.
              right.
              split>[reflexivity|].
              destruct H1y as [H1y|[H1y H2y]].
              {
                inversion H1y.
              }
              {
                destruct (b !! i) eqn:Hbi.
                {
                  simpl in *.
                  apply (inj Some) in H2y.
                  subst x.
                  simpl in *.
                  rewrite lookup_fmap.
                  rewrite map_lookup_filter.
                  simpl.
                  rewrite fmap_Some.
                  rewrite bind_Some in H2x.
                  destruct H2x as [pf1 [_ H1]].
                  apply (inj Some) in H1.
                  subst t.
                  exists t0.
                  split>[|reflexivity].
                  rewrite bind_Some.
                  setoid_rewrite lookup_union.
                  setoid_rewrite lookup_fmap.
                  apply not_elem_of_dom_1 in pf1 as pf1'.
                  rewrite pf1'.
                  simpl.
                  setoid_rewrite (right_id None union).
                  setoid_rewrite map_lookup_filter.
                  simpl.
                  rewrite Hbi.
                  simpl.
                  exists t0.
                  split.
                  {
                    rewrite bind_Some.
                    exists pf1.
                    split>[|reflexivity].
                    apply option_guard_True_pi.
                    intros pf8 pf9.
                    apply proof_irrelevance.
                  }
                  {
                    rewrite bind_Some.
                    ltac1:(unshelve(eexists)).
                    {
                      intros HContra.
                      subst t0.
                      simpl in *.
                      ltac1:(rewrite Hai in H).
                      ltac1:(contradiction H).
                      reflexivity.
                    }
                    {
                      split>[|reflexivity].
                      apply option_guard_True_pi.
                      intros pfa pfb.
                      apply proof_irrelevance.
                    }
                  }
                  }
                  {
                    simpl in H2y.
                    inversion H2y.
                  }
                }
              }
            }
            {
              destruct H1t as [H1t H2t].
              rewrite bind_None in H1t.
              rewrite map_lookup_filter in H1t.
              rewrite bind_None in H1t.
              rewrite lookup_union in H1t.
              rewrite lookup_fmap in H1t.
              rewrite map_lookup_filter in H1t.
              setoid_rewrite lookup_fmap.
              setoid_rewrite bind_None.
              destruct (a !! i) eqn:Hai.
              {
                rewrite map_lookup_filter.
                simpl.
                rewrite lookup_union.
                rewrite lookup_fmap.
                rewrite map_lookup_filter.
                rewrite fmap_Some.
                setoid_rewrite bind_Some.
                setoid_rewrite bind_Some.
                destruct (b !! i) eqn:Hbi.
                {
                  simpl.
                  destruct (c !! i) eqn:Hci.
                  {
                    simpl.
                    rewrite lookup_fmap in H2t.
                    rewrite Hci in H2t.
                    simpl in H2t.
                    ltac1:(simplify_eq/=).
                    rewrite union_None in H1t.
                    destruct H1t as [[H1t|H1t]|H1t].
                    {
                      destruct H1t as [? H1t].
                      inversion H1t.
                    }
                    {
                      destruct H1t as [p [H1p H2p]].
                      rewrite union_Some in H1p.
                      rewrite bind_Some in H1p.
                      destruct H1p as [H1p|H1p].
                      {
                        destruct H1p as [H1p [_ ?]].
                        apply not_elem_of_dom_1 in H1p.
                        ltac1:(congruence).
                      }
                      {
                        destruct H1p as [_ H1p].
                        ltac1:(simplify_eq/=).
                        destruct (decide (subp_app b t2 = t_over (bov_variable i))).
                        {
                          left.
                          exists t0.
                          split>[reflexivity|].
                          remember (subp_compose a b) as ab.
                          assert(Heqab' := Heqab).
                          unfold subp_compose in Heqab'.
                          unfold subp_normalize in Heqab'.
                          setoid_rewrite <- Heqab.
                          clear Heqab'.
                          subst ab.
                          rewrite subp_compose_correct.
                          unfold compose.
                          rewrite e.
                          simpl.
                          ltac1:(rewrite Hai).
                          ltac1:(unshelve(eexists)).
                          {
                            rewrite elem_of_dom.
                            rewrite map_lookup_filter.
                            simpl.
                            rewrite lookup_union.
                            rewrite map_lookup_filter.
                            rewrite Hbi.
                            simpl.
                            rewrite option_guard_False.
                            { simpl. rewrite lookup_fmap. rewrite Hci. simpl.
                              rewrite option_guard_False.
                              { intros [u Hu].
                                simpl in Hu.
                                inversion Hu.
                              }
                              { ltac1:(congruence). }
                            }
                            rewrite elem_of_dom.
                            rewrite Hci.
                            intros Hu. apply Hu. exists t2. reflexivity.
                          }
                          {
                            split.
                            {
                              apply option_guard_True_pi.
                              intros pfa pfb.
                              apply proof_irrelevance.
                            }
                            { reflexivity. }
                          }
                        }
                        {
                          right.
                          split.
                          { right.
                            exists t0.
                            split>[reflexivity|].
                            rewrite option_guard_False.
                            { simpl. reflexivity. }
                            {
                              intros HC. apply HC. clear HC.
                              rewrite elem_of_dom.
                              rewrite map_lookup_filter.
                              rewrite lookup_union.
                              rewrite map_lookup_filter.
                              rewrite Hbi.
                              simpl.
                              rewrite lookup_fmap.
                              rewrite Hci.
                              simpl.
                              rewrite option_guard_False.
                              { simpl. rewrite option_guard_True.
                                eexists. reflexivity.
                                ltac1:(congruence).
                              }
                              {
                                rewrite elem_of_dom.
                                intros HH. apply HH. clear HH.
                                rewrite Hci.
                                eexists. reflexivity.
                              }
                          }  
                        }
                        {
                          exists (subp_app b t2).
                          split.
                          {
                            exists (subp_app b t2).
                            repeat split. 
                            {
                              rewrite option_guard_False.
                              { simpl. reflexivity. }
                              {
                                rewrite elem_of_dom.
                                rewrite Hci.
                                intros HContra. apply HContra.
                                exists t2.
                                reflexivity.
                              }
                            }
                            {
                              apply nesym in n.
                              exists n.
                              split>[|reflexivity].
                              apply option_guard_True_pi.
                              intros pfa pfb. apply proof_irrelevance.
                            }
                          }
                          {
                            ltac1:(replace (subp_app a (subp_app b t2))
                              with (((subp_app a) ∘ (subp_app b)) t2)
                              by reflexivity).
                           rewrite <- subp_compose_correct.
                           reflexivity.
                          }
                        }
                      }
                    }
                  } {
                      destruct H1t as [p [H1p H2p]].
                      rewrite bind_Some in H1p.
                      destruct H1p as [q [H1q H2q]].
                      rewrite bind_Some in H2q.
                      destruct H2q as [Hq [_ ?]].
                      ltac1:(simplify_eq/=).
                      rewrite union_Some in H1q.
                      destruct H1q as [H1q|H1q].
                      {
                        rewrite bind_Some in H1q.
                        destruct H1q as [Hib' [_ ?]].
                        apply not_elem_of_dom_1 in Hib'.
                        ltac1:(congruence).
                      }
                      {
                        destruct H1q as [_ H1q].
                        ltac1:(simplify_eq/=).
                        (* I think that [H] is just a tautology.
                         *)
                        clear H.
                        
                        destruct (decide (i ∈ dom (filter (λ kv : variable * TermOver' BuiltinOrVar, t_over (bov_variable kv.1) ≠ kv.2)
                   (filter (λ kv : variable * TermOver BuiltinOrVar, kv.1 ∉ dom c) b ∪ (subp_app b <$> c))))) as [Hin|Hnotin].
                        {
                          rewrite elem_of_dom in Hin.
                          destruct Hin as [p Hp].
                          rewrite map_lookup_filter in Hp.
                          rewrite bind_Some in Hp.
                          destruct Hp as [q [H1q H2q]].
                          rewrite lookup_union in H1q.
                          rewrite map_lookup_filter in H1q.
                          rewrite lookup_fmap in H1q.
                          rewrite Hbi in H1q.
                          simpl in H1q.
                          rewrite union_Some in H1q.
                          destruct H1q as [H1q|H1q].
                          {
                            rewrite bind_Some in H1q.
                            destruct H1q as [? [_ ?]].
                            ltac1:(simplify_eq/=).
                            apply elem_of_dom_2 in Hci.
                            ltac1:(contradiction).
                          }
                          {
                            destruct H1q as [_ H1q].
                            rewrite Hci in H1q.
                            simpl in H1q.
                            ltac1:(simplify_eq/=).
                            clear H2p.
                            rewrite bind_Some in H2q.
                            destruct H2q as [? [_ ?]].
                            ltac1:(simplify_eq/=).
                            right.
                            split.
                            {
                              right.
                              exists t0.
                              split>[reflexivity|].
                              rewrite bind_None.
                              
                              left.
                              Search guard None.
                              rewrite option_guard_False.
                              { reflexivity. }
                              rewrite elem_of_dom.
                              intros HContra.
                              apply HContra.
                              rewrite map_lookup_filter.
                              rewrite lookup_union.
                              rewrite map_lookup_filter.
                              rewrite lookup_fmap.
                              rewrite Hbi.
                              simpl.
                              rewrite Hci.
                              simpl.
                              rewrite option_guard_False.
                              { simpl. rewrite option_guard_True. eexists. reflexivity.
                                assumption.
                              }
                              rewrite elem_of_dom.
                              rewrite Hci.
                              intros HH. apply HH. eexists. reflexivity.
                            }
                            {
                              exists (subp_app b t2).
                              ltac1:(replace (subp_app a (subp_app b t2)) with ((compose (subp_app a) (subp_app b)) t2) by reflexivity).
                              rewrite <- subp_compose_correct.
                              unfold subp_compose.
                              unfold subp_normalize.
                              split>[|reflexivity].
                              exists (subp_app b t2).
                              split.
                              {
                                rewrite option_guard_False.
                                simpl.
                                reflexivity.
                                intros HC. apply HC. clear HC.
                                rewrite elem_of_dom.
                                rewrite Hci.
                                exists t2. reflexivity.
                              }
                              {
                                exists x.
                                split>[|reflexivity].
                                apply option_guard_True_pi.
                                intros pfa pfb.
                                apply proof_irrelevance.
                              }
                            }
                          }
                        }
                        {
                          destruct (decide (t_over (bov_variable i) = subp_app b t2)).
                          {
                            left.
                            exists t0.
                            split>[reflexivity|].
                            exists Hnotin.
                            split.
                            {
                              apply option_guard_True_pi.
                              intros pfa pfb. apply proof_irrelevance.
                            }
                            {
                              apply f_equal.
                              lazy_match! goal with
                              | [|- _ = ?r] =>
                                assert(Hr: $r = (subp_app (subp_compose a b) t2))
                              end.
                              {
                                reflexivity.
                              }
                              rewrite Hr. clear Hr.
                              rewrite subp_compose_correct.
                              unfold compose.
                              rewrite <- e.
                              simpl.
                              ltac1:(rewrite Hai).
                              reflexivity.
                            }
                          }
                          {
                            ltac1:(exfalso).
                            apply Hnotin. clear Hnotin.
                            rewrite elem_of_dom.
                            rewrite map_lookup_filter.
                            rewrite lookup_union.
                            rewrite lookup_fmap.
                            rewrite map_lookup_filter.
                            rewrite Hbi.
                            simpl.
                            rewrite Hci.
                            rewrite option_guard_False.
                            {
                              simpl.
                              rewrite option_guard_True.
                              eexists. reflexivity.
                              ltac1:(congruence).
                            }
                            {
                              intros HH. apply HH. clear HH.
                              rewrite elem_of_dom.
                              rewrite Hci. eexists. reflexivity.
                            }
                          }
                        }
                        
                    }
                }
              }
              {
              
                simpl in *.
                rewrite lookup_fmap in H2t.
                rewrite Hci in H2t.
                simpl in H2t.
                inversion H2t.
              }
            }
            {
                simpl in *.
                rewrite lookup_fmap in H2t.
                destruct (c !! i) eqn:Hci.
                {
                  simpl in H2t.
                  ltac1:(simplify_eq/=).
                  destruct (decide (subp_app b t1 = t_over (bov_variable i))) as [Hiyes|Hino].
                  {
                    left.
                    exists t0.
                    split>[reflexivity|].
                    simpl.
                    remember (subp_compose a b) as ab.
                    assert(Hnice := Heqab).
                    unfold subp_compose in Heqab.
                    unfold subp_normalize in Heqab.
                    setoid_rewrite <- Heqab.
                    setoid_rewrite Hnice.
                    rewrite subp_compose_correct.
                    unfold compose.
                    rewrite Hiyes.
                    simpl.
                    ltac1:(rewrite Hai).
                    ltac1:(unshelve(eexists)).
                    {
                      rewrite elem_of_dom.
                      intros [p Hp].
                      rewrite map_lookup_filter in Hp.
                      rewrite lookup_union in Hp.
                      rewrite lookup_fmap in Hp.
                      simpl in *.
                      rewrite Hci in Hp.
                      rewrite map_lookup_filter in Hp.
                      rewrite Hbi in Hp.
                      simpl in Hp.
                      rewrite bind_Some in Hp.
                      destruct Hp as [? [_ ?]].
                      ltac1:(simplify_eq/=).
                    }
                    {
                      split>[|reflexivity].
                      apply option_guard_True_pi.
                      intros ? ?.
                      apply proof_irrelevance.
                    }
                  }
                  {
                    right.
                    split.
                    {
                      right.
                      exists t0.
                      split>[reflexivity|].
                      rewrite option_guard_False.
                      { reflexivity. }
                      intros HH. apply HH. clear HH.
                      rewrite elem_of_dom.
                      rewrite map_lookup_filter.
                      simpl.
                      rewrite lookup_union.
                      rewrite map_lookup_filter.
                      rewrite Hbi.
                      simpl.
                      rewrite lookup_fmap.
                      rewrite Hci.
                      simpl.
                      rewrite option_guard_True.
                      { eexists. reflexivity. }
                      {
                        ltac1:(congruence).
                      }
                    }
                    {
                      exists (subp_app b t1).
                      ltac1:(replace(subp_app a (subp_app b t1)) with (((subp_app a) ∘ (subp_app b)) t1) by reflexivity).
                      rewrite <- subp_compose_correct.
                      split>[|reflexivity].
                      eexists.
                      split>[reflexivity|].
                      apply nesym in Hino.
                      exists Hino.
                      split>[|reflexivity].
                      apply option_guard_True_pi.
                      intros pfa pfb.
                      apply proof_irrelevance.
                    }
                  }
                }
                {
                  simpl in H2t.
                  inversion H2t.
                }
            }
          }
          { 
            destruct (b !! i) eqn:Hbi.
            {
              simpl in *.
              destruct (c !! i) eqn:Hci.
              {
                simpl in H2t.
                ltac1:(simplify_eq/=).
                destruct (decide (t_over (bov_variable i) = subp_app b t1)).
                {
                  admit.
                }
                {
                  right. split. left. reflexivity.
                  rewrite map_lookup_filter.
                  simpl.
                  rewrite fmap_Some.
                  setoid_rewrite lookup_union.
                  setoid_rewrite lookup_fmap.
                  setoid_rewrite map_lookup_filter.
                  
                  exists (subp_app b t1).
                  split.
                  {
                    simpl.
                    rewrite Hbi.
                    simpl.
                    rewrite Hci.
                    rewrite option_guard_False.
                    { simpl. rewrite option_guard_True. reflexivity.
                      ltac1:(congruence).
                    }
                    {
                      intros L. apply L. clear L.
                      rewrite elem_of_dom.
                      rewrite Hci.
                      exists t1. reflexivity.
                    } 
                  }
                  {
                    fold (compose (subp_app a) (subp_app b) t1).
                    rewrite <- subp_compose_correct.
                    symmetry.
                    unfold subp_compose.
                    unfold subp_normalize.
                    simpl in *.
                    rewrite lookup_fmap in H2t.
                    rewrite Hci in H2t.
                    simpl in H2t.
                    ltac1:(simplify_eq/=).
                    reflexivity.
                  }
                }
              }
              { simpl in H2t. 
                rewrite lookup_fmap in H2t.
                rewrite Hci in H2t.
                simpl in H2t.            
                inversion H2t.                
              }
            }
            {
              simpl in H2t.
              rewrite lookup_fmap in H2t.
              destruct (c !! i) eqn:Hci.
              {
                simpl in *.
                ltac1:(simplify_eq/=).
                destruct (decide (t_over (bov_variable i) = subp_app b t0)).
                {
                  remember (subp_app (subp_compose a b) t0) as nice.
                  assert (Hnice := Heqnice).
                  unfold subp_compose in Hnice.
                  unfold subp_normalize in Hnice.
                  ltac1:(setoid_rewrite <- Hnice in H0).
                  rewrite Heqnice in H0.
                  rewrite subp_compose_correct in H0.
                  unfold compose in H0. simpl in H0.
                  rewrite <- e in H0.
                  simpl in H0.
                  ltac1:(rewrite Hai in H0).
                  simpl in H0.
                  ltac1:(contradiction H0).
                  reflexivity.
                }
                {
                  right.
                  split. left. reflexivity.
                  rewrite map_lookup_filter.
                  rewrite fmap_Some.
                  simpl.
                  setoid_rewrite bind_Some.
                  exists (subp_app b t0).
                  split.
                  {
                    exists (subp_app b t0).
                    split.
                    {
                      rewrite lookup_union.
                      rewrite map_lookup_filter.
                      rewrite Hbi.
                      simpl.
                      rewrite lookup_fmap.
                      rewrite Hci.
                      simpl.
                      reflexivity.
                    }
                    {
                      rewrite option_guard_True.
                      reflexivity.
                      ltac1:(congruence).
                    }
                  }
                  {
                    fold (compose (subp_app a) (subp_app b) t0).
                    rewrite <- subp_compose_correct.
                    reflexivity.
                  }
                }
              }
              {
                simpl in *.
                inversion H2t.
              }
            }
          }
        }
       }
       {
        rewrite option_guard_True.
        reflexivity.
        ltac1:(congruence).
       }
     }
     {
        (* UFF, now the second inclusion *)
        symmetry.
        rewrite map_lookup_filter in Heql.
        rewrite lookup_union in Heql.
        rewrite map_lookup_filter in Heql.
        rewrite lookup_fmap in Heql.
        rewrite map_lookup_filter in Heql.
        rewrite lookup_union in Heql.
        simpl in Heql.
        rewrite lookup_fmap in Heql.
        rewrite map_lookup_filter in Heql.
        simpl in Heql.
        ltac1:(rewrite !(map_lookup_filter,lookup_union,lookup_fmap)).
        destruct (a !! i) eqn:Hai, (b !! i) eqn:Hbi, (c !! i) eqn:Hci;
          simpl in *;
            assert(Hai' := Hai);
            assert(Hbi' := Hbi);
            assert(Hci' := Hci);
            try (apply elem_of_dom_2 in Hai');
            try (apply elem_of_dom_2 in Hbi');
            try (apply elem_of_dom_2 in Hci');
            try (apply not_elem_of_dom_1 in Hai');
            try (apply not_elem_of_dom_1 in Hbi');
            try (apply not_elem_of_dom_1 in Hci');
            (repeat ((repeat (rewrite option_guard_decide));(repeat (rewrite option_guard_decide in Heql));ltac1:((repeat case_match); simplify_eq/=; simpl in *; try reflexivity)); try (solve [ltac1:(contradiction)]));
            try reflexivity;
            repeat (match! goal with
            | [h: decide _ = _ |- _] => clear $h
            end).

        (* The above worked *)    

        assert(Hlem: forall x m t, t_over (bov_variable x) = subp_app m t -> exists y, t = t_over (bov_variable y)).
        {
          intros x' m' t' HH.
          destruct t'; simpl in HH.
          {           destruct a0; simpl in HH.
            inversion HH.
            exists x. reflexivity.
          }
          { inversion HH. }
        }

        Check guard.

        repeat (try (match! goal with
        | [x : variable, h : (forall (_ : TermOver BuiltinOrVar), _) |- _] => let y := Control.hyp x in let h2 := Control.hyp h in 
            let myf := (Fresh.in_goal ident:(h)) in
            assert ($myf := $h2 constr:(t_over (bov_variable $y)))
        | [x : (TermOver BuiltinOrVar), h : (forall (_ : TermOver BuiltinOrVar), _) |- _] => let y := Control.hyp x in let h2 := Control.hyp h in  let my := (Fresh.in_goal ident:(y)) in remember (t_over (bov_variable $y)) as $my;
           apply $h2 in $h as $my
        | [h: _ ∉ (dom _) |- _] => apply not_elem_of_dom_1 in $h
        | [h: context [guard _] |- _] => rewrite option_guard_decide in $h
        | [h1: (?m !! ?k = Some _), h2: context [?m !! ?k] |- _ ] => let h := Control.hyp h1 in rewrite $h in $h2
        | [h1: (?m !! ?k = None), h2: context [?m !! ?k] |- _ ] => let h := Control.hyp h1 in rewrite $h in $h2
        | [h: context [(union _ _) !! _ = _] |- _]  => setoid_rewrite lookup_union in $h
        | [h: context [(union _ _) = None] |- _]  => setoid_rewrite union_None in $h
        | [h: context [(union _ _) = Some _] |- _]  => setoid_rewrite union_Some in $h
        | [h: context[(filter _ _) !! _ = Some _] |- _] => setoid_rewrite map_lookup_filter in $h
        | [h: context[(filter _ _) !! _ = None] |- _] => setoid_rewrite map_lookup_filter_None in $h
        | [h: context[(_ <$> _) !! _ = _] |- _] => setoid_rewrite lookup_fmap in $h
        | [h: decide _ = _ |- _] => clear $h
        | [h: ~ (~ _) |- _] => apply dec_stable in $h
        | [h: union _ _ = None |- _] => apply union_None in $h
        | [h: _ <$> _ = None |- _] => apply fmap_None in $h
        | [h: (t_over (bov_variable _) = subp_app _ _) |- _] => apply Hlem in $h
        | [h: (ex _) |- _] => Std.destruct false [({Std.indcl_arg:=Std.ElimOnIdent(h); Std.indcl_eqn:=None; Std.indcl_as:=None; Std.indcl_in:=None})] None
        | [h: (right _ = right _) |- _] => clear $h
        | [h: (forall _, _), a:_ |- _] => let f := ltac1:(ra rb|- learn_hyp (ra rb)) in f (Ltac1.of_constr (Control.hyp h)) (Ltac1.of_constr (Control.hyp a))
        (*| [h: (?p -> _) |- _] => let hmy := (Fresh.in_goal ident:(my)) in try ((assert ($hmy: $p)>[ltac1:(tauto)|]); let h2 := Control.hyp h in apply $h2 in $hmy; clear $h)*)
        end); ltac1:(destruct_and?; destruct_or?; try congruence; (repeat case_match); simplify_eq/=); simpl in *;ltac1:(try tauto))
      .
      
      lazy_match! goal with
        | [x : variable, h : (forall (_ : TermOver BuiltinOrVar), _) |- _] => let y := Control.hyp x in let h2 := Control.hyp h in  let my := (Fresh.in_goal ident:(y)) in remember (t_over (bov_variable $y)) as $my;
            let myf := (Fresh.in_goal ident:(h)) in
            let my2 := Control.hyp my in
            assert ($myf := $h2 $my2);
            subst $my
       end.

        (lazy_match! goal with
        | [x : variable, h : (forall (_ : TermOver BuiltinOrVar), _) |- _] => let y := Control.hyp x in let h2 := Control.hyp h in  let my := (Fresh.in_goal ident:(y)) in remember (t_over (bov_variable $y)) as $my;
          let myf := (Fresh.in_goal ident:(h)) in
            let my2 := Control.hyp my in
            assert ($myf := $h2 $my2)
        end).
      specialize(n0 (t_over (bov_variable x)) ltac:(tauto)).
     Search (None = Some _).
     ltac1:(tauto).
     setoid_rewrite Hbi in n0.
     rewrite union_None in n0.
     
     setoid_rewrite lookup_union in n0.
     setoid_rewrite map_lookup_filter in n0.
     setoid_rewrite lookup_fmap in n0.
     simpl in n0.
     rewrite Hbi in n0.
     simpl in n0.
     setoid_rewrite option_guard_False in n0>[|ltac1:(set_solver)].
     simpl in n0.
     setoid_rewrite Hci in n0.
     simpl in n0.
     setoid_rewrite (left_id None union) in n0.
     specialize (n0 _ eq_refl).
     apply dec_stable in n0.
     rewrite H in n0.
     ltac1:(simplify_eq/=).
     specialize (
     Unset Printing Notations.

                    
        

        Search (_ <$> _ = None).
        ltac1:(rewrite_strat (topdown _)).
        apply not_elem_of_dom_1  
        Search dom filter.
     }
Qed.

(* 
Lemma subp_union_is_compose__sometimes
  {Σ : StaticModel}
  (a b : gmap variable (TermOver BuiltinOrVar))
  :
  (subp_app b <$> a) = a ->
  a ∪ b = subp_compose a b
.
Proof.
    intros HH.
    unfold subp_compose.
    rewrite HH.
    reflexivity.
Qed.

 *)
