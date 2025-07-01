From Minuska Require Import
    prelude
    spec
    substitution_parallel
    basic_properties
    termoverbov_subst
    termoverbov_subst_properties
.

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

Example subp_compose_ex1
  {Σ : StaticModel}
  (x y : variable)
  (f : symbol)
  (t : TermOver BuiltinOrVar)
  :
  subp_compose ({[y := t]}) ({[x := t_term f [t_over (bov_variable y)]]})
  = {[x := t_term f [t]]}
.
Proof.
  unfold subp_compose.
  unfold SubP in *.
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
  ltac1:(rewrite lookup_insert).
  rewrite map_filter_insert.
  simpl.
  rewrite map_filter_empty.
  ltac1:(case_match).
  {
    clear H.
    ltac1:(rename n into H).
    unfold subp_codom in H.
    rewrite elem_of_union_list in H.
    ltac1:(exfalso).
    apply H.
    clear H.
    exists ({[y]}).
    rewrite elem_of_singleton.
    split>[|reflexivity].
    rewrite elem_of_list_fmap.
    exists (t_term f [t_over (bov_variable y)]).
    unfold vars_of; simpl.
    unfold vars_of; simpl.
    split>[ltac1:(set_solver)|].
    rewrite elem_of_elements.
    ltac1:(rewrite elem_of_map_img).
    exists x.
    rewrite lookup_insert.
    reflexivity.
  }
  {
    clear H.
    ltac1:(rename n into H).
    apply dec_stable in H.
    rewrite delete_empty.
    ltac1:(rewrite map_filter_empty).
    rewrite fmap_empty.
    rewrite left_id.
    {
        reflexivity.
    }
    {
        apply _.
    }
  }
Qed.


Lemma subp_compose_assoc
  {Σ : StaticModel}
  (a b c : SubP)
:
    subp_codom b ## subp_dom c ->
    subp_compose (subp_compose a b) c = subp_compose a (subp_compose b c)
.
Proof.
  unfold SubP in *.
  unfold subp_compose.
  intros Hdisj.
  rewrite assoc.
  f_equal.
  rewrite map_fmap_union.
  f_equal.
  rewrite <- map_fmap_compose.
  f_equal.
  apply functional_extensionality.
  intros x.
  rewrite subp_compose_helper_1.
  {
    rewrite subp_app_union.
    { reflexivity. }
    { exact Hdisj. }
  }
  {
    assumption.
  }
  {
    apply _.
  }
Qed.

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


