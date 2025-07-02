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

Lemma subp_compse_correct
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
            ltac1:(rewrite lookup_union).
            ltac1:(rewrite lookup_fmap).
            rewrite map_lookup_filter.
            destruct (bb !! x) eqn:Hbbx,
                (aa !! x) eqn:Haax.
            {
                ltac1:(rewrite Haax; simpl; repeat case_match; simplify_option_eq; destruct_and?;
                    simplify_eq/=; try reflexivity);
                unfold subp_dom in *.
                ltac1:(exfalso).
                apply H.
                ltac1:(rewrite elem_of_dom).
                exists t.
                assumption.
            }
            {
                ltac1:(rewrite Haax; simpl; repeat case_match; simplify_option_eq; destruct_and?;
                    simplify_eq/=; try reflexivity);
                unfold subp_dom in *.
            }
            {
                ltac1:(rewrite Haax; simpl; repeat case_match; simplify_option_eq; destruct_and?;
                    simplify_eq/=; try reflexivity);
                unfold subp_dom in *.
                ltac1:(exfalso).
                ltac1:(rewrite elem_of_dom in H).
                ltac1:(rewrite Hbbx in H).
                destruct H as [? H].
                inversion H.
            }
            {
                ltac1:(rewrite Haax).
                simpl.
                ltac1:(rewrite Haax).
                ltac1:(rewrite Hbbx).
                simpl.
                reflexivity.
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
Qed. *)

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
    ltac1:(rewrite !(map_filter_union, map_filter_filter)).
    {       
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite map_lookup_filter in Hx.
        rewrite lookup_fmap in Hy.
        ltac1:(simplify_option_eq).   
        ltac1:(apply not_elem_of_dom_1 in H0).
        ltac1:(simplify_eq/=).
    }
    {
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite map_lookup_filter in Hx.
        rewrite lookup_fmap in Hy.
        ltac1:(simplify_option_eq).   
        ltac1:(apply not_elem_of_dom_1 in H0).
        ltac1:(simplify_eq/=).
    }
    {
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite lookup_union in Hx.
        rewrite union_Some in Hx.
        rewrite lookup_fmap in Hy.
        simpl in *.
        rewrite fmap_Some in Hy.
        destruct Hy as [z [H1z H2z]].
        subst y.
        ltac1:(simplify_eq/=).
        rewrite map_lookup_filter in Hx.
        rewrite map_lookup_filter in Hx.
        destruct (c !! i) eqn:Hci.
        {
            simpl in *.
            destruct (a !! i) eqn:Hai.
            {
                ltac1:(rewrite Hai in Hx).
                simpl in Hx.
                ltac1:(rewrite option_guard_False in Hx).
                {
                    apply elem_of_dom_2 in Hci.
                    ltac1:(naive_solver).
                }
                {
                    simpl in *.
                    rewrite lookup_fmap in Hx.
                    destruct (b !! i) eqn:Hbi.
                    {
                        simpl in *.
                        apply elem_of_dom_2 in Hci as Hci'.
                        apply elem_of_dom_2 in Hbi as Hbi'.
                        ltac1:(simplify_option_eq; naive_solver).
                    }
                    {
                        simpl in *.
                        ltac1:(naive_solver).
                    }
                }
            }
            {
                ltac1:(rewrite Hai in Hx).
                simpl in *.
                rewrite lookup_fmap in Hx.
                destruct (b !! i) eqn:Hbi.
                {
                    simpl in *.
                    apply elem_of_dom_2 in Hci as Hci'.
                    apply elem_of_dom_2 in Hbi as Hbi'.
                    ltac1:(simplify_option_eq; naive_solver).
                }
                {
                    simpl in *.
                    ltac1:(naive_solver).
                }
            }
        }
        {
            simpl in *.
            destruct (a !! i) eqn:Hai.
            {
                ltac1:(rewrite Hai in Hx).
                simpl in Hx.
                ltac1:(rewrite option_guard_False in Hx).
                {
                    ltac1:(naive_solver).
                }
                {
                    simpl in *.
                    rewrite lookup_fmap in Hx.
                    destruct (b !! i) eqn:Hbi.
                    {
                        simpl in *.
                        apply elem_of_dom_2 in Hbi as Hbi'.
                        ltac1:(simplify_option_eq; naive_solver).
                    }
                    {
                        simpl in *.
                        ltac1:(naive_solver).
                    }
                }
            }
            {
                ltac1:(rewrite Hai in Hx).
                simpl in *.
                rewrite lookup_fmap in Hx.
                destruct (b !! i) eqn:Hbi.
                {
                    simpl in *.
                    apply elem_of_dom_2 in Hbi as Hbi'.
                    ltac1:(simplify_option_eq; naive_solver).
                }
                {
                    simpl in *.
                    ltac1:(naive_solver).
                }
            }
        }
    }
    {       
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite map_lookup_filter in Hx.
        rewrite lookup_fmap in Hy.
        ltac1:(simplify_option_eq).   
        ltac1:(apply not_elem_of_dom_1 in H0).
        ltac1:(simplify_eq/=).
    }
    {       
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite map_lookup_filter in Hx.
        rewrite lookup_fmap in Hy.
        ltac1:(simplify_option_eq).   
        ltac1:(apply not_elem_of_dom_1 in H0).
        ltac1:(simplify_eq/=).
    }
    {       
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite map_lookup_filter in Hx.
        rewrite lookup_fmap in Hy.
        ltac1:(simplify_option_eq).   
        ltac1:(apply not_elem_of_dom_1 in H0).
        ltac1:(simplify_eq/=).
    }
    {       
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite map_lookup_filter in Hx.
        rewrite lookup_fmap in Hy.
        ltac1:(simplify_option_eq).   
        ltac1:(apply not_elem_of_dom_1 in H0).
        ltac1:(simplify_eq/=).
    }
    {       
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite map_lookup_filter in Hx.
        rewrite lookup_fmap in Hy.
        ltac1:(simplify_option_eq).   
        ltac1:(apply not_elem_of_dom_1 in H0).
        ltac1:(simplify_eq/=).
    }
    {
        (* The main part *)

        simpl in *.
        rewrite map_fmap_union.
        simpl in *.
        rewrite map_filter_fmap.
        rewrite map_filter_fmap.
        rewrite map_filter_fmap.
        rewrite map_filter_fmap.


        apply map_eq.
        intros i.
        do 3 (rewrite lookup_union).
        do 3 (rewrite map_lookup_filter).
        destruct (a !! i) eqn:Hai.
        {
          admit.
        }
        {
            simpl.
            rewrite (left_id None union).
            rewrite (left_id None union).
            simpl.
            do 2 (rewrite lookup_fmap).
            do 2 (rewrite map_lookup_filter).
            destruct (b !! i) eqn:Hbi.
            {
              admit.
            }
            {
                simpl.
                do 1 (rewrite (left_id None union)).
                destruct (c !! i) eqn:Hci.
                {
                    rewrite <- map_fmap_compose.
                    rewrite lookup_union.
                    rewrite lookup_fmap.
                    rewrite lookup_fmap.
                    rewrite map_lookup_filter.
                    rewrite map_lookup_filter.
                    simpl.
                    rewrite Hbi.
                    simpl.
                    rewrite (left_id None union).
                    rewrite Hci.
                    simpl.
                    lazy_match! goal with
                    | [|- _ = ?r] => destruct ($r) eqn:Heqr
                    end.
                    {
                        rewrite bind_Some in Heqr.
                        destruct Heqr as [t2 [H1t2 H2t2]].
                        rewrite fmap_Some in H1t2.
                        destruct H1t2 as [t3 [H1t3 H2t3]].
                        rewrite bind_Some in H2t2.
                        rewrite bind_Some in H1t3.
                        destruct H1t3 as [t4 [H1t4 H2t4]].
                        destruct H2t2 as [t5 [H1t5 H2t5]].
                        subst.
                        ltac1:(simplify_eq/=).
                        clear H1t5 H1t4.
                        rewrite fmap_Some.
                        exists t3.
                        split.
                        {
                            rewrite bind_Some.
                            ltac1:(unshelve(eexists)).
                            intros HContra.
                            destruct t3; simpl in *.
                            {
                                destruct a0; simpl in *.
                                {
                                    ltac1:(simplify_eq/=).
                                }
                                {
                                    ltac1:(simplify_eq/=).
                                    ltac1:(case_match).
                                    {
                                        ltac1:(rewrite lookup_union in H).
                                        rewrite map_lookup_filter in H.
                                        rewrite lookup_fmap in H.
                                        subst t.
                                        rewrite union_Some in H.
                                        destruct (a !! x) eqn:Hax.
                                        {
                                          simpl in H.
                                          rewrite bind_Some in H.
                                          lazy_match! (Constr.type (Control.hyp @H)) with
                                          | ( ?l \/ _) => destruct (classic $l) as [Hmy|Hmy]
                                          end.
                                          {
                                            destruct Hmy as [[pf1 pf2][pf3 pf4]].
                                            ltac1:(simplify_eq/=).
                                            clear pf3.
                                            clear H.
                                            destruct (b !! x) eqn:Hbx.
                                            {
                                              apply pf2.
                                              ltac1:(rewrite elem_of_dom).
                                              exists t.
                                              exact Hbx.
                                            }
                                            {
                                              ltac1:(rewrite Hbx in t4).
                                              ltac1:(rewrite Hbx in t5).
                                              simpl in *.
                                              ltac1:(rewrite Hax in t5).
                                              apply t5.
                                              reflexivity.
                                            }
                                          }
                                          {
                                            lazy_match! (Constr.type (Control.hyp @H)) with
                                            | ( _ \/ ?r) => destruct (classic $r) as [Hmy'|Hmy']
                                            end.
                                            {
                                              destruct Hmy' as [Hm1 Hm2].
                                              rewrite bind_None in Hm1.
                                              rewrite fmap_Some in Hm2.
                                              destruct Hm2 as [x0 [H1x0 H2x0]].
                                              rewrite map_lookup_filter in H1x0.
                                              rewrite bind_Some in H1x0.
                                              destruct H1x0 as [x1 [H1x1 H2x1]].
                                              rewrite bind_Some in H2x1.
                                              destruct H2x1 as [pf1 [pf2 pf3]].
                                              ltac1:(simplify_eq/=).
                                              clear pf2.
                                              clear H.
                                              destruct (b !! x) eqn:Hbx.
                                              {
                                                ltac1:(rewrite Hbx in t4).
                                                ltac1:(rewrite Hbx in t5).
                                                ltac1:(congruence).
                                              }
                                              {
                                                ltac1:(rewrite Hbx in t4).
                                                ltac1:(rewrite Hbx in t5).
                                                ltac1:(congruence).
                                              }
                                            }
                                            {
                                              ltac1:(naive_solver).
                                            }
                                          }
                                        }
                                        {
                                          simpl in H.
                                          destruct H as [H|H].
                                          { inversion H. }
                                          destruct H as [_ H].
                                          rewrite map_lookup_filter in H.
                                          destruct (b !! x) eqn:Hbx.
                                          {
                                            simpl in *.
                                            rewrite fmap_Some in H.                                            
                                            destruct H as [t' [H1t' H2t']].
                                            rewrite bind_Some in H1t'.
                                            destruct H1t' as [x0 [H1x0 H2x0]].
                                            ltac1:(simplify_eq/=).
                                            clear H1x0.
                                            ltac1:(rewrite Hbx in t4).
                                            ltac1:(rewrite Hbx in t5).
                                            ltac1:(congruence).
                                          }
                                          {
                                            ltac1:(rewrite Hbx in t4).
                                            ltac1:(rewrite Hbx in t5).
                                            simpl in *.
                                            inversion H.
                                          }
                                        }
                                    }
                                    {
                                      ltac1:(simplify_eq/=).
                                      destruct (b !! x) eqn:Hbx.
                                      {
                                        ltac1:(rewrite Hbx in t4).
                                        ltac1:(rewrite Hbx in t5).
                                        ltac1:(congruence).
                                      }
                                      {
                                        ltac1:(rewrite Hbx in t4).
                                        ltac1:(rewrite Hbx in t5).
                                        simpl in *.
                                        ltac1:(simplify_eq/=).
                                      }
                                    }
                                }
                            }
                            {
                              
                            }
                        }
                        {

                        }
                        (* Search (guard _ = Some _). *)
                        (* apply option_guard_True_pi in H1t5. *)
                    }
(*                     
                    ltac1:(simplify_option_eq; simpl in *; try reflexivity).
                    {
                        ltac1:(rewrite subp_app_union in H).
                        unfold subp_dom, subp_codom.
                        rewrite elem_of_disjoint.
                        intros x H1x H2x.
                        ltac1:(rewrite elem_of_dom in H2x).
                        rewrite elem_of_union_list in H1x.
                        destruct H2x as [p Hp].
                        rewrite lookup_fmap in Hp.
                        destruct H1x as [X [H1X H2X]].
                        rewrite elem_of_list_fmap in H1X.
                        destruct H1X as [y [H1y H2y]].
                        subst X.
                        simpl in *.
                        rewrite elem_of_elements in H2y.
                        ltac1:(rewrite elem_of_map_img in H2y).
                        destruct H2y as [j Hj].
                        ltac1:(rewrite map_lookup_filter in Hp).
                        rewrite fmap_Some in Hp.
                        destruct Hp as [x1 [H1x1 H2x1]].
                        subst p.
                        rewrite map_lookup_filter in Hj.
                        destruct (a !! j) eqn:Haj.
                        {
                            destruct (b !! x) eqn:Hbx.
                            {
                                simpl in *.
                                rewrite bind_Some in Hj.
                                destruct Hj as [[pf1 H2][_ H4]].
                                ltac1:(simplify_eq/=).
                                rewrite bind_Some in H1x1.
                                destruct H1x1 as [? [_ ?]].
                                ltac1:(simplify_eq/=).
                                destruct y; simpl in *.
                                {
                                    destruct a0; simpl in *.
                                    {
                                        unfold vars_of in H2X; simpl in H2X.
                                        unfold vars_of in H2X; simpl in H2X.
                                        rewrite elem_of_empty in H2X.
                                        inversion H2X.
                                    }
                                    {
                                        unfold vars_of in H2X; simpl in H2X.
                                        unfold vars_of in H2X; simpl in H2X.
                                        rewrite elem_of_singleton in H2X.
                                        subst.
                                        ltac1:(rename i into y1).
                                        ltac1:(rename x2 into y2).
                                        ltac1:(rename j into y3).
                                        destruct t; simpl in *.
                                        {
                                            destruct a0; simpl in *.
                                            {
                                                destruct x1; simpl in *.
                                                {
                                                    destruct a0; simpl in *.
                                                    {

                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            {
                                simpl in *.
                                inversion H1x1.
                            }
                        }
                        {
                            simpl in Hj.
                            inversion Hj.
                        }
                        
                        (* rewrite bind_Some in Hp. *)
                    } *)
                }
                {
                    simpl.
                    rewrite <- map_fmap_compose.
                    rewrite lookup_union.
                    rewrite lookup_fmap.
                    rewrite lookup_fmap.
                    rewrite map_lookup_filter.
                    rewrite map_lookup_filter.
                    ltac1:(rewrite Hbi).
                    ltac1:(rewrite Hci).
                    simpl.
                    reflexivity.
                }
            }
            
        }
(* 
        (* Another TRYYYY *)

        lazy_match! goal with
            | [|- ((?a ∪ _) ∪ _) = (?c ∪ _)] =>
                assert (Hmy1: $a = $c)
        end.
        {
            apply map_filter_ext.
            intros i x Hix.
            simpl.
            split.
            {
                intros [[[H1 H2] H3] H4].
                split>[assumption|].
                intros HContra.
                rewrite elem_of_dom in HContra.
                destruct HContra as [y Hy].
                rewrite lookup_union in Hy.
                rewrite map_lookup_filter in Hy.
                (* rewrite map_lookup_filter in Hy. *)
                rewrite lookup_fmap in Hy.
                destruct (b !! i) eqn:Hbi,
                    (c !! i) eqn:Hci.
                {
                    apply elem_of_dom_2 in Hbi as Hbi'.
                    apply elem_of_dom_2 in Hci as Hci'.
                    ltac1:(simplify_option_eq; naive_solver).
                }
                {
                    apply elem_of_dom_2 in Hbi as Hbi'.
                    ltac1:(simplify_option_eq; naive_solver).
                }
                {
                    apply elem_of_dom_2 in Hci as Hci'.
                    ltac1:(simplify_option_eq; naive_solver).
                }
                {
                    simpl in *.
                    rewrite map_lookup_filter in Hy.
                    ltac1:(rewrite Hci in Hy).
                    simpl in *.
                    inversion Hy.
                }
            }
            {
                intros HContra.
                ltac1:(rewrite elem_of_dom in HContra).
                unfold is_Some in HContra.
                subst.
                clear Hix.
                ltac1:(rewrite elem_of_dom).
                ltac1:(rewrite elem_of_dom).
                ltac1:(destruct_and!).
                repeat split; try ltac1:(naive_solver).
                intros HContra.
                destruct HContra as [p Hp].
                apply H0.
                clear H0.
                rewrite lookup_union.
                ltac1:(rewrite map_lookup_filter).
                (* ltac1:(rewrite map_lookup_filter). *)
                rewrite lookup_fmap.
                ltac1:(rewrite map_lookup_filter).
                rewrite Hp.
                simpl.
                destruct (b !! i) eqn:Hbi.
                {
                    simpl.
                    apply elem_of_dom_2 in Hp as Hp'.
                    apply elem_of_dom_2 in Hbi as Hbi'.
                    rewrite option_guard_False.
                    {
                        simpl.
                        destruct (decide (subp_app b p = t_over (bov_variable i))).
                        {
                            rewrite option_guard_False.
                            {
                                simpl.
                                ltac1:(exfalso).
                                (* 
                                    p,t <> i
                                    but sub_app b p = i
                                    thus b must be some variable that gets renamed to i,
                                 *)
                                assert (p <> t_over (bov_variable i)).
                                {
                                    intros Hcontra.
                                    subst p.
                                    unfold subp_is_normal in Hnormalc.
                                    assert(Hp'' := Hp).
                                    rewrite <- Hnormalc in Hp.
                                    unfold subp_normalize in Hp.
                                    rewrite map_lookup_filter in Hp.
                                    rewrite Hp'' in Hp.
                                    simpl in Hp.
                                    ltac1:(simplify_option_eq).
                                }
                                assert (t <> t_over (bov_variable i)).
                                {
                                    intros Hcontra.
                                    subst t.
                                    unfold subp_is_normal in Hnormalb.
                                    assert(Hbi'' := Hbi).
                                    rewrite <- Hnormalb in Hbi.
                                    unfold subp_normalize in Hbi.
                                    rewrite map_lookup_filter in Hbi.
                                    rewrite Hbi'' in Hbi.
                                    simpl in Hbi.
                                    ltac1:(simplify_option_eq).
                                }
                                assert(exists j, p = t_over (bov_variable j)).
                                {
                                    destruct p; simpl in *.
                                    {
                                        destruct a0; simpl in *.
                                        {
                                            ltac1:(simplify_eq/=).
                                        }
                                        {
                                            destruct (b !! x0) eqn:Hbx0;
                                                simpl in *.
                                            {
                                                ltac1:(rewrite Hbx0 in e).
                                                subst.
                                                unfold subp_is_normal in Hnormalb.
                                                rewrite <- Hnormalb in Hbx0.
                                                unfold subp_normalize in Hbx0.
                                                rewrite map_lookup_filter in Hbx0.
                                                rewrite bind_Some in Hbx0.
                                                destruct Hbx0 as [x1 [H'1 H'2]].
                                                ltac1:(simplify_option_eq).
                                                eexists.
                                                reflexivity.
                                            }
                                            {
                                                eexists.
                                                reflexivity.
                                            }
                                        }
                                    }
                                    {
                                        ltac1:(congruence).
                                    }    
                                }
                                destruct H2 as [j Hj].
                                subst p.
                                simpl in *.
                                destruct (b !! j) eqn:Hbj.
                                {
                                    ltac1:(rewrite Hbj in e).
                                    subst.
                                    assert (j <> i) by ltac1:(congruence).
                                }
                                {
                                    ltac1:(rewrite Hbj in e).
                                    ltac1:(congruence).
                                }
                                
                            }   
                            {
                                ltac1:(naive_solver).
                            } 
                        }
                        {
                            rewrite option_guard_True.
                            {
                                eexists.
                                reflexivity.
                            }
                            {
                                ltac1:(naive_solver).
                            }
                        }
                    }
                    {
                        ltac1:(naive_solver).
                    }
                }
                destruct (c !! i) eqn:Hci.
                {
                    ltac1:(exfalso).
                    apply HContra. clear HContra.
                    exists (subp_app b t).
                    apply lookup_union_Some_r.
                    {
                        apply map_disjoint_spec.
                        intros i0 x0 y HH1 HH2.
                        rewrite lookup_fmap in HH2.
                        rewrite map_lookup_filter in HH1.
                        ltac1:(simplify_option_eq).
                        apply H1.
                        ltac1:(rewrite elem_of_dom).
                        rewrite Heqo1.
                        exists H.
                        reflexivity.
                    }
                    {
                        rewrite lookup_fmap.
                        rewrite Hci.
                        simpl.
                        reflexivity.
                    }
                }
                split.
                {
                    intros HContra2.
                    apply HContra.
                    clear HContra.
                    destruct HContra2 as [wtf Hwtf].
                    inversion Hwtf.
                }
                {
                    intros HContra2.
                    apply HContra.
                    clear HContra.
                    destruct HContra2 as [v Hv].
                    exists v.
                    (* exists (subp_app b v). *)
                    apply lookup_union_Some_l.
                    rewrite map_lookup_filter.
                    rewrite Hv.
                    simpl.
                    ltac1:(simplify_option_eq).
                    {
                        ltac1:(exfalso).
                        ltac1:(rewrite elem_of_dom in H).
                        rewrite Hci in H.
                        destruct H as [? H].
                        inversion H.
                    }
                    reflexivity.
                }
            }
        
        }


        f_equal.

        (* NOT THIS WAY *)
        setoid_rewrite subp_app_union.
        {

        }
        {
            unfold subp_dom,subp_codom.
            rewrite elem_of_disjoint.
            intros x H1x H2x.
            ltac1:(rewrite elem_of_dom in H2x).
            destruct H2x as [p Hp].
            rewrite elem_of_union_list in H1x.
            destruct H1x as [X [H1X H2X]].
            rewrite elem_of_list_fmap in H1X.
            destruct H1X as [y [H1y H2y]].
            subst.
            rewrite elem_of_elements in H2y.
            ltac1:(rewrite elem_of_map_img in H2y).
            destruct H2y as [i Hi].
            simpl in *.
            rewrite map_lookup_filter_Some in Hp.
            rewrite map_lookup_filter_Some in Hi.
            destruct Hp as [H1 H2].
            destruct Hi as [H3 [H4 H5]].
            rewrite lookup_fmap in H1.
            simpl in *.
            (* NOT THIS WAY *)
            destruct ()
        }
        Search subp_app compose.
        (* rewrite map_fmap_union. *)
        (* reflexivity. *)
        ltac1:(rewrite map_filter_union).
        (* rewrite <- union_assoc_L. *)
    }
        (* destruct Hx as [Hx|Hx].
        {
            simpl in *.
            rewrite Hx.
        } *)
        rewrite subp_app_union in Hy.
        rewrite lookup_union in Hy.
        rewrite union_Some in Hy.
        simpl in *.
    }
  {
    reflexivity.
  }
  rewrite map_filter_union.
  {
    unfold subp_dom.
    rewrite map_filter_filter.
    rewrite map_filter_filter.
    simpl.
    remember (subp_app b <$> c) as bc.
    remember (subp_app a <$> b) as ab.
    rewrite subp_app_union.
    apply map_eq.
    intros i.
    rewrite lookup_union.
    do 4 (rewrite map_lookup_filter).
    do 2 (rewrite lookup_union).
    do 2 (rewrite map_lookup_filter).
    do 3 (rewrite lookup_fmap).
    simpl.
    (* ltac1:(simplify_option_eq). *)
    (* setoid_rewrite not_elem_of_dom. *)
    destruct (a !! i) eqn:Hai,
        (b !! i) eqn:Hbi,
        (c !! i) eqn:Hci;
        simpl.
    {
        (* ltac1:(simplify_option_eq). *)
        rewrite option_guard_False.
        {
            simpl.
        }
        {
            intros HContra.
            apply HContra.
            ltac1:(rewrite elem_of_dom).
            eexists. exact Hbi.
        }
        Search guard.
    }
    {
        simpl.
    }
    remember (subp_app b <$> c) as c'.
    lazy_match! goal with
    | [|- ((?a ∪ _) ∪ _) = (?c ∪ _)] =>
        assert (Hmy1: $a = $c)
    end.
    {
        apply map_filter_ext.
        intros i x Hix.
        simpl.
        split.
        {
            intros [H1 H2] HContra.
            ltac1:(rewrite elem_of_dom in HContra).
            destruct HContra as [y Hy].
            subst c'.
            apply lookup_union_Some in Hy.
            {
                destruct Hy as [Hy|Hy].
                {
                    apply map_lookup_filter_Some in Hy.
                    destruct Hy as [H4 H5].
                    simpl in *.
                    apply H2.
                    ltac1:(rewrite elem_of_dom).
                    rewrite H4.
                    exists y.
                    reflexivity.
                }
                {
                    rewrite lookup_fmap in Hy.
                    rewrite fmap_Some in Hy.
                    destruct Hy as [z [H1z H2z]].
                    subst.
                    apply H1.
                    ltac1:(rewrite elem_of_dom).
                    rewrite H1z.
                    exists z.
                    reflexivity.
                }
            }
            {
                apply map_disjoint_spec.
                intros i0 x0 y0 HH1 HH2.
                rewrite lookup_fmap in HH2.
                rewrite fmap_Some in HH2.
                destruct HH2 as [x1 [HH3 HH4]].
                subst.
                apply map_lookup_filter_Some in HH1.
                destruct HH1 as [HH1 HH2].
                simpl in *.
                apply HH2.
                ltac1:(rewrite elem_of_dom).
                rewrite HH3.
                exists x1.
                reflexivity.
            }
        }
        {
            intros HContra.
            ltac1:(rewrite elem_of_dom in HContra).
            unfold is_Some in HContra.
            subst.
            clear Hix.
            ltac1:(rewrite elem_of_dom).
            ltac1:(rewrite elem_of_dom).
            destruct (c !! i) eqn:Hci.
            {
                ltac1:(exfalso).
                apply HContra. clear HContra.
                exists (subp_app b t).
                apply lookup_union_Some_r.
                {
                    apply map_disjoint_spec.
                    intros i0 x0 y HH1 HH2.
                    rewrite lookup_fmap in HH2.
                    rewrite map_lookup_filter in HH1.
                    ltac1:(simplify_option_eq).
                    apply H1.
                    ltac1:(rewrite elem_of_dom).
                    rewrite Heqo1.
                    exists H.
                    reflexivity.
                }
                {
                    rewrite lookup_fmap.
                    rewrite Hci.
                    simpl.
                    reflexivity.
                }
            }
            split.
            {
                intros HContra2.
                apply HContra.
                clear HContra.
                destruct HContra2 as [wtf Hwtf].
                inversion Hwtf.
            }
            {
                intros HContra2.
                apply HContra.
                clear HContra.
                destruct HContra2 as [v Hv].
                exists v.
                (* exists (subp_app b v). *)
                apply lookup_union_Some_l.
                rewrite map_lookup_filter.
                rewrite Hv.
                simpl.
                ltac1:(simplify_option_eq).
                {
                    ltac1:(exfalso).
                    ltac1:(rewrite elem_of_dom in H).
                    rewrite Hci in H.
                    destruct H as [? H].
                    inversion H.
                }
                reflexivity.
            }
        }
    }
    rewrite Hmy1.
    ltac1:(rewrite map_filter_fmap).
    simpl.
    rewrite map_fmap_union.

    subst c'.
    rewrite <- map_fmap_compose.
    rewrite map_union_assoc.
    f_equal.
    rewrite <- subp_compse_correct.
    reflexivity.
  }
  {
    apply map_disjoint_spec.
    intros i x y HH1 HH2.
    rewrite lookup_fmap in HH2.
    rewrite map_lookup_filter in HH1.
    ltac1:(simplify_option_eq).
    apply H0.
    unfold subp_dom.
    ltac1:(rewrite elem_of_dom).
    exists H.
    assumption.
  } *)
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
