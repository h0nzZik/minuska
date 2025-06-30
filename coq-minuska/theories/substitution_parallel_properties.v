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

Lemma subp_compose_correct
    {Σ : StaticModel}
    (a b : SubP)
    (* (p : TermOver BuiltinOrVar) *)
  :
    subp_dom b ## subp_codom b ->
    subp_app (subp_compose a b) = (subp_app a) ∘ (subp_app b)
.
Proof.
    unfold subp_compose.
    unfold SubP in *.
    revert a.
    ltac1:(induction b using map_ind); intros a HH.
    {
        ltac1:(rewrite subp_app_empty').
        unfold compose.
        apply f_equal.
        rewrite map_fmap_id.
        rewrite map_union_empty.
        reflexivity.
    }
    {
        (* simpl. *)
        apply functional_extensionality.
        intros q.
        (* simpl. *)
        ltac1:(rewrite subp_app_insert0).
        {
            simpl.
            unfold subp_dom in *.
            unfold subp_codom in *.
            (* clear - HH. *)
            unfold subp_dom in HH.
            ltac1:(rewrite map_img_insert in HH).
            ltac1:(rewrite dom_insert_L in HH).
            rewrite elem_of_disjoint.
            intros y H1y H2y.
            rewrite elem_of_disjoint in HH.
            specialize (HH y).
            apply HH; clear HH.
            {
                ltac1:(set_solver).
            }
            {
                rewrite elem_of_union_list.
                exists (vars_of x).
                split>[|exact H1y].
                rewrite elem_of_list_fmap.
                exists x.
                split>[reflexivity|].
                rewrite elem_of_elements.
                ltac1:(set_solver).
            }
        }
        (* apply functional_extensionality. *)

        
        assert (H': subp_dom m ## subp_codom m).
        {
            clear IHb.
            unfold subp_dom in *.
            unfold subp_codom in *.
            ltac1:(rewrite dom_insert_L in HH).
            ltac1:(rewrite map_img_insert in HH).
            rewrite elem_of_disjoint.
            intros y Hy.
            rewrite elem_of_disjoint in HH.
            specialize (HH y).
            intros HContra.
            apply HH;
                clear HH.
            { ltac1:(set_solver). }
            {
                rewrite elem_of_union_list in HContra.
                rewrite elem_of_union_list.
                destruct HContra as [X [H1x H2X]].
                exists X.
                split>[|exact H2X].
                rewrite elem_of_list_fmap in H1x.
                rewrite elem_of_list_fmap.
                destruct H1x as [z [H1z H2z]].
                subst.
                exists z.
                split>[reflexivity|].
                rewrite elem_of_elements. 
                rewrite elem_of_elements in H2z.
                rewrite delete_notin.
                {
                    rewrite elem_of_union.
                    right.
                    exact H2z.
                }
                {
                    assumption.
                }
            }
        }

        (* simpl. *)
        (* lazy_match! goal with
        | [|- subp_app _ _ = subp_app _ (((subp_app m) ∘ ?f) _)] =>
            remember $f as f
        end. *)
        (* remember (subp_app m ∘ f) as f'. *)
        
        assert (Hmix : <[i:=x]>m = {[i:=x]} ∪ m).
        {
            clear - H.
            apply map_eq_iff.
            intros y.
            destruct (decide (i = y)).
            {
                subst.
                rewrite lookup_insert.
                rewrite lookup_union.
                rewrite lookup_singleton.
                rewrite H.
                reflexivity.
            }
            {
                rewrite lookup_insert_ne.
                {
                    rewrite lookup_union.
                    rewrite lookup_singleton_ne.
                    unfold union,option_union,union_with,option_union_with.
                    ltac1:(case_match); reflexivity.
                    ltac1:(congruence).
                }
                {
                    ltac1:(congruence).
                }
            }
        }
        (* Search compose. *)
        (* rewrite Hmix. *)
        (* rewrite assoc. *)
        rewrite <- subp_app_singleton.
        remember ([eta subp_app m ∘ subp_app {[i := x]}] ) as f.
        rewrite Hmix.
        rewrite assoc.
        ltac1:(replace ({[i:=x]}) with ((subp_app {[i := x]}) <$> ({[i := (t_over (bov_variable i))]}:(gmap variable (TermOver BuiltinOrVar))))).
        {
            subst f.
            Set Printing Parentheses.
            ltac1:(rewrite map_fmap_compose).
            
            ltac1:(rewrite <- map_fmap_union).
        }
        {
            rewrite <- insert_empty.
            rewrite fmap_insert.
            rewrite fmap_empty.
            rewrite insert_empty.
            subst f.
            simpl.
            ltac1:(rewrite lookup_singleton).
            reflexivity.
        }
        specialize (IHb ((f' <$> a) ∪ {[i := x]})).
        ltac1:(ospecialize (IHb _)).
        {
            assumption.
        }
        Set Printing Parentheses.
        (* rewrite set_fmap_union in IHb. *)
        ltac1:(rewrite <- list_fmap_compose in IHb).
        rewrite IHb.
        unfold subp_compose in *.
        unfold compose in *.
        rewrite IHb.
    }
Qed.