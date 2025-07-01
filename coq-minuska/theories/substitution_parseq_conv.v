From Minuska Require Import
    prelude
    spec
    basic_properties
    termoverbov_subst
    termoverbov_subst_properties
    substitution_parallel
    substitution_parallel_properties
    substitution_sequential
    substitution_sequential_properties
.

From Coq Require Import
    Logic.Classical_Prop
.

Definition make_parallel
    {Σ : StaticModel}
    (sub : SubS)
    : (gmap variable (TermOver BuiltinOrVar))
:=
    list_to_map sub
.

Fixpoint fresh_var_seq
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    : list variable
:=
    match n with
    | 0 => []
    | S n' => (fresh avoid)::(fresh_var_seq ((fresh avoid)::avoid) n')
    end
.

Fixpoint fresh_nth
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    : variable
:=
    match n with
    | 0 => fresh avoid
    | S n' => (fresh_nth ((fresh avoid)::avoid) n')
    end
.

Definition RenamingT {Σ : StaticModel} : Type := gmap variable variable.

Definition renaming_ok {Σ : StaticModel} (r : RenamingT) : Prop :=
    forall k1 k2 v, r !! k1 = Some v -> r !! k2 = Some v -> k1 = k2
.

Lemma renaming_ok_empty
    {Σ : StaticModel}
    :
    renaming_ok ∅
.
Proof.
    unfold renaming_ok.
        intros k1 k2 v HH1 HH2.
        ltac1:(rewrite lookup_empty in HH1).
        inversion HH1.
Qed.

Lemma renaming_ok_insert_inv {Σ : StaticModel}
    (r : RenamingT)
    (x y : variable)
:
    x ∉ dom r ->
    renaming_ok (<[x:=y]>r) ->
    renaming_ok r
.
Proof.
    unfold RenamingT in *.
    intros HH1 HH.
    unfold renaming_ok in *.
    intros k1 k2 v H1 H2.
    specialize (HH k1 k2 v).
    destruct (decide (k1 = x)).
    {
        subst.
        ltac1:(rewrite lookup_insert in HH).
        ltac1:(contradiction HH1).
        rewrite elem_of_dom.
        exists v.
        apply H1.
    }
    {
        ltac1:(rewrite lookup_insert_ne in HH).
        {
            ltac1:(congruence).
        }
        specialize (HH H1).
        destruct (decide (k2 = x)).
        {
            subst.
            ltac1:(rewrite lookup_insert in HH).
            ltac1:(contradiction HH1).
            rewrite elem_of_dom.
            exists v.
            apply H2.
        }
        {
            ltac1:(rewrite lookup_insert_ne in HH).
            {
                ltac1:(congruence).
            }
            specialize (HH H2).
            exact HH.
        }
    }
Qed.

Definition r_inverse {Σ : StaticModel} (r : RenamingT) : RenamingT :=
    list_to_map ((fun kv => (kv.2,kv.1))<$>(map_to_list r))
.

Lemma renaming_ok_nodup
    {Σ : StaticModel}
    (r : RenamingT)
    :
    renaming_ok r ->
    NoDup ([eta snd] <$> map_to_list r)
.
Proof.
    unfold RenamingT in *.
    intros H.
    apply NoDup_fmap_2_strong.
    {
        intros [a b] [c d] HH3' HH4' HH5'.
        simpl in *.
        subst.
        f_equal.
        rewrite elem_of_map_to_list in HH3'.
        rewrite elem_of_map_to_list in HH4'.
        apply (H a c d HH3' HH4').
    }
    {
        apply NoDup_map_to_list.
    }
Qed.

Lemma r_inverse_insert
    {Σ : StaticModel}
    (r : RenamingT)
    (x y : variable)
    :
    renaming_ok r ->
    x ∉ dom r ->
    y ∉ (@map_img variable variable (gmap variable variable) _ (gset variable) _ _ _ r) ->
    r_inverse (<[x:=y]>r) = <[y:=x]>(r_inverse r)
.
Proof.
    unfold r_inverse.
    intros HH2 HH3 HH1.
    unfold RenamingT in *.
    ltac1:(apply map_eq_iff).
    intros i.
    assert(Htmp2 : NoDup ([eta snd] <$> map_to_list r)).
    {
        apply renaming_ok_nodup.
        exact HH2.
    }
    assert(Htmp1 : NoDup
        ((λ kv : variable * variable, (kv.2, kv.1)) <$> map_to_list (<[x:=y]> r)).*1).
    {
        ltac1:(rewrite <- list_fmap_compose).
        unfold compose.
        simpl.
        unfold renaming_ok in HH2.
        rewrite map_to_list_insert.
        rewrite fmap_cons.
        simpl.
        constructor.
        {
            intros HContra.
            (* apply HH1. clear HH1. *)
            (* rewrite elem_of_dom. *)
            rewrite elem_of_list_fmap in HContra.
            destruct HContra as [[z1 z2][H1z H2z]].
            subst.
            simpl in *.
            rewrite elem_of_map_to_list in H2z.
            rewrite elem_of_map_img in HH1.
            apply HH1.
            exists z1.
            exact H2z.
        }
        {
            apply Htmp2.
        }
        {
            apply not_elem_of_dom_1 in HH3.
            exact HH3.
        }
  
    }
    destruct (decide (i = y)).
    {
        subst.
        rewrite lookup_insert.
        ltac1:(rewrite - elem_of_list_to_map).
        {
            assumption.
        }
        rewrite elem_of_list_fmap.
        exists (x,y).
        simpl.
        split>[reflexivity|].
        rewrite elem_of_map_to_list.
        rewrite lookup_insert.
        reflexivity.
    }
    {
        rewrite lookup_insert_ne.
        lazy_match! goal with
        | [|- _ = ?r !! ?i] =>
            destruct ($r !! $i) eqn:Heq
        end.
        {
            ltac1:(rewrite - elem_of_list_to_map).
            {
                apply Htmp1.
            }
            ltac1:(rewrite - elem_of_list_to_map in Heq).
            {
                rewrite <- list_fmap_compose.
                unfold compose.
                simpl.
                exact Htmp2.
            }
            rewrite elem_of_list_fmap in Heq.
            rewrite elem_of_list_fmap.
            destruct Heq as [[z1 z2][H1z H2z]].
            simpl in *.
            ltac1:(simplify_eq/=).
            exists (z1, z2).
            split>[reflexivity|].
            rewrite elem_of_map_to_list.
            destruct (decide (z1 = x)).
            {
                subst.
                rewrite elem_of_map_to_list in H2z.
                ltac1:(contradiction HH3).
                rewrite elem_of_dom.
                rewrite H2z.
                exists z2.
                simpl.
                reflexivity.
            }
            {
                rewrite lookup_insert_ne.
                {
                    rewrite elem_of_map_to_list in H2z.
                    exact H2z.
                }
                {
                    ltac1:(congruence).
                }
            }
        }
        {
            apply not_elem_of_list_to_map_2 in Heq.
            apply not_elem_of_list_to_map_1.
            intros HContra.
            apply Heq. clear Heq.
            rewrite <- list_fmap_compose.
            rewrite <- list_fmap_compose in HContra.
            unfold compose in *.
            simpl in *.
            rewrite elem_of_list_fmap.
            rewrite elem_of_list_fmap in HContra.
            destruct HContra as [[z1 z2][H1z H2z]].
            simpl in *.
            subst.
            rewrite elem_of_map_to_list in H2z.
            apply lookup_insert_Some in H2z.
            destruct H2z as [H2z|H2z].
            {
                destruct H2z as [H1 H2].
                subst.
                ltac1:(contradiction n).
                reflexivity.
            }
            {
                destruct H2z as [H1 H2].
                exists (z1, z2).
                simpl.
                split>[reflexivity|].
                rewrite elem_of_map_to_list.
                exact H2.
            }
        }
        {
            ltac1:(congruence).
        }
    }
Qed.

Lemma r_inverse_ok {Σ : StaticModel} (r : RenamingT) :
    renaming_ok r ->
    renaming_ok (r_inverse r)
.
Proof.
    unfold RenamingT in *.
    intros H.
    unfold renaming_ok, r_inverse.
    intros k1 k2 v HH1 HH2.
    ltac1:(rewrite - elem_of_list_to_map in HH1).
    {
        rewrite <- list_fmap_compose.
        unfold compose.
        simpl.
        apply renaming_ok_nodup.
        exact H.
    }
    ltac1:(rewrite - elem_of_list_to_map in HH2).
    {
        rewrite <- list_fmap_compose.
        unfold compose.
        simpl.
        apply renaming_ok_nodup.
        exact H.
    }
    rewrite elem_of_list_fmap in HH1.
    rewrite elem_of_list_fmap in HH2.
    destruct HH1 as [[a b][HH11 HH12]].
    destruct HH2 as [[c d][HH21 HH22]].
    simpl in *.
    ltac1:(simplify_eq/=).
    ltac1:(rewrite elem_of_map_to_list in HH12).
    ltac1:(rewrite elem_of_map_to_list in HH22).
    ltac1:(simplify_eq/=).
    reflexivity.
Qed.

Lemma r_inverse_inverse {Σ : StaticModel} (r : RenamingT) :
    renaming_ok r ->
    r_inverse (r_inverse r) = r
.
Proof.
    intros Hok.
    unfold r_inverse.
    unfold RenamingT in *.
    apply map_eq_iff.
    intros i.
    destruct (r !! i) eqn:Hri.
    {
        ltac1:(rewrite - elem_of_list_to_map).
        rewrite <- list_fmap_compose.
        unfold compose.
        simpl.
        apply renaming_ok_nodup.
        {
            apply r_inverse_ok.
            apply Hok.
        }
        {
            rewrite elem_of_list_fmap.
            exists (v, i).
            split>[reflexivity|].
            (* ltac1:(rewrite list_to_map_to_list). *)
            rewrite elem_of_map_to_list.
            ltac1:(rewrite - elem_of_list_to_map).
            {
                rewrite <- list_fmap_compose.
                unfold compose.
                simpl.
                apply renaming_ok_nodup.
                exact Hok.
            }
            {
                rewrite elem_of_list_fmap.
                exists (i, v).
                split>[reflexivity|].
                rewrite elem_of_map_to_list.
                exact Hri.
            }
        }
    }
    {
        apply not_elem_of_list_to_map_1.
        intros HContra.
        rewrite elem_of_list_fmap in HContra.
        destruct HContra as [[a b] [H1 H2]].
        simpl in *. subst.
        rewrite elem_of_list_fmap in H2.
        destruct H2 as [[c d][H3 H4]].
        ltac1:(simpl in *; simplify_eq/=).
        rewrite elem_of_map_to_list in H4.
        ltac1:(rewrite - elem_of_list_to_map in H4).
        {
            rewrite <- list_fmap_compose.
            unfold compose.
            simpl.
            apply renaming_ok_nodup.
            exact Hok.
        }
        rewrite elem_of_list_fmap in H4.
        destruct H4 as [[a b] [H5 H6]].
        simpl in *.
        ltac1:(simplify_eq/=).
        rewrite elem_of_map_to_list in H6.
        rewrite H6 in Hri.
        inversion Hri.
    }
Qed.

Definition renaming_for
    {Σ : StaticModel}
    (sub_mm : SubP)
    :
    RenamingT
:=
    let rhss : list (TermOver BuiltinOrVar) := snd <$> map_to_list sub_mm in
    let avoid : list variable := elements (union_list (vars_of <$> rhss)) in
    let to_be_renamed : list variable := elements (dom sub_mm) in
    let r' := zip to_be_renamed (fresh_var_seq (to_be_renamed ++ avoid) (length to_be_renamed)) in
    list_to_map r'
.

Lemma length_fresh_var_seq
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    :
    length (fresh_var_seq avoid n) = n
.
Proof.
    revert avoid.
    induction n; intros avoid; simpl in *.
    { reflexivity. }
    {
        rewrite IHn. reflexivity.
    }
Qed.


Lemma elem_of_fresh_var_seq
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    (x : variable)
    :
    x ∈ fresh_var_seq avoid n ->
    x ∉ avoid
.
Proof.
    revert avoid.
    induction n; intros avoid HH; simpl in *.
    {
        rewrite elem_of_nil in HH.
        destruct HH.
    }
    {
        rewrite elem_of_cons in HH.
        destruct HH as [HH|HH].
        {
            subst x.
            apply infinite_is_fresh.
        }
        {
            specialize (IHn (fresh avoid::avoid) HH).
            ltac1:(set_solver).
        }
    }
Qed.

Lemma NoDup_fresh_var_seq
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    :
    NoDup (fresh_var_seq avoid n)
.
Proof.
    revert avoid.
    induction n; intros avoid; simpl in *.
    {
        constructor.
    }
    {
        constructor.
        intros HContra.
        apply elem_of_fresh_var_seq in HContra.
        ltac1:(set_solver).
        apply IHn.
    }
Qed.


Lemma renaming_for_ok
    {Σ : StaticModel}
    (s : SubP)
    :
    renaming_ok (renaming_for s)
.
Proof.
    unfold renaming_for.
    unfold renaming_ok.
    intros k1 k2 v H1 H2.
    ltac1:(rewrite - elem_of_list_to_map in H1).
    {
        rewrite fst_zip.
        apply NoDup_elements.
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
    ltac1:(rewrite - elem_of_list_to_map in H2).
    {
        rewrite fst_zip.
        apply NoDup_elements.
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
    rewrite elem_of_list_lookup in H1.
    rewrite elem_of_list_lookup in H2.
    destruct H1 as [i Hi].
    destruct H2 as [j Hj].
    apply lookup_of_zip_both_2 in Hi.
    apply lookup_of_zip_both_2 in Hj.
    destruct Hi as [H1 H2].
    destruct Hj as [H3 H4].
    assert (i = j).
    {
        About NoDup_lookup.
        eapply NoDup_lookup>[|apply H2|apply H4].
        apply NoDup_fresh_var_seq.
    }
    subst j.
    ltac1:(simplify_eq/=).
    reflexivity.
Qed.

Definition rlift
    {Σ : StaticModel}
    (r : RenamingT)
    :
    SubP
:=
   (fun x => t_over (bov_variable x)) <$> r
.

Definition make_serial
    {Σ : StaticModel}
    (s : gmap variable (TermOver BuiltinOrVar))
    :
    SubS
:=
    let r := renaming_for s in
    let rinv := r_inverse r in
    (map_to_list (rlift r))
    ++
    (map_to_list (subp_compose s (rlift rinv)))
.

Lemma make_parallel_app
    {Σ : StaticModel}
    (s1 s2 : SubS)
    :
    make_parallel (s1 ++ s2) = make_parallel s1 ∪ make_parallel s2
.
Proof.
    unfold make_parallel.
    unfold SubS,SubP in *.
    apply list_to_map_app.
Qed.

Lemma make_parallel_map_to_list
    {Σ : StaticModel}
    (s : gmap variable (TermOver BuiltinOrVar))
    :
    make_parallel (map_to_list s) = s
.
Proof.
    unfold make_parallel.
    unfold SubP in *.
    apply list_to_map_to_list.
Qed.

Definition idren
    {Σ : StaticModel}
    (vs : gset variable)
    : RenamingT
:=
    set_to_map (fun x => (x,x)) vs
.

(* Likely is not true *)
Lemma compose_renaming_inverse
    {Σ : StaticModel}
    (r : RenamingT)
    :
    renaming_ok r ->
    (subp_compose (rlift (r_inverse r)) (rlift r)) = rlift (idren (dom r))
.
Proof.
    intros Hrok.
    unfold subp_compose.
    apply map_eq_iff.
    intros i.
    unfold rlift,idren,r_inverse.
    rewrite <- map_fmap_compose.
    unfold compose.
    simpl.
    rewrite lookup_fmap.
    destruct ((set_to_map _ (dom r)) !! i) eqn:Heq.
    {
        simpl.
        ltac1:(rewrite lookup_set_to_map in Heq).
        {
            intros y y' Hy Hy' HH.
            simpl in *.
            exact HH.
        }
        destruct Heq as [y [H1y H2y]].
        ltac1:(simplify_eq/=).
        rewrite lookup_union.
        rewrite lookup_fmap.
        (* rewrite lookup_fmap. *)
        ltac1:(rewrite elem_of_dom in H1y).
        destruct H1y as [v' Hv'].
        rewrite Hv'.
        simpl.
        rewrite map_lookup_filter.
        simpl.
        remember (list_to_map ((λ kv : variable * variable, (kv.2, kv.1)) <$> map_to_list r)) as r'.
        rewrite lookup_fmap.
        unfold union,option_union,union_with,option_union_with.
        ltac1:(case_match).
        {
            ltac1:(simplify_option_eq).
            ltac1:(rewrite - elem_of_list_to_map in Heqo1).
            {
                rewrite <- list_fmap_compose.
                apply renaming_ok_nodup.
                apply Hrok.
            }
            {
                unfold RenamingT in *.
                unfold SubP in *.
                ltac1:(rewrite elem_of_list_fmap in Heqo1).
                destruct Heqo1 as [[y z][HH1 HH2]].
                simpl in *.
                ltac1:(simplify_eq/=).
                rewrite elem_of_map_to_list in HH2.
                ltac1:(contradiction H0).
                unfold subp_dom.
                ltac1:(rewrite elem_of_dom).
                rewrite lookup_fmap.
                rewrite Hv'.
                simpl.
                eexists.
                reflexivity.
            }
        }
        {
            ltac1:(simplify_option_eq).
            {
                ltac1:(rewrite lookup_fmap).
                unfold subp_dom in H0.
                ltac1:(rewrite elem_of_dom in H0).
                destruct H0 as [? H0].
                rewrite lookup_fmap in H0.
                rewrite Hv' in H0.
                simpl in H0.
                destruct (decide (v = v')).
                {
                    subst.
                    rewrite Heqo1.
                    simpl.
                    ltac1:(simplify_eq/=).
                    ltac1:(rewrite - elem_of_list_to_map in Heqo1).
                    {
                        rewrite <- list_fmap_compose.
                        apply renaming_ok_nodup.
                        apply Hrok.
                    }
                    {
                        rewrite elem_of_list_fmap in Heqo1.
                        destruct Heqo1 as [[y z][H1 H2]].
                        simpl in *.
                        ltac1:(simplify_eq/=).
                        ltac1:(rewrite elem_of_map_to_list in H2).
                        specialize (Hrok _ _ _ Hv' H2).
                        subst.
                        reflexivity.
                    }
                }
                {
                    ltac1:(simplify_eq/=).
                    ltac1:(repeat case_match; simplify_eq/=).
                    {
                        rewrite fmap_Some in H0.
                        destruct H0 as [x [H1x H2]].
                        subst t.
                        ltac1:(rewrite - elem_of_list_to_map in Heqo1).
                        {
                            rewrite <- list_fmap_compose.
                            apply renaming_ok_nodup.
                            apply Hrok.
                        }
                        {
                            rewrite elem_of_list_fmap in Heqo1.
                            destruct Heqo1 as [[y z][HH1 HH2]].
                            simpl in *.
                            ltac1:(simplify_eq/=).
                            ltac1:(rewrite elem_of_map_to_list in HH2).
                            ltac1:(rewrite - elem_of_list_to_map in H1x).
                            {
                                rewrite <- list_fmap_compose.
                                apply renaming_ok_nodup.
                                apply Hrok.
                            }
                            {
                                rewrite elem_of_list_fmap in H1x.
                                destruct H1x as [[y' z'][HH1' HH2']].
                                simpl in *.
                                ltac1:(simplify_eq/=).
                                ltac1:(rewrite elem_of_map_to_list in HH2').
                                specialize (Hrok _ _ _ Hv' HH2').
                                subst y'.
                                reflexivity.
                            }
                        }
                    }
                    {
                        rewrite fmap_None in H0.
                        unfold RenamingT in *.
                        ltac1:(rewrite - elem_of_list_to_map in Heqo1).
                        {
                            rewrite <- list_fmap_compose.
                            apply renaming_ok_nodup.
                            apply Hrok.
                        }
                        {
                            rewrite elem_of_list_fmap in Heqo1.
                            destruct Heqo1 as [[y z][H1 H2]].
                            simpl in *.
                            ltac1:(simplify_eq/=).
                            ltac1:(rewrite elem_of_map_to_list in H2).
                            unfold RenamingT in *.
                            ltac1:(apply not_elem_of_list_to_map_2 in H0).
                            rewrite elem_of_list_fmap in H0.
                            ltac1:(setoid_rewrite elem_of_list_fmap in H0).
                            ltac1:(contradiction H0).
                            clear H0.
                            destruct (decide (y = z)).
                            {
                                subst.
                                eexists (v', _).
                                split>[reflexivity|].
                                eexists (v', _).
                                split>[reflexivity|].
                                ltac1:(simplify_eq/=).
                            }
                            {
                                eexists (v', _).
                                split>[reflexivity|].
                                eexists (_, _).
                                split>[reflexivity|].
                                rewrite elem_of_map_to_list.
                                exact Hv'.
                            }
                        }
                    }
                }
            }
            unfold RenamingT in *.
            ltac1:(apply not_elem_of_list_to_map_2 in Heqo0).
            rewrite elem_of_list_fmap in Heqo0.
            ltac1:(setoid_rewrite elem_of_list_fmap in Heqo0).
            ltac1:(case_match).
            {
                ltac1:(rewrite lookup_fmap_Some in H).
                destruct H as [x [H1x H2x]].
                subst t.
                ltac1:(rewrite - elem_of_list_to_map in H2x).
                {
                    rewrite <- list_fmap_compose.
                    apply renaming_ok_nodup.
                    apply Hrok.
                }
                {
                    rewrite elem_of_list_fmap in H2x.
                    destruct H2x as [[y' z'][HH1' HH2']].
                    simpl in *.
                    ltac1:(simplify_eq/=).
                    ltac1:(rewrite elem_of_map_to_list in HH2').
                    specialize (Hrok _ _ _ Hv' HH2').
                    subst y'.
                    reflexivity.
                }
            }
            {
                ltac1:(rewrite lookup_fmap in H).
                rewrite fmap_None in H.
                unfold RenamingT in *.
                ltac1:(apply not_elem_of_list_to_map_2 in H).
                rewrite elem_of_list_fmap in H.
                ltac1:(setoid_rewrite elem_of_list_fmap in H).
                destruct (decide (v = v')).
                {
                    subst.
                    reflexivity.
                }
                {
                    ltac1:(contradiction H).
                    clear H.
                    eexists (_,_).
                    split>[reflexivity|].
                    eexists (_,_).   
                    split>[reflexivity|].
                    rewrite elem_of_map_to_list.
                    exact Hv'.
                }
            }
        }
    }
    {
        simpl.
        rewrite lookup_union.
        rewrite union_None.
        split.
        {
            rewrite map_lookup_filter.
            simpl.
            rewrite bind_None.

            unfold set_to_map in Heq.
            ltac1:(rewrite - not_elem_of_list_to_map in Heq).
            rewrite <- list_fmap_compose in Heq.
            unfold compose in Heq.
            simpl in Heq.
            rewrite list_fmap_id in Heq.
            rewrite elem_of_elements in Heq.
            ltac1:(rewrite not_elem_of_dom in Heq).

            
            rewrite lookup_fmap.
            rewrite fmap_None.
            unfold RenamingT in *.
            ltac1:(rewrite - not_elem_of_list_to_map).
            rewrite <- list_fmap_compose.
            unfold compose.
            simpl.
            rewrite elem_of_list_fmap.
            
            apply Decidable.imp_simp.
            {
                (* Shame on me. *)
                apply classic.
            }
            {
                intros HH.
                destruct HH as [[y z][H1 H2]].
                simpl in *.
                subst.
                rewrite elem_of_map_to_list in H2.
                exists (t_over (bov_variable y)).
                simpl.
                (* ltac1:(simplify_option_eq). *)
                {
                    split.
                    {
                        (* rewrite <- map_fmap_compose. *)
                        unfold SubP in *.
                        rewrite fmap_Some.
                        eexists _.
                        split>[|reflexivity].
                        ltac1:(rewrite - elem_of_list_to_map).
                        {
                            rewrite <- list_fmap_compose.
                            apply renaming_ok_nodup.
                            apply Hrok.
                        }
                        rewrite elem_of_list_fmap.
                        eexists (_, _).
                        simpl.
                        split>[reflexivity|].
                        rewrite elem_of_map_to_list.
                        exact H2.
                    }
                    {
                        rewrite bind_None.
                        left.
                        ltac1:(simplify_option_eq).
                        { reflexivity. }
                        {
                            ltac1:(contradiction H).
                            clear H H0.
                            unfold subp_dom.
                            ltac1:(rewrite elem_of_dom).
                            rewrite lookup_fmap.
                            ltac1:(rewrite Heq).
                            simpl.
                        }
                        {
                            ltac1:(contradiction H).
                        }
                    }
                }
                {
                    ltac1:(rewrite elem_of_dom in H).
                    ltac1:(contradiction H).
                    clear H.
                }
            }
            {
                (* Shame on me again. *)
                apply classic.
            }

            Search ((~ _) \/ _ ).

            destruct ((r_inverse r) !! i) eqn:Heq'.
            {
                unfold r_inverse in Heq'.
                setoid_rewrite Heq'.
                simpl.
                right.
                eexists.
                split>[reflexivity|].
                rewrite bind_None.
                ltac1:(simplify_option_eq).
                {
                    left. reflexivity.
                }
                {
                    ltac1:(exfalso).
                    ltac1:(rewrite - elem_of_list_to_map in Heq').
                    {
                        rewrite <- list_fmap_compose.
                        apply renaming_ok_nodup.
                        apply Hrok.
                    }
                    {
                        rewrite elem_of_list_fmap in Heq'.
                        destruct Heq' as [[y z][H1 H2]].
                        simpl in *.
                        ltac1:(simplify_eq/=).
                        ltac1:(rewrite elem_of_map_to_list in H2).
                    }
                }
                left.
                ltac1:(simplify_option_eq).
                { reflexivity. }
                {
                    unfold subp_dom in H.
                    ltac1:(rewrite not_elem_of_dom in H).
                    rewrite lookup_fmap in H.

                }
                {
                    ltac1:(contradiction H).
                }
            }
            ltac1:(destruct (decide (i ∈ (map_img r)))).

            left.
            intros HContra.
            destruct HContra as [[y z][H1 H2]].
            subst.
            simpl in *.
            rewrite elem_of_map_to_list in H2.
            
        }
        {

        }
    }
    ltac1:(rewrite lookup_set_to_map).
    (* rewrite lookup_set_to_map_id. *)
    (* rewrite lookup_fmap. *)
    (* rewrite <- map_fmap_compose. *)
    (* destruct (dom r !! i). *)
    (* rewrite lookup_fmap. *)
    (* rewrite <- map_fmap_compose. *)
Qed.

Lemma to_serial_then_to_parallel
    {Σ : StaticModel}
    (s : gmap variable (TermOver BuiltinOrVar))
    :
    make_parallel ∘ make_serial = id
.
Proof.
    apply functional_extensionality.
    intros m.
    unfold compose.
    unfold make_serial.
    rewrite make_parallel_app.
    rewrite make_parallel_map_to_list.
    ltac1:(rewrite make_parallel_map_to_list).
    rewrite map_union_comm.
    {
        rewrite subp_union_is_compose__sometimes.
        {
            rewrite subp_compose_assoc.
        }
        {

        }
    }
    {
        (* Search map_disjoint. *)
        (* Search "##ₘ". *)
        (* rewrite elem_of_disjoint. *)
    }
    Search union "comm".
    (* rewrite union_comm_L. *)
    rewrite subp_union_is_compose__sometimes.
    {

    }
    {

    }
    (* unfold subp_compose. *)
    (* rewrite assoc. *)
    Search make_parallel.
Qed.



Lemma subp_app_insert
    {Σ : StaticModel}
    (sub_mm : SubP)
    (x : variable)
    (v : TermOver BuiltinOrVar)
    (φ : TermOver BuiltinOrVar)
    :
    subtmm_closed sub_mm  ->
    x ∉ dom sub_mm ->
    subp_app (<[x:=v]>sub_mm) φ
    = subs_app [(x,v)] (subp_app sub_mm φ)
.
Proof.
    induction φ; intros Hsub1 Hxsub; simpl.
    {
        destruct a; simpl.
        {
            reflexivity.
        }
        {
            destruct (decide (x = x0)).
            {
                subst x0.
                ltac1:(rewrite lookup_insert).
                {
                    ltac1:(rewrite not_elem_of_dom_1).
                    { exact Hxsub. }
                    {
                        simpl.
                        rewrite decide_True.
                        { reflexivity. }
                        { reflexivity. }
                    }
                }
            }
            {
                ltac1:(rewrite lookup_insert_ne).
                { assumption. }
                {
                    ltac1:(repeat case_match).
                    {
                        assert (t = t0).
                        {
                            ltac1:(rewrite H in H0).
                            apply (inj Some) in H0.
                            exact H0.
                        }
                        subst t0.
                        symmetry. apply subst_notin2.
                        unfold subtmm_closed in Hsub1.
                        erewrite Hsub1.
                        { ltac1:(set_solver). }
                        { apply H. }
                    }
                    {
                        simpl.
                        rewrite decide_False.
                        {
                            ltac1:(rewrite H0 in H).
                            inversion H.
                        }
                        { assumption. }
                    }
                    {
                        ltac1:(rewrite H0 in H).
                        inversion H.
                    }
                    {
                        simpl.
                        rewrite decide_False.
                        reflexivity.
                        assumption.
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
            rewrite (H1 Hsub1).
            rewrite (IHl H2).
            reflexivity.
            assumption.
        }
    }
Qed.


Lemma subp_app_insert_2
    {Σ : StaticModel}
    (sub_mm : SubP)
    (x : variable)
    (v : TermOver BuiltinOrVar)
    (φ : TermOver BuiltinOrVar)
    :
    vars_of v = ∅ ->
    subp_app (<[x:=v]>sub_mm) φ
    = subp_app sub_mm (subs_app [(x,v)] φ)
.
Proof.
    induction φ; intros Hvars; simpl.
    {
        destruct a; simpl.
        {
            reflexivity.
        }
        {
            destruct (decide (x = x0)).
            {
                subst x0.
                ltac1:(rewrite lookup_insert).
                {
                    rewrite subp_app_closed.
                    reflexivity.
                    exact Hvars.
                }
            }
            {
                ltac1:(rewrite lookup_insert_ne).
                { assumption. }
                {
                    ltac1:(repeat case_match).
                    {
                        simpl.
                        ltac1:(rewrite H).
                        reflexivity.
                    }
                    {
                        simpl.
                        ltac1:(rewrite H).
                        reflexivity.
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
            rewrite (H1 Hvars).
            rewrite (IHl H2).
            reflexivity.
        }
    }
Qed.


Lemma make_parallel_correct
    {Σ : StaticModel}
    (sub : SubS)
    (φ : TermOver BuiltinOrVar)
    :
    subt_closed sub ->
    subp_app (make_parallel sub) φ = subs_app sub φ
.
Proof.
    revert φ.
    induction sub; intros φ HH; simpl.
    {
        rewrite subp_app_empty.
        reflexivity.
    }
    {
        destruct a; simpl in *.
        rewrite subp_app_insert_2.
        simpl.
        rewrite IHsub.
        { reflexivity. }
        {
            unfold subt_closed in HH.
            unfold subt_closed.
            intros k v0 H1.
            specialize (HH (S k)).
            simpl in HH.
            apply HH.
            assumption.
        }
        {
            unfold subt_closed in HH.
            unfold subt_closed.
            (* intros k v0 H1. *)
            specialize (HH 0 (v,t) eq_refl).
            simpl in HH.
            apply HH.
        }
    }
Qed.


Lemma NoDup_1_renaming_for
    {Σ : StaticModel}
    (sub_mm : SubP)
    :
    NoDup (fst <$> renaming_for sub_mm)
.
Proof.
    unfold renaming_for.
    rewrite fst_zip.
    {
        apply NoDup_elements.
    }
    {
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
Qed.

Lemma NoDup_2_renaming_for
    {Σ : StaticModel}
    (sub_mm : SubP)
    :
    NoDup (snd <$> renaming_for sub_mm)
.
Proof.
    unfold renaming_for.
    rewrite snd_zip.
    {
        apply NoDup_fresh_var_seq.
    }
    {
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
Qed.

Lemma NoTwice_renaming_for
    {Σ : StaticModel}
    (sub_mm : SubP)
    :
    forall (x : variable),
        x ∈ (snd <$> renaming_for sub_mm) ->
        x ∉ (fst <$> renaming_for sub_mm)
.
Proof.
    unfold renaming_for.
    remember (length (elements (dom sub_mm))) as n.
    intros x Hx HContra.
    rewrite elem_of_list_fmap in HContra.
    destruct HContra as [[y z] [H1 H2]].
    apply elem_of_zip_l in H2 as H2l.
    apply elem_of_zip_r in H2 as H2r.
    clear H2.
    subst x.
    simpl in *.
    rewrite elem_of_list_fmap in Hx.
    destruct Hx as [[x y1][H3 H4]].
    simpl in *.
    subst y1.
    apply elem_of_zip_l in H4 as Hx1.
    apply elem_of_zip_r in H4 as Hx2.
    clear H4.
    apply elem_of_fresh_var_seq in Hx2.
    clear - Hx2 H2l.
    ltac1:(set_solver).
Qed.

Lemma renaming_for_all
    {Σ : StaticModel}
    (sub_mm : SubP)
    :
    elements (dom sub_mm) ⊆ (fst <$> (renaming_for sub_mm))
.
Proof.
    unfold renaming_for.
    ltac1:(rewrite elem_of_subseteq).
    intros x Hx.
    rewrite fst_zip.
    {
        exact Hx.
    }
    {
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
Qed.

Lemma fresh_var_seq_mono
    {Σ : StaticModel}
    avoid n
    :
    fresh_var_seq avoid n ⊆ fresh_var_seq avoid (S n)
.
Proof.
    revert avoid.
    induction n; intros avoid.
    {
        simpl.
        ltac1:(set_solver).
    }
    {
        specialize (IHn (fresh avoid::avoid)).
        remember (S n) as n'.
        rewrite Heqn' at 1.
        simpl.
        ltac1:(set_solver).
    }
Qed.


Lemma fresh_nth_iff
    {Σ : StaticModel}
    (avoid : list variable)
    (n m : nat)
    (x : variable)
    :
    n < m ->
    fresh_nth avoid n = x <-> ((fresh_var_seq avoid m) !! n = Some x)
.
Proof.
    revert avoid m x.
    induction n; intros avoid m x HH; simpl in *.
    {
        destruct m.
        {
            ltac1:(lia).
        }
        {
            simpl.
            ltac1:(naive_solver).
        }
    }
    {
        destruct m.
        {
            ltac1:(lia).
        }
        {
            specialize (IHn (fresh avoid :: avoid) m x ltac:(lia)).
            simpl.
            exact IHn.
        }
    }
Qed.

(* TODO *)
Lemma make_serial_correct
    {Σ : StaticModel}
    (sub_mm : SubP)
    (φ : TermOver BuiltinOrVar)
:
    subs_app (make_serial sub_mm) φ = subp_app sub_mm φ
.
Proof.
Qed.
