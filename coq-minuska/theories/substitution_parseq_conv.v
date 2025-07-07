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
    (map_to_list (subp_compose s (rlift rinv)))
    ++
    (map_to_list (rlift r))
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

Lemma compose_renaming_inverse_restrict
    {Σ : StaticModel}
    (r : RenamingT)
    :
    renaming_ok r ->
    subp_restrict (dom r) ((subp_compose (rlift (r_inverse r)) (rlift r))) = subp_id
.
Proof.
    intros Hrok.
    unfold subp_restrict,subp_compose,subp_id.
    unfold RenamingT in *.
    unfold SubP in *.
    apply map_eq.
    intros i.
    rewrite lookup_empty.
    unfold subp_normalize.
    rewrite map_filter_filter.
    rewrite map_lookup_filter.
    rewrite lookup_union.
    rewrite lookup_fmap.
    rewrite map_lookup_filter.
    simpl.
    unfold subp_dom in *.
    unfold SubP in *.
    destruct (rlift r !! i) eqn:Hri,
        (rlift (r_inverse r) !! i) eqn:Hnri.
    {
        ltac1:(rewrite Hnri Hri).
        simpl.
        rewrite option_guard_False.
        {
            simpl.
            rewrite option_guard_False.
            {
                reflexivity.
            }
            {
                intros [HH1 HH2].
                unfold rlift,r_inverse in Hnri.
                ltac1:(rewrite lookup_fmap in Hnri).
                rewrite fmap_Some in Hnri.
                destruct Hnri as [x Hnri].
                ltac1:(rewrite - elem_of_list_to_map in Hnri).
                {
                    rewrite <- list_fmap_compose.
                    unfold compose. simpl.
                    apply renaming_ok_nodup.
                    exact Hrok.
                }
                destruct Hnri as [H1 H2].
                subst t0.
                rewrite elem_of_list_fmap in H1.
                destruct H1 as [[z1 z2][H1z H2z]].
                ltac1:(simplify_eq/=).
                ltac1:(rewrite elem_of_map_to_list in H2z).
                unfold rlift in Hri.
                ltac1:(rewrite lookup_fmap in Hri).
                rewrite fmap_Some in Hri.
                destruct Hri as [x [H1ri H2ri]].
                ltac1:(simplify_eq/=).
                ltac1:(case_match).
                {
                    unfold rlift, r_inverse in H.
                    unfold SubP in *.
                    rewrite lookup_fmap in H.
                    rewrite fmap_Some in H.
                    destruct H as [x0 [H1 H2]].
                    ltac1:(simplify_eq/=).
                    rewrite elem_of_dom in HH1.
                    destruct HH1 as [y Hy].
                    ltac1:(simplify_eq/=).
                    ltac1:(rewrite - elem_of_list_to_map in H1).
                    {
                        rewrite <- list_fmap_compose.
                        unfold compose. simpl.
                        apply renaming_ok_nodup.
                        exact Hrok.
                    }
                    rewrite elem_of_list_fmap in H1.
                    destruct H1 as [[z'1 z'2][H'1z H'2z]].
                    ltac1:(simplify_eq/=).
                    ltac1:(rewrite elem_of_map_to_list in H'2z).
                    assert(Htmp := Hrok _ _ _ Hy H'2z).
                    subst.
                    ltac1:(simplify_eq/=).
                }
                {
                    clear HH1.
                    unfold rlift,r_inverse in H.
                    unfold SubP in *.
                    rewrite lookup_fmap in H.
                    rewrite fmap_None in H.
                    unfold RenamingT in *.
                    ltac1:(rewrite <- not_elem_of_list_to_map in H).
                    rewrite <- list_fmap_compose in H.
                    unfold compose in H.
                    simpl in H.
                    rewrite elem_of_list_fmap in H.
                    apply H. clear H.
                    exists (z2, x).
                    split>[reflexivity|].
                    rewrite elem_of_map_to_list.
                    exact H1ri.
                }
            }
        }
        {
            intros HH. apply HH. clear HH.
            rewrite elem_of_dom.
            ltac1:(rewrite Hri).
            eexists. reflexivity.
        }
    }
    {
        ltac1:(rewrite Hnri Hri).
        simpl.
        rewrite option_guard_False.
        { reflexivity. }
        {
            intros [H1 H2].
            unfold rlift,r_inverse in Hnri.
            unfold RenamingT in *.
            unfold SubP in *.
            rewrite lookup_fmap in Hnri.
            rewrite fmap_None in Hnri.
            rewrite <- not_elem_of_list_to_map in Hnri.
            rewrite <- list_fmap_compose in Hnri.
            unfold compose in Hnri.
            simpl in Hnri.
            rewrite elem_of_dom in H1.
            rewrite elem_of_list_fmap in Hnri.
            destruct H1 as [z Hz].
            unfold rlift in Hri.
            rewrite lookup_fmap in Hri.
            unfold RenamingT in *.
            unfold SubP in *.
            ltac1:(rewrite fmap_Some in Hri).
            destruct Hri as [y [H1y H2y]].
            ltac1:(simplify_eq/=).
            destruct (rlift (r_inverse r) !! z) eqn:H2z.
            {
                unfold rlift, r_inverse in H2z.
                unfold RenamingT in *.
                unfold SubP in *.
                rewrite lookup_fmap in H2z.
                rewrite fmap_Some in H2z.
                destruct H2z as [y [H1y H2y]].
                ltac1:(simplify_eq/=).
                ltac1:(rewrite - elem_of_list_to_map in H1y).
                {
                    rewrite <- list_fmap_compose.
                    unfold compose. simpl.
                    apply renaming_ok_nodup.
                    exact Hrok.
                }
                unfold RenamingT in *.
                unfold SubP in *.
                (* rewrite list_lookup_fmap in H1y. *)
                rewrite elem_of_list_fmap in H1y.
                destruct H1y as [[z1 z2][H1z H2z]].
                ltac1:(simplify_eq/=).
                rewrite elem_of_map_to_list in H2z.
                assert(Htmp := Hrok _ _ _ Hz H2z).
                subst i.
                ltac1:(contradiction H2).
                reflexivity.
            }
            {
                unfold rlift, r_inverse in H2z.
                unfold RenamingT in *.
                unfold SubP in *.
                rewrite lookup_fmap in H2z.
                rewrite fmap_None in H2z.
                rewrite <- not_elem_of_list_to_map in H2z.
                rewrite <- list_fmap_compose in H2z.
                unfold compose in H2z.
                simpl in H2z.
                rewrite elem_of_list_fmap in H2z.
                apply H2z. clear H2z.
                exists (i, z).
                simpl.
                split>[reflexivity|].
                rewrite elem_of_map_to_list.
                exact Hz.
            }
        }
    }
    {
        ltac1:(rewrite Hnri Hri).
        simpl.
        rewrite (right_id None union).
        rewrite option_guard_True.
        {
            simpl. 
            rewrite option_guard_False.
            { reflexivity. }
            {
                unfold subp_dom.
                unfold SubP in *.
                rewrite elem_of_dom.
                (* rewrite Hri. *)
                intros [HH1 HH2].
                unfold rlift,r_inverse in Hnri.
                unfold rlift in Hri.
                unfold RenamingT, SubP in *.
                rewrite lookup_fmap in Hnri.
                rewrite lookup_fmap in Hri.
                destruct (r !! i) eqn:Hri2.
                {
                    simpl in Hri. inversion Hri.
                }
                {
                    destruct HH1 as [? HH1].
                    inversion HH1.
                }
            }
        }
        {
            unfold RenamingT, SubP in *.
            rewrite elem_of_dom.
            rewrite Hri.
            intros [? HContra].
            inversion HContra.
        }
    }
    {
        ltac1:(rewrite Hnri Hri).
        simpl.
        reflexivity.
    }
Qed.

Lemma subp_restrict_compose
  {Σ : StaticModel}
  (a b : gmap variable (TermOver BuiltinOrVar))
  (vars : gset variable)
:
  dom a ⊆ vars ->
  subp_restrict vars (subp_compose a b) = subp_compose (subp_restrict vars a) (subp_restrict vars b)
.
Proof.
  intros Hva.


    unfold subp_restrict at 1.
    unfold subp_compose at 1.
    unfold subp_normalize at 1.
    unfold SubP in *.
    rewrite map_filter_comm.
    (* Unset Printing Notations. *)
    rewrite map_filter_union.
    {
        rewrite map_filter_fmap.
        simpl.
        unfold subp_compose.
        unfold subp_normalize.
        (* f_equal. *)
        simpl in *.
        f_equal.
        rewrite map_filter_filter.
        unfold subp_restrict at 4.
        unfold SubP in *.
        rewrite map_filter_filter.
        simpl.
        f_equal.
        {
            unfold subp_restrict,subp_dom.
            unfold SubP in *.
            apply map_filter_ext.
            intros i x Haix.
            split.
            {
                intros [Hiv Hib].
                split>[|assumption].
                rewrite elem_of_dom.
                rewrite elem_of_dom in Hib.
                intros HContra. apply Hib. clear Hib.
                destruct HContra as [y Hy].
                rewrite map_lookup_filter in Hy.
                destruct (b !! i) eqn:Hbi.
                {
                    simpl in Hy.
                    rewrite option_guard_True in Hy.
                    {
                        exists t.
                        reflexivity.
                    }
                    {
                        assumption.
                    }
                }
                {
                    inversion Hy.
                }
            }
            {
                intros [Hib Hiv].
                split>[assumption|].
                rewrite elem_of_dom.
                rewrite elem_of_dom in Hib.
                intros HContra.
                apply Hib. clear Hib.
                destruct HContra as [y Hy].
                rewrite map_lookup_filter.
                rewrite Hy.
                simpl.
                rewrite option_guard_True.
                {
                    exists y.
                    reflexivity.
                }
                {
                    assumption.
                }
            }
        }
        {
            apply map_eq.
            intros i.
            rewrite lookup_fmap.
            rewrite map_lookup_filter.
            rewrite lookup_fmap.
            unfold subp_restrict.
            unfold SubP in *.
            rewrite map_lookup_filter.
            destruct (b !! i) eqn:Hbi.
            {
                simpl in *.
                rewrite option_guard_decide.
                destruct (decide (i ∈ vars)).
                {
                    simpl.
                    apply f_equal.
                    f_equal.
                    symmetry.
                    apply map_filter_id.
                    intros i0 x0 Hai0.
                    simpl.
                    apply elem_of_dom_2 in Hai0.
                    clear -Hai0 Hva.
                    ltac1:(set_solver).
                }
                {
                    simpl. reflexivity.
                }
            }
            {
                simpl in *.
                reflexivity.
            }
        }
    }
    {
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite lookup_fmap in Hy.
        rewrite map_lookup_filter in Hx.
        simpl in *.
        destruct (a !! i) eqn:Hai.
        {
            destruct (b !! i) eqn:Hbi.
            {
                simpl in Hx.
                rewrite option_guard_False in Hx.
                {
                    simpl in Hx.
                    inversion Hx.
                }
                {
                    intros Hin.
                    unfold subp_dom in Hin.
                    unfold SubP in *.
                    rewrite elem_of_dom in Hin.
                    rewrite Hbi in Hin.
                    apply Hin.
                    exists t0.
                    reflexivity.
                }
            }
            {
                simpl in Hy.
                inversion Hy.
            }
        }
        {
            simpl in Hx.
            inversion Hx.
        }
    }
Qed.


Lemma to_serial_then_to_parallel
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    subp_is_normal m ->
    subp_restrict (dom m) (make_parallel (make_serial m)) = m
.
Proof.
    intros Hnorm.
    unfold make_serial.
    rewrite make_parallel_app.
    rewrite make_parallel_map_to_list.
    ltac1:(rewrite make_parallel_map_to_list).
    rewrite subp_union_is_compose__sometimes_1.
    { 
      rewrite subp_compose_assoc.
      {
        
        admit.
      }
      {
        Search subp_is_normal.
        admit.
      }
    }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    rewrite map_union_comm.
    {
        (*rewrite subp_union_is_compose__sometimes.
        {
            rewrite subp_compose_assoc.
            admit.
        }
        {
          admit.
        }
        *)
        admit.
    }
    {
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        (* This has to be simpler. If [i] is in the domain of the composition, then [i] is in the domain of one of the inputs.
          Then, if [i] is in [m], then surely it HAS TO BE in the renaming, so this sucks, because this property does not hold.
        
         *)
        Search subp_compose.
        unfold subp_compose in Hy.
        unfold subp_normalize in Hy.
        rewrite map_lookup_filter in Hy.
        rewrite lookup_union in Hy.
        rewrite lookup_fmap in Hy.
        rewrite map_lookup_filter in Hy.
        unfold rlift in Hx.
        rewrite lookup_fmap in Hx.
        simpl in *.
        unfold rlift in Hy.
        rewrite lookup_fmap in Hy.
        destruct (m !! i) eqn:Hmi,
            (renaming_for m !! i) eqn:Hri,
            (r_inverse (renaming_for m) !! i) eqn:Hiri
        .
        {
            simpl in *.
            ltac1:(rewrite Hiri in Hy).
            simpl in Hy.
            unfold r_inverse in Hiri.
            destruct (m !! v0) eqn:Hmv0.
            {
              ltac1:(rewrite Hmv0 in Hy).
              simpl in Hy.
              rewrite option_guard_decide in Hy.
              ltac1:(case_match); simpl in *.
              {
                clear H. ltac1:(rename n into H).
                unfold subp_dom in H.
                ltac1:(rewrite elem_of_dom in H).
                apply H. clear H.
                unfold r_inverse.
                rewrite lookup_fmap.
                ltac1:(rewrite Hiri).
                simpl.
                eexists. reflexivity.
              } 
              {
                clear H. ltac1:(rename n into H).
                rewrite option_guard_decide in Hy.
                ltac1:(case_match); simpl in *.
                {
                  ltac1:(simplify_eq/=).
                  clear H0. ltac1:(rename n into H0).
                  apply dec_stable in H.
                  unfold subp_dom in H.
                  ltac1:(rewrite elem_of_dom in H).
                  destruct H as [z Hz].
                  rewrite lookup_fmap in Hz.
                  unfold r_inverse in Hz.
                  ltac1:(rewrite Hiri in Hz).
                  ltac1:(simplify_eq/=).
                  
                  ltac1:(rewrite - elem_of_list_to_map in Hiri).
                  {
                      rewrite <- list_fmap_compose.
                      unfold compose.
                      simpl.
                      apply renaming_ok_nodup.
                      apply renaming_for_ok.    
                  }
                  rewrite elem_of_list_fmap in Hiri.
                  destruct Hiri as [[z1 z2][HH1 HH2]].
                  ltac1:(simplify_eq/=).
                  ltac1:(rewrite elem_of_map_to_list in HH2).
                  ltac1:(simplify_eq/=).
                  ltac1:(rewrite Hri in Hx).
                  simpl in Hx.
                  ltac1:(simplify_eq/=).
                  (* Now, HH2 and Hmi are in conflict *)
                  unfold renaming_for in HH2.
                  ltac1:(rewrite - elem_of_list_to_map in HH2).
                  {
                    rewrite fst_zip.
                    { apply NoDup_elements. }
                    {
                      rewrite length_fresh_var_seq.
                      ltac1:(lia).
                    }
                  }
                  apply elem_of_zip_l in HH2 as HH3.
                  apply elem_of_zip_r in HH2 as HH4.
                  clear HH2.
                  apply elem_of_fresh_var_seq in HH4.
                  
                  unfold renaming_for in Hri.
                  ltac1:(rewrite - elem_of_list_to_map in Hri).
                  {
                      rewrite fst_zip.
                      { apply NoDup_elements. }
                      {
                        rewrite length_fresh_var_seq.
                        ltac1:(lia).
                      }
                  }
                  apply elem_of_zip_l in Hri as HH5.
                  clear - HH5 HH4.
                  ltac1:(set_solver).
                }
                {
                  inversion Hy.
                }
              }
            }
            {
              ltac1:(rewrite Hmv0 in Hy).
              rewrite option_guard_decide in Hy.
              unfold subp_dom in Hy.
              unfold SubP in *.
              ltac1:(case_match).
              {
                clear H. ltac1:(rename n into H).
                ltac1:(rewrite elem_of_dom in H).              
                simpl in Hy.
                ltac1:(rewrite Hri in Hx).
                simpl in Hx.
                ltac1:(simplify_eq/=).
                rewrite option_guard_decide in Hy.
                ltac1:(case_match).
                {
                  clear H0. ltac1:(rename n into H0).
                  ltac1:(simplify_eq/=).
                  unfold r_inverse in H.
                  rewrite lookup_fmap in H.
                  ltac1:(rewrite Hiri in H).
                  simpl in H.
                  apply H.
                  eexists. reflexivity.
                }
                {
                  clear H0.
                  apply dec_stable in n.
                  subst t.
                  inversion Hy.
                }
              }
              {
                clear H. ltac1:(rename n into H).
                apply dec_stable in H.
                ltac1:(rewrite elem_of_dom in H).
                rewrite lookup_fmap in H.
                rewrite (left_id None union) in Hy.
                simpl in Hy.
                rewrite option_guard_decide in Hy.
                ltac1:(case_match).
                {
                  clear H0. ltac1:(rename n into H0).
                  ltac1:(simplify_eq/=).
                  unfold r_inverse in H.
                  ltac1:(rewrite Hiri in H).
                  simpl in H.
                  clear H.
                  ltac1:(rewrite - elem_of_list_to_map in Hiri).
                  {
                      rewrite <- list_fmap_compose.
                      unfold compose.
                      simpl.
                      apply renaming_ok_nodup.
                      apply renaming_for_ok.
                  }
                  rewrite elem_of_list_fmap in Hiri.
                  destruct Hiri as [[z1 z2][HH1 HH2]].
                  ltac1:(simplify_eq/=).
                  ltac1:(rewrite elem_of_map_to_list in HH2).
                  ltac1:(rewrite Hri in Hx).
                  simpl in Hx.
                  ltac1:(simplify_eq/=).
                  unfold renaming_for in Hri.
                  unfold renaming_for in HH2.
                  ltac1:(rewrite - elem_of_list_to_map in Hri).
                  {
                      rewrite fst_zip.
                      { apply NoDup_elements. }
                      {
                        rewrite length_fresh_var_seq.
                        ltac1:(lia).
                      }
                  }
                  ltac1:(rewrite - elem_of_list_to_map in HH2).
                  {
                      rewrite fst_zip.
                      { apply NoDup_elements. }
                      {
                        rewrite length_fresh_var_seq.
                        ltac1:(lia).
                      }
                  }
                  apply elem_of_zip_l in Hri.
                  apply elem_of_zip_r in HH2.
                  apply elem_of_fresh_var_seq in HH2.
                  ltac1:(set_solver).
                }
                {
                  clear H0.
                  apply dec_stable in n.
                  inversion Hy.
                }
              }
            }
          }
        {
            simpl in *.
            ltac1:(rewrite Hiri in Hy).
            simpl in Hy.
            unfold subp_dom in Hy.
            unfold SubP in *.
            rewrite (right_id None union) in Hy.
            rewrite option_guard_decide in Hy.
            ltac1:(case_match).
            {
              simpl in *.
              rewrite option_guard_decide in Hy.
              ltac1:(case_match).
              {
                ltac1:(simplify_eq/=).
                clear H H0.
                ltac1:(rename n into H; rename n0 into H0).
                unfold SubP in *.
                ltac1:(rewrite elem_of_dom in H).
                rewrite lookup_fmap in H.
                ltac1:(rewrite Hiri in H).
                simpl in H.
                clear H.
                ltac1:(rewrite Hri in Hx).
                simpl in Hx.
                ltac1:(simplify_eq/=).
                unfold renaming_for in Hri.
                ltac1:(rewrite - elem_of_list_to_map in Hri).
                {
                    rewrite fst_zip.
                    { apply NoDup_elements. }
                    {
                      rewrite length_fresh_var_seq.
                      ltac1:(lia).
                    }
                }
                rewrite elem_of_list_lookup in Hri.
                destruct Hri as [j Hj].
                apply lookup_of_zip_both_2 in Hj.
                destruct Hj as [H1j H2j].
                unfold r_inverse in Hiri.
                unfold RenamingT in *.
                unfold SubP in *.
                apply not_elem_of_list_to_map_2 in Hiri.
                rewrite <- list_fmap_compose in Hiri.
                unfold compose in Hiri.
                simpl in Hiri.
                rewrite elem_of_list_lookup in Hiri.
                ltac1:(setoid_rewrite list_lookup_fmap in Hiri).
                unfold renaming_for in Hiri.
                apply Hiri. clear Hiri.
                rewrite elem_of_list_fmap.
                exists (v, i).
                simpl.
                split>[reflexivity|].
                rewrite elem_of_map_to_list.
                unfold renaming_for.
                ltac1:(rewrite - elem_of_list_to_map).
                {
                    rewrite fst_zip.
                    { apply NoDup_elements. }
                    {
                      rewrite length_fresh_var_seq.
                      ltac1:(lia).
                    }
                }
                rewrite elem_of_list_lookup.
                exists j.
                apply lookup_of_zip_both.
                {
                  exact H1j.
                }
                {
                  apply H2j.
                }
                Search zip lookup.
                apply elem_of_zip_both.
                ltac1:(rewrite lookup_fmap in Hiri).
                ltac1:(rewrite <- not_elem_of_list_to_map in Hiri).
              }
            }

        }
        {
            simpl in *.
            ltac1:(rewrite Hiri in Hy).
            simpl in Hy.
        }
        {
            simpl in *.
            ltac1:(rewrite Hiri in Hy).
            simpl in Hy.
            rewrite (right_id None union) in Hy.
        }
        {
            simpl in *.
            ltac1:(rewrite Hiri in Hy).
            simpl in Hy.
        }
        {
            simpl in *.
            ltac1:(rewrite Hiri in Hy).
            simpl in Hy.
            inversion Hy.
        }
        {
            simpl in *.
            ltac1:(rewrite Hiri in Hy).
            simpl in Hy.
        }
        {
            simpl in *.
            ltac1:(rewrite Hiri in Hy).
            simpl in Hy.
            inversion Hy.
        }
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
