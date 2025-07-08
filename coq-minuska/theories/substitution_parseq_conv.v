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
    Logic.PropExtensionality
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

Definition renaming_ok {Σ : StaticModel} (r : (gmap variable variable)) : Prop :=
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
    (r : (gmap variable variable))
    (x y : variable)
:
    x ∉ dom r ->
    renaming_ok (<[x:=y]>r) ->
    renaming_ok r
.
Proof.
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

Definition pair_swap {A B : Type} (x : (A*B)) : B*A :=
    (snd x, fst x)
.

Definition r_inverse {Σ : StaticModel} (r : (gmap variable variable)) : (gmap variable variable) :=
    list_to_map (pair_swap <$> (map_to_list r))
.

Lemma renaming_ok_nodup
    {Σ : StaticModel}
    (r : (gmap variable variable))
    :
    renaming_ok r ->
    NoDup ([eta snd] <$> map_to_list r)
.
Proof.
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
    (r : (gmap variable variable))
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
            unfold pair_swap in *.
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

Lemma r_inverse_ok {Σ : StaticModel} (r : (gmap variable variable)) :
    renaming_ok r ->
    renaming_ok (r_inverse r)
.
Proof.
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
    unfold pair_swap in *.
    ltac1:(simplify_eq/=).
    ltac1:(rewrite elem_of_map_to_list in HH12).
    ltac1:(rewrite elem_of_map_to_list in HH22).
    ltac1:(simplify_eq/=).
    reflexivity.
Qed.

Lemma r_inverse_inverse {Σ : StaticModel} (r : (gmap variable variable)) :
    renaming_ok r ->
    r_inverse (r_inverse r) = r
.
Proof.
    intros Hok.
    unfold r_inverse.
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
        unfold pair_swap in *.
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
    (gmap variable variable)
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
        eapply NoDup_lookup>[|apply H2|apply H4].
        apply NoDup_fresh_var_seq.
    }
    subst j.
    ltac1:(simplify_eq/=).
    reflexivity.
Qed.

Definition rlift
    {Σ : StaticModel}
    (r : (gmap variable variable))
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
    (map_to_list (subp_compose (rlift r) s ))
    ++
    (map_to_list (rlift rinv))
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
    : (gmap variable variable)
:=
    set_to_map (fun x => (x,x)) vs
.

Lemma compose_renaming_inverse_restrict
    {Σ : StaticModel}
    (r : (gmap variable variable))
    (vars : gset variable)
    :
    renaming_ok r ->
    map_img r ∩ vars ⊆ dom r  ->
    subp_restrict vars ((subp_compose (rlift (r_inverse r)) (rlift r))) = subp_id
.
Proof.
    intros Hrok Hvars.
    unfold subp_restrict,subp_compose,subp_id.
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
                unfold pair_swap in *.
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
                    (* rewrite elem_of_dom in HH1. *)
                    (* destruct HH1 as [y Hy]. *)
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
                    unfold pair_swap in *.
                    ltac1:(simplify_eq/=).
                    ltac1:(rewrite elem_of_map_to_list in H'2z).
                    assert(Htmp := Hrok _ _ _ H1ri H'2z).
                    subst.
                    ltac1:(simplify_eq/=).
                }
                {
                    clear HH1.
                    unfold rlift,r_inverse in H.
                    unfold SubP in *.
                    rewrite lookup_fmap in H.
                    rewrite fmap_None in H.
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
            unfold SubP in *.
            rewrite lookup_fmap in Hnri.
            rewrite fmap_None in Hnri.
            rewrite <- not_elem_of_list_to_map in Hnri.
            rewrite <- list_fmap_compose in Hnri.
            unfold compose in Hnri.
            simpl in Hnri.
            (* rewrite elem_of_dom in H1. *)
            rewrite elem_of_list_fmap in Hnri.
            (* destruct H1 as [z Hz]. *)
            unfold rlift in Hri.
            rewrite lookup_fmap in Hri.
            unfold SubP in *.
            ltac1:(rewrite fmap_Some in Hri).
            destruct Hri as [y [H1y H2y]].
            ltac1:(simplify_eq/=).
            destruct (rlift (r_inverse r) !! y) eqn:H2z.
            {
                unfold rlift, r_inverse in H2z.
                unfold SubP in *.
                rewrite lookup_fmap in H2z.
                rewrite fmap_Some in H2z.
                destruct H2z as [y' [H1y' H2y']].
                ltac1:(simplify_eq/=).
                ltac1:(rewrite - elem_of_list_to_map in H1y').
                {
                    rewrite <- list_fmap_compose.
                    unfold compose. simpl.
                    apply renaming_ok_nodup.
                    exact Hrok.
                }
                unfold SubP in *.
                (* rewrite list_lookup_fmap in H1y. *)
                rewrite elem_of_list_fmap in H1y'.
                destruct H1y' as [[z1 z2][H1z H2z]].
                unfold pair_swap in *.
                ltac1:(simplify_eq/=).
                rewrite elem_of_map_to_list in H2z.
                assert(Htmp := Hrok _ _ _ H1y H2z).
                subst i.
                ltac1:(contradiction H2).
                reflexivity.
            }
            {
                unfold rlift, r_inverse in H2z.
                unfold SubP in *.
                rewrite lookup_fmap in H2z.
                rewrite fmap_None in H2z.
                rewrite <- not_elem_of_list_to_map in H2z.
                rewrite <- list_fmap_compose in H2z.
                unfold compose in H2z.
                simpl in H2z.
                rewrite elem_of_list_fmap in H2z.
                apply H2z. clear H2z.
                exists (i, y).
                simpl.
                split>[reflexivity|].
                rewrite elem_of_map_to_list.
                exact H1y.
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
                (* rewrite elem_of_dom. *)
                (* rewrite Hri. *)
                intros [HH1 HH2].
                unfold rlift,r_inverse in Hnri.
                unfold rlift in Hri.
                rewrite lookup_fmap in Hnri.
                rewrite lookup_fmap in Hri.
                destruct (r !! i) eqn:Hri2.
                {
                    simpl in Hri. inversion Hri.
                }
                {
                    apply not_elem_of_dom in Hri2.
                    clear Hri.
                    rewrite fmap_Some in Hnri.
                    destruct Hnri as [q [H1q H2q]].
                    ltac1:(simplify_eq/=).
                    ltac1:(rewrite - elem_of_list_to_map in H1q).
                    {
                        rewrite <- list_fmap_compose.
                        unfold compose.
                        simpl.
                        apply renaming_ok_nodup.
                        apply Hrok.
                    }
                    rewrite elem_of_list_fmap in H1q.
                    destruct H1q as [[z1 z2][H1z H2z]].
                    unfold pair_swap in H1z.
                    simpl in *.
                    symmetry in H1z.
                    ltac1:(simplify_eq/=).
                    rewrite elem_of_map_to_list in H2z.
                    assert (i ∈ ((@map_img variable variable (gmap variable variable) _ (gset variable) _ _ _ r))).
                    {
                        apply elem_of_map_img.
                        exists q.
                        exact H2z.
                    }
                    clear - Hvars HH1 Hri2 H.
                    apply Hri2. clear Hri2.
                    rewrite elem_of_subseteq in Hvars.
                    specialize (Hvars i).
                    rewrite elem_of_intersection in Hvars.
                    specialize (Hvars (conj H HH1)).
                    exact Hvars.
                }
            }
        }
        {
            rewrite elem_of_dom.
            ltac1:(rewrite Hri).
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
    rewrite map_filter_union.
    {
        rewrite map_filter_fmap.
        simpl.
        unfold subp_compose.
        unfold subp_normalize.
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

Lemma subp_is_normal_restrict
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    :
    subp_is_normal m ->
    subp_is_normal (subp_restrict vars m)
.
Proof.
    intros Hm.
    unfold subp_is_normal, subp_restrict, subp_normalize in *.
    unfold SubP in *.
    rewrite map_filter_comm.
    ltac1:(rewrite Hm).
    reflexivity.
Qed.
(* 
#[export]
Instance subp_is_normal_proper {Σ : StaticModel}: Proper ((≡) ==> flip impl) subp_is_normal.
Proof.
    intros a.
Qed. *)

#[export]
Instance pair_swap_perm {A B : Type}: Proper ((≡ₚ) ==> (≡ₚ)) (fmap (@pair_swap A B)).
Proof.
    intros x y Hxy.
    apply fmap_Permutation.
    exact Hxy.
Qed.

Lemma pair_swap_zip
    {A B : Type}
    (la : list A)
    (lb : list B)
    :
    pair_swap <$> (zip la lb) = zip lb la
.
Proof.
    revert lb.
    induction la; intros lb.
    {
        destruct lb.
        {
            reflexivity.
        }
        {
            reflexivity.
        }
    }
    {
        destruct lb.
        {
            reflexivity.
        }
        {
            simpl.
            f_equal.
            apply IHla.
        }
    }
Qed.

Lemma subp_is_normal_spec
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    subp_is_normal m <->
    (
        forall (k : variable) (v : TermOver BuiltinOrVar), m !! k = Some v -> t_over (bov_variable k) <> v
    )
.
Proof.
    unfold subp_is_normal.
    unfold subp_normalize.
    unfold SubP in *.
    split.
    {
        intros H.
        intros k v Hkv HContra.
        subst v.
        rewrite <- H in Hkv.
        rewrite map_lookup_filter in Hkv.
        rewrite bind_Some in Hkv.
        destruct Hkv as [v [H1v H2v]].
        simpl in H2v.
        rewrite option_guard_decide in H2v.
        ltac1:(case_match; simplify_eq/=).
    }
    {
        intros H.
        apply map_filter_id.
        simpl.
        ltac1:(naive_solver).
    }
Qed.

Lemma dom_subp_compose_subseteq
    {Σ : StaticModel}
    (a b : SubP)
    :
    dom (subp_compose a b) ⊆ dom a ∪ dom b
.
Proof.
    unfold subp_compose.
    unfold SubP in *.
    unfold subp_normalize.
    eapply transitivity>[apply dom_filter_subseteq|].
    rewrite dom_union.
    apply union_mono.
    {
        eapply transitivity>[apply dom_filter_subseteq|].
        apply reflexivity.
    }
    {
        rewrite dom_fmap.
        apply reflexivity.
    }
Qed.

Lemma restrict_more
    {Σ : StaticModel}
    (a b : gmap variable (TermOver BuiltinOrVar))
    (vars vars' : gset variable)
:
    vars' ⊆ vars ->
    subp_restrict vars a = subp_restrict vars b ->
    subp_restrict vars' a = subp_restrict vars' b
.
Proof.
    intros H1 H2.
    unfold subp_restrict in *.
    unfold SubP in *.
    rewrite map_eq_iff in H2.
    apply map_eq.
    intros i.
    rewrite map_lookup_filter.
    rewrite map_lookup_filter.
    specialize (H2 i).
    rewrite map_lookup_filter in H2.
    rewrite map_lookup_filter in H2.
    destruct (a !! i) eqn:Hai, (b !! i) eqn:Hbi.
    {
        simpl.
        rewrite option_guard_decide.
        rewrite option_guard_decide.
        ltac1:(case_match; simplify_eq/=; try reflexivity).
        simpl in H2.
        rewrite option_guard_decide in H2.
        rewrite option_guard_decide in H2.
        ltac1:(case_match; simplify_eq/=).
        { reflexivity. }
        {
            ltac1:(exfalso).
            clear H H0.
            ltac1:(set_solver).
        }
    }
    {
        simpl.
        simpl in H2.
        rewrite option_guard_decide.
        rewrite option_guard_decide in H2.
        ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
        { clear H H0. ltac1:(set_solver). }
    }
    {
        simpl.
        simpl in H2.
        rewrite option_guard_decide.
        rewrite option_guard_decide in H2.
        ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
        { clear H H0. ltac1:(set_solver). }
    }
    {
        reflexivity.
    }
Qed.

Lemma restrict_filter
    {Σ : StaticModel}
    (a b : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    (P : prod variable (TermOver BuiltinOrVar) -> Prop)
    {EP : forall x, Decision (P x)}
    :
    subp_restrict vars a = subp_restrict vars b ->
    subp_restrict vars (filter P a) = subp_restrict vars (filter P b)
.
Proof.
    intros HH.
    unfold subp_restrict in *.
    unfold SubP in *.
    rewrite map_filter_filter.
    rewrite map_filter_filter.

    rewrite map_eq_iff in HH.
    apply map_eq.
    intros i.
    rewrite map_lookup_filter.
    rewrite map_lookup_filter.
    specialize (HH i).
    rewrite map_lookup_filter in HH.
    rewrite map_lookup_filter in HH.
    destruct (a !! i) eqn:Hai, (b !! i) eqn:Hbi.
    {
        simpl.
        rewrite option_guard_decide.
        rewrite option_guard_decide.
        ltac1:(case_match; simplify_eq/=; try reflexivity).
        simpl in HH.
        rewrite option_guard_decide in HH.
        rewrite option_guard_decide in HH.
        ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
        {
            ltac1:(exfalso).
            clear H H0.
            ltac1:(set_solver).
        }
        {
            ltac1:(exfalso).
            clear H H0.
            ltac1:(set_solver).
        }
        {
            ltac1:(exfalso).
            clear H H0.
            ltac1:(set_solver).
        }
        {
            (* ltac1:(exfalso). *)
            clear H H0.
            apply not_and_or in n.
            rewrite option_guard_decide in HH.
            rewrite option_guard_decide in HH.
            destruct n as [H1|H1].
            {
                ltac1:(repeat case_match; simplify_eq/=; try naive_solver).
            }
            {
                ltac1:(repeat case_match; simplify_eq/=; try naive_solver).
                clear H0.
                destruct a0 as [H2 H3].
                ltac1:(contradiction n).
            }
        }
    }
    {
        simpl.
        simpl in HH.
        rewrite option_guard_decide.
        rewrite option_guard_decide in HH.
        ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
        { clear H H0. ltac1:(set_solver). }
    }
    {
        simpl.
        simpl in HH.
        rewrite option_guard_decide.
        rewrite option_guard_decide in HH.
        ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
        { clear H H0. ltac1:(set_solver). }
    }
    {
        reflexivity.
    }
Qed.

Lemma restrict_equiv_2
    {Σ : StaticModel}
    (a b d : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    :
    subp_restrict vars b = subp_restrict vars d ->
    subp_restrict vars (subp_compose a b) = subp_restrict vars (subp_compose a d)
.
Proof.
    intros H2.
    unfold subp_compose.
    unfold subp_normalize.
    unfold subp_restrict.
    unfold SubP in *.
    rewrite map_filter_comm.
    symmetry.
    rewrite map_filter_comm.
    symmetry.
    f_equal.
    rewrite map_filter_union.
    {
        symmetry.
        rewrite map_filter_union.
        {
            symmetry.
            f_equal.
            {
                rewrite map_filter_filter.
                rewrite map_filter_filter.
                simpl.
                apply map_eq.
                intros i.
                rewrite map_lookup_filter.
                rewrite map_lookup_filter.
                destruct (a !! i) eqn:Hai.
                {
                    simpl.
                    rewrite option_guard_decide.
                    rewrite option_guard_decide.
                    unfold subp_dom.
                    unfold SubP in *.
                    apply elem_of_dom_2 in Hai as Hai'.
                    rewrite map_eq_iff in H2.
                    specialize (H2 i).
                    unfold subp_restrict in H2.
                    unfold SubP in *.
                    rewrite map_lookup_filter in H2.
                    rewrite map_lookup_filter in H2.
                    destruct (b !! i) eqn:Hbi, (d !! i) eqn:Hdi;
                        ltac1:(simplify_eq/=).
                    {
                        apply elem_of_dom_2 in Hbi as Hbi'.
                        apply elem_of_dom_2 in Hdi as Hdi'.
                        ltac1:(repeat case_match; simplify_eq/=;
                            try naive_solver).
                        {
                            clear H0 H3.
                            ltac1:(naive_solver).
                        }
                        {
                            clear H0 H3.
                            ltac1:(naive_solver).
                        }
                    }
                    {
                        apply elem_of_dom_2 in Hbi as Hbi'.
                        apply not_elem_of_dom_2 in Hdi as Hdi'.
                        rewrite option_guard_decide in H2.
                        ltac1:(repeat case_match; simplify_eq/=;
                            try naive_solver).
                        {
                            clear H0 H3.
                            ltac1:(naive_solver).
                        }
                        {
                            clear H0 H3.
                            ltac1:(naive_solver).
                        }
                    }
                    {
                        apply not_elem_of_dom_2 in Hbi as Hbi'.
                        apply elem_of_dom_2 in Hdi as Hdi'.
                        rewrite option_guard_decide in H2.
                        ltac1:(repeat case_match; simplify_eq/=;
                            try naive_solver).
                        {
                            clear H0 H1 H3.
                            ltac1:(naive_solver).
                        }
                        {
                            clear H0 H1 H3.
                            ltac1:(naive_solver).
                        }
                    }
                    {
                        apply not_elem_of_dom_2 in Hbi as Hbi'.
                        apply not_elem_of_dom_2 in Hdi as Hdi'.
                        ltac1:(repeat case_match; simplify_eq/=;
                            try naive_solver).
                        {
                            clear H H0 H2 H3.
                            ltac1:(naive_solver).
                        }
                        {
                            clear H H0 H2 H3.
                            ltac1:(naive_solver).
                        }
                    }
                }
                {
                    reflexivity.
                }
            }
            {
                rewrite map_filter_fmap.
                rewrite map_filter_fmap.
                f_equal.
                apply H2.
            }
        }
        {
            apply map_disjoint_spec.
            intros i x y Hx Hy.
            rewrite lookup_fmap in Hy.
            rewrite map_lookup_filter in Hx.
            destruct (a !! i) eqn:Hai;
                simpl in *; ltac1:(simplify_eq/=).
            { rewrite option_guard_False in Hx.
            
                { simpl in Hx.
                inversion Hx. }      
                {
                    intros HH. apply HH. clear HH.
                    unfold subp_dom.
                    rewrite fmap_Some in Hy.
                    destruct Hy as [z [H1z H2z]].
                    ltac1:(simplify_eq/=).
                    apply elem_of_dom_2 in H1z.
                    exact H1z.
                }
            }
        }
    }
    {
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite lookup_fmap in Hy.
        rewrite map_lookup_filter in Hx.
        destruct (a !! i) eqn:Hai, (b !! i) eqn:Hbi;
            simpl in *; ltac1:(simplify_eq/=).
        rewrite option_guard_False in Hx.
        { inversion Hx. }
        {
            intros HH. apply HH. clear HH.
            unfold subp_dom.
            apply elem_of_dom_2 in Hbi.
            exact Hbi.
        }
    }
Qed.

Lemma restrict_id
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    :
    (dom m) ⊆ vars ->
    subp_restrict vars m = m
.
Proof.
    intros Hdm.
    unfold subp_restrict.
    unfold SubP in *.
    apply map_filter_id.
    intros i x Hix.
    simpl.
    apply elem_of_dom_2 in Hix.
    ltac1:(set_solver).
Qed.

Lemma subp_app_restrict
    {Σ : StaticModel}
    (a : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    (p : TermOver BuiltinOrVar)
    :
    vars_of p ⊆ vars ->
    subp_app (subp_restrict vars a) p = subp_app a p
.
Proof.
    induction p; intros Hvars; simpl in *.
    {
        destruct a0; simpl.
        { reflexivity. }
        {
            unfold subp_restrict.
            unfold SubP in *.
            rewrite map_lookup_filter.
            destruct (a !! x) eqn:Hax.
            {
                simpl.
                unfold vars_of in Hvars; simpl in Hvars.
                unfold vars_of in Hvars; simpl in Hvars.
                rewrite option_guard_True.
                { reflexivity. }
                {
                    (* apply elem_of_dom_2 in Hax. *)
                    rewrite singleton_subseteq_l in Hvars.
                    exact Hvars.
                }
            }
            {
                simpl.
                reflexivity.
            }
        }
    }
    {
        f_equal.
        ltac1:(replace (map) with (@fmap list list_fmap) by reflexivity).
        apply list_fmap_ext.
        rewrite Forall_forall in H.
        intros i x Hix.
        unfold SubP in *.
        apply elem_of_list_lookup_2 in Hix as Hix'.
        specialize (H x Hix').
        rewrite vars_of_t_term in Hvars.
        apply take_drop_middle in Hix as Hix''.
        rewrite <- Hix'' in Hvars.
        rewrite fmap_app in Hvars.
        rewrite union_list_app in Hvars.
        rewrite fmap_cons in Hvars.
        rewrite union_list_cons in Hvars.
        specialize (H ltac:(set_solver)).
        apply H.
    }
Qed.

Lemma restrict_equiv_1
    {Σ : StaticModel}
    (a b c : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    :
    subp_codom b ⊆ vars ->
    subp_restrict vars a = subp_restrict vars c ->
    subp_restrict vars (subp_compose a b) = subp_restrict vars (subp_compose c b)
.
Proof.
    intros H1 H2.
    unfold subp_compose.
    unfold subp_normalize.
    unfold subp_restrict.
    unfold SubP in *.
    rewrite map_filter_comm.
    symmetry.
    rewrite map_filter_comm.
    symmetry.
    f_equal.
    rewrite map_filter_union.
    {
        symmetry.
        rewrite map_filter_union.
        {
            symmetry.
            f_equal.
            {
                rewrite map_filter_filter.
                rewrite map_filter_filter.
                simpl.
                apply map_eq.
                intros i.
                rewrite map_lookup_filter.
                rewrite map_lookup_filter.

                rewrite map_eq_iff in H2.
                specialize (H2 i).
                unfold subp_restrict in H2.
                unfold SubP in *.
                rewrite map_lookup_filter in H2.
                rewrite map_lookup_filter in H2.
                destruct (a !! i) eqn:Hai, (c !! i) eqn:Hci.
                {
                    simpl.
                    rewrite option_guard_decide.
                    (* rewrite option_guard_decide. *)
                    unfold subp_dom.
                    unfold SubP in *.
                    apply elem_of_dom_2 in Hai as Hai'.
                    rewrite option_guard_decide.
                    apply elem_of_dom_2 in Hci as Hci'.
                    ltac1:(repeat case_match; simplify_eq/=;
                        try naive_solver).
                    {
                        
                        rewrite option_guard_decide in H2.
                        rewrite option_guard_decide in H2.
                        ltac1:(repeat case_match; simplify_eq/=;
                        try naive_solver).
                        clear H H0.
                        ltac1:(naive_solver).
                    }
                }
                {
                    simpl in *.
                    rewrite option_guard_decide.
                    rewrite option_guard_decide in H2.
                    ltac1:(repeat case_match; simplify_eq/=;
                        try naive_solver).
                    {
                        clear H0 H.
                        ltac1:(naive_solver).
                    }
                }
                {
                    simpl in *.
                    rewrite option_guard_decide.
                    rewrite option_guard_decide in H2.
                    ltac1:(repeat case_match; simplify_eq/=;
                        try naive_solver).
                    {
                        clear H0 H.
                        ltac1:(naive_solver).
                    }
                }
                {
                    reflexivity.
                }
            }
            {
                rewrite map_filter_fmap.
                rewrite map_filter_fmap.
                simpl.
                apply map_eq.
                intros i.
                rewrite lookup_fmap.
                rewrite lookup_fmap.
                rewrite map_lookup_filter.
                destruct (b !! i) eqn:Hbi; simpl; try reflexivity.
                rewrite option_guard_decide.
                destruct (decide ( i ∈ vars)).
                {
                    simpl.
                    apply f_equal.
                    assert (Hvt: vars_of t ⊆ vars).
                    {
                        unfold subp_codom in H1.
                        unfold SubP in *.
                        unfold TermOver in *.
                        assert (Ht: t ∈ ((map_img b):(listset _))).
                        {
                            eapply elem_of_map_img_2.
                            apply Hbi.
                        }
                        apply elem_of_elements in Ht.
                        rewrite elem_of_list_lookup in Ht.
                        destruct Ht as [j Ht].
                        apply take_drop_middle in Ht.
                        rewrite <- Ht in H1.
                        rewrite fmap_app in H1.
                        rewrite fmap_cons in H1.
                        rewrite union_list_app in H1.
                        rewrite union_list_cons in H1.
                        clear - H1.
                        ltac1:(set_solver).
                    }
                    rewrite <- subp_app_restrict with (vars := vars).
                    {
                        rewrite H2.
                        rewrite subp_app_restrict.
                        { reflexivity. }
                        {
                            apply Hvt.
                        }
                    }
                    {
                        apply Hvt.
                    }
                }
                {
                    reflexivity.
                }
            }
        }
        {
            apply map_disjoint_spec.
            intros i x y Hx Hy.
            rewrite lookup_fmap in Hy.
            rewrite map_lookup_filter in Hx.
            destruct (c !! i) eqn:Hci;
                simpl in *; ltac1:(simplify_eq/=).
            { rewrite option_guard_False in Hx.
            
                { simpl in Hx.
                inversion Hx. }      
                {
                    intros HH. apply HH. clear HH.
                    unfold subp_dom.
                    rewrite fmap_Some in Hy.
                    destruct Hy as [z [H1z H2z]].
                    ltac1:(simplify_eq/=).
                    apply elem_of_dom_2 in H1z.
                    exact H1z.
                }
            }
        }
    }
    {
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite lookup_fmap in Hy.
        rewrite map_lookup_filter in Hx.
        destruct (a !! i) eqn:Hai, (b !! i) eqn:Hbi;
            simpl in *; ltac1:(simplify_eq/=).
        rewrite option_guard_False in Hx.
        { inversion Hx. }
        {
            intros HH. apply HH. clear HH.
            unfold subp_dom.
            apply elem_of_dom_2 in Hbi.
            exact Hbi.
        }
    }
Qed.

(* This is probably useless *)
Lemma restrict_equiv_1'
    {Σ : StaticModel}
    (a b c : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    :
    subp_dom b ## vars ->
    subp_restrict vars a = subp_restrict vars c ->
    subp_restrict vars (subp_compose a b) = subp_restrict vars (subp_compose c b)
.
Proof.
    intros H1 H2.
    unfold subp_compose.
    unfold subp_normalize.
    unfold subp_restrict.
    unfold SubP in *.
    rewrite map_filter_comm.
    symmetry.
    rewrite map_filter_comm.
    symmetry.
    f_equal.
    rewrite map_filter_union.
    {
        symmetry.
        rewrite map_filter_union.
        {
            symmetry.
            f_equal.
            {
                rewrite map_filter_filter.
                rewrite map_filter_filter.
                simpl.
                apply map_eq.
                intros i.
                rewrite map_lookup_filter.
                rewrite map_lookup_filter.

                rewrite map_eq_iff in H2.
                specialize (H2 i).
                unfold subp_restrict in H2.
                unfold SubP in *.
                rewrite map_lookup_filter in H2.
                rewrite map_lookup_filter in H2.
                destruct (a !! i) eqn:Hai, (c !! i) eqn:Hci.
                {
                    simpl.
                    rewrite option_guard_decide.
                    (* rewrite option_guard_decide. *)
                    unfold subp_dom.
                    unfold SubP in *.
                    apply elem_of_dom_2 in Hai as Hai'.
                    rewrite option_guard_decide.
                    apply elem_of_dom_2 in Hci as Hci'.
                    ltac1:(repeat case_match; simplify_eq/=;
                        try naive_solver).
                    {
                        
                        rewrite option_guard_decide in H2.
                        rewrite option_guard_decide in H2.
                        ltac1:(repeat case_match; simplify_eq/=;
                        try naive_solver).
                        clear H H0.
                        ltac1:(naive_solver).
                    }
                }
                {
                    simpl in *.
                    rewrite option_guard_decide.
                    rewrite option_guard_decide in H2.
                    ltac1:(repeat case_match; simplify_eq/=;
                        try naive_solver).
                    {
                        clear H0 H.
                        ltac1:(naive_solver).
                    }
                }
                {
                    simpl in *.
                    rewrite option_guard_decide.
                    rewrite option_guard_decide in H2.
                    ltac1:(repeat case_match; simplify_eq/=;
                        try naive_solver).
                    {
                        clear H0 H.
                        ltac1:(naive_solver).
                    }
                }
                {
                    reflexivity.
                }
            }
            {
                rewrite map_filter_fmap.
                rewrite map_filter_fmap.
                simpl.
                apply map_eq.
                intros i.
                rewrite lookup_fmap.
                rewrite lookup_fmap.
                rewrite map_lookup_filter.
                destruct (b !! i) eqn:Hbi; simpl; try reflexivity.
                rewrite option_guard_decide.
                destruct (decide ( i ∈ vars)) as [Hin|Hnotin].
                {
                    apply elem_of_dom_2 in Hbi.
                    clear - Hbi Hin H1.
                    ltac1:(set_solver).
                }
                {
                    reflexivity.
                }
            }
        }
        {
            apply map_disjoint_spec.
            intros i x y Hx Hy.
            rewrite lookup_fmap in Hy.
            rewrite map_lookup_filter in Hx.
            destruct (c !! i) eqn:Hci;
                simpl in *; ltac1:(simplify_eq/=).
            { rewrite option_guard_False in Hx.
            
                { simpl in Hx.
                inversion Hx. }      
                {
                    intros HH. apply HH. clear HH.
                    unfold subp_dom.
                    rewrite fmap_Some in Hy.
                    destruct Hy as [z [H1z H2z]].
                    ltac1:(simplify_eq/=).
                    apply elem_of_dom_2 in H1z.
                    exact H1z.
                }
            }
        }
    }
    {
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite lookup_fmap in Hy.
        rewrite map_lookup_filter in Hx.
        destruct (a !! i) eqn:Hai, (b !! i) eqn:Hbi;
            simpl in *; ltac1:(simplify_eq/=).
        rewrite option_guard_False in Hx.
        { inversion Hx. }
        {
            intros HH. apply HH. clear HH.
            unfold subp_dom.
            apply elem_of_dom_2 in Hbi.
            exact Hbi.
        }
    }
Qed.


Lemma dom_renaming_for
    {Σ : StaticModel}
    (a : SubP)
    :
    dom (renaming_for a) = subp_dom a
.
Proof.
    unfold subp_dom, subp_codom, renaming_for.
    unfold SubP in *.
    rewrite dom_list_to_map_L.
    rewrite fst_zip.
    rewrite list_to_set_elements_L.
    reflexivity.
    unfold SubP in *.
    rewrite length_fresh_var_seq.
    ltac1:(lia).
Qed.

Lemma subp_restrict_id_2
    {Σ : StaticModel}
    (vars : gset variable)
    :
    subp_restrict vars subp_id = subp_id
.
Proof.
    unfold subp_restrict, subp_id.
    unfold SubP in *.
    rewrite map_filter_empty.
    reflexivity.
Qed.

Lemma renaming_is_normal
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    subp_is_normal (rlift (renaming_for m))
.
Proof.
    rewrite subp_is_normal_spec.
    intros k v Hkv HContra.
    subst v.
    unfold rlift in Hkv.
    rewrite lookup_fmap in Hkv.
    destruct (renaming_for m !! k) eqn:Hrmk.
    {
        simpl in Hkv.
        ltac1:(simplify_eq/=).
        unfold renaming_for in Hrmk.
        ltac1:(rewrite - elem_of_list_to_map in Hrmk).
        {
            rewrite fst_zip.
            apply NoDup_elements.
            rewrite length_fresh_var_seq.
            ltac1:(lia).
        }
        apply elem_of_zip_l in Hrmk as H1.
        apply elem_of_zip_r in Hrmk as H2.
        clear Hrmk.
        apply elem_of_fresh_var_seq in H2.
        ltac1:(set_solver).
    }
    {
        inversion Hkv.
    }
Qed.

Lemma map_img_renaming_for_dom
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    map_img (renaming_for m) ## dom m
.
Proof.
    rewrite elem_of_disjoint.
    intros x H1 H2.
    rewrite elem_of_map_img in H1.
    (* rewrite elem_of_dom in H2. *)
    destruct H1 as [i Hi].
    (* destruct H2 as [j Hj]. *)
    unfold renaming_for in Hi.
    ltac1:(rewrite - elem_of_list_to_map in Hi).
    {
        rewrite fst_zip.
        apply NoDup_elements.
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
    apply elem_of_zip_r in Hi.
    apply elem_of_fresh_var_seq in Hi.
    ltac1:(set_solver).
Qed.

Lemma map_img_renaming_for_codom
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    map_img (renaming_for m) ## subp_codom m
.
Proof.
    rewrite elem_of_disjoint.
    intros x H1 H2.
    rewrite elem_of_map_img in H1.
    destruct H1 as [i Hi].
    unfold renaming_for in Hi.
    ltac1:(rewrite - elem_of_list_to_map in Hi).
    {
        rewrite fst_zip.
        apply NoDup_elements.
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
    apply elem_of_zip_r in Hi.
    apply elem_of_fresh_var_seq in Hi.
    unfold subp_codom in H2.
    unfold SubP in *.
    rewrite elem_of_union_list in H2.
    destruct H2 as [X [H1X H2X]].
    rewrite elem_of_list_fmap in H1X.
    destruct H1X as [y [H1y H2y]].
    subst X.
    rewrite elem_of_elements in H2y.
    ltac1:(rewrite map_img_alt in H2y).
    rewrite elem_of_list_to_set in H2y.
    rewrite elem_of_list_lookup in H2y.
    destruct H2y as [j Hj].
    apply take_drop_middle in Hj as Hj'.
    rewrite <- Hj' in Hi.
    rewrite fmap_app in Hi.
    rewrite fmap_cons in Hi.
    rewrite union_list_app in Hi.
    rewrite union_list_cons in Hi.
    rewrite elem_of_app in Hi.
    rewrite elem_of_elements in Hi.
    rewrite elem_of_elements in Hi.
    apply not_or_and in Hi.
    destruct Hi as [H1 H2].
    clear - H2X H2.
    ltac1:(set_solver).
Qed.

Lemma dom_rlift_inverse
    {Σ : StaticModel}
    (r : gmap variable variable)
    :
    dom (rlift (r_inverse r)) = map_img r
.
Proof.
    unfold subp_dom.
    unfold rlift.
    unfold r_inverse.
    unfold SubP in *.
    rewrite dom_fmap_L.
    rewrite dom_list_to_map_L.
    rewrite <- list_fmap_compose.
    unfold compose.
    simpl.
    rewrite map_img_alt_L.
    reflexivity.
Qed.

Lemma map_disjoint_compose_inverse
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
:
    subp_compose (rlift (renaming_for m)) m
    ##ₘ rlift (r_inverse (renaming_for m))
.
Proof.
    apply map_disjoint_spec.
    intros i x y Hx Hy.
    assert(Hdom := dom_subp_compose_subseteq (rlift (renaming_for m)) m).
    apply elem_of_dom_2 in Hx.
    apply elem_of_dom_2 in Hy.
    unfold SubP in *.
    ltac1:(rewrite dom_rlift_inverse in Hy).
    unfold renaming_for in Hy.
    rewrite map_img_alt_L in Hy.
    rewrite map_to_list_to_map in Hy.
    {
        rewrite snd_zip in Hy.
        rewrite elem_of_list_to_set in Hy.
        apply elem_of_fresh_var_seq in Hy.
        rewrite elem_of_app in Hy.
        apply not_or_and in Hy.
        destruct Hy as [H1 H2].
        rewrite elem_of_elements in H1.
        rewrite elem_of_elements in H2.
        unfold rlift in Hdom at 2.
        rewrite dom_fmap in Hdom.
        ltac1:(rewrite dom_renaming_for in Hdom).
        unfold subp_dom in Hdom.
        ltac1:(set_solver).
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
    {
        rewrite fst_zip.
        apply NoDup_elements.
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
Qed.

Lemma map_to_list_union {A B : Type}
    {_EA : EqDecision A}
    {_CA : Countable A}
    (a b : gmap A B)
    :
    dom a ## dom b ->
    map_to_list (a ∪ b) ≡ₚ map_to_list a ++ map_to_list b
.
Proof.
    revert b.
    ltac1:(induction a using map_ind); intros b Hab.
    {
        rewrite (left_id empty union).
        rewrite map_to_list_empty.
        simpl.
        reflexivity.
    }
    {
        rewrite dom_insert_L in Hab.
        rewrite <- insert_union_l.
        rewrite map_to_list_insert.
        {
            rewrite map_to_list_insert.
            {
                simpl.
                rewrite IHa.
                reflexivity.
                ltac1:(set_solver).
            }
            {
                assumption.
            }
        }
        {
            apply not_elem_of_dom_1.
            apply not_elem_of_dom_2 in H.
            ltac1:(set_solver).
        }
    }
Qed.

Lemma list_filter_comm
    {A : Type}
    (l : list A)
    (P Q : A -> Prop)
    {_DP: forall x, Decision (P x)}
    {_DQ: forall x, Decision (Q x)}
    :
    filter P (filter Q l) = filter Q (filter P l)
.
Proof.
    rewrite list_filter_filter.
    rewrite list_filter_filter.
    induction l; simpl.
    {
        rewrite filter_nil.
        rewrite filter_nil.
        reflexivity.
    }
    {
        rewrite filter_cons.
        rewrite filter_cons.
        rewrite IHl.
        ltac1:(repeat case_match; try naive_solver).
        { clear H H0. ltac1:(naive_solver). }
        { clear H H0. ltac1:(naive_solver). }
    }
Qed.

Lemma make_parallel_2
    {Σ : StaticModel}
    (s1 s2 : SubS)
    :
    NoDup (s1 ++ s2).*1 ->
    make_parallel (s1 ++ s2) = subp_compose (make_parallel s2) (make_parallel s1)
.
Proof.
    intros HH.
    unfold make_parallel.
    unfold SubS,SubP in *.
    unfold subp_compose.
    unfold subp_normalize.
    rewrite map_filter_alt.
    rewrite map_filter_alt.
    assert (Hs2 : map_to_list (list_to_map s2) ≡ₚ s2).
    {
        apply map_to_list_to_map.
        rewrite fmap_app in HH.
        rewrite NoDup_app in HH.
        destruct HH as [H1 [H2 H3]].
        exact H3.
    }
    assert(Hs2' : filter (fun kv => kv.1 ∉ subp_dom (list_to_map s1)) (map_to_list (list_to_map s2)) ≡ₚ filter (fun kv => kv.1 ∉ subp_dom (list_to_map s1)) s2).
    {
        eapply (filter_Permutation (fun kv => kv.1 ∉ subp_dom (list_to_map s1))) in Hs2.
        apply Hs2.
    }
    assert(Htmp := @filter_fmap (variable*(TermOver BuiltinOrVar)) variable fst (fun (x:variable) => x ∉ subp_dom (list_to_map s1)) _ _ s2).
    unfold compose in Htmp.
    
    apply list_to_map_proper in Hs2'.
    {
        ltac1:(rewrite Hs2').

        (* About list_to_map. *)
        assert(Hdoms: dom
            (@list_to_map variable (TermOver BuiltinOrVar) (gmap variable (TermOver BuiltinOrVar)) _ _
            (filter
            (λ kv : variable * TermOver BuiltinOrVar,
            kv.1 ∉ subp_dom (list_to_map s1))
            s2))
            ## dom (subp_app (list_to_map s2) <$> (@list_to_map variable (TermOver BuiltinOrVar) (gmap variable (TermOver BuiltinOrVar)) _ _ s1))).
        {
            rewrite dom_list_to_map.
            rewrite dom_fmap.
            rewrite dom_list_to_map.
            setoid_rewrite <- Htmp.
            rewrite elem_of_disjoint.
            intros x H1x H2x.
            rewrite elem_of_list_to_set in H1x.
            rewrite elem_of_list_filter in H1x.
            rewrite elem_of_list_to_set in H2x.
            destruct H1x as [? H1x].
            rewrite fmap_app in HH.
            rewrite NoDup_app in HH.
            destruct HH as [? [HH ?]].
            apply (HH _ H2x H1x).

        }

        symmetry.
        ltac1:(under (list_to_map_proper)).
        {
            apply NoDup_fmap_fst.
            {
                intros x h1 h2 Hy1 Hy2.
                ltac1:(rewrite elem_of_list_filter in Hy1).
                ltac1:(rewrite elem_of_list_filter in Hy2).
                destruct Hy1 as [H1 H2].
                destruct Hy2 as [H3 H4].
                simpl in *.
                rewrite elem_of_map_to_list in H2.
                rewrite elem_of_map_to_list in H4.
                ltac1:(simplify_eq/=).
                reflexivity.
            }
            {
                apply NoDup_filter.
                apply NoDup_map_to_list.
            }
            
        }
        rewrite map_to_list_union.
        {
            rewrite filter_app.
            rewrite map_to_list_to_map.
            {
                rewrite list_filter_comm.
                rewrite map_to_list_fmap.
                ltac1:(over).
            }
            {
                rewrite fmap_app in HH.
                setoid_rewrite <- Htmp.
                apply NoDup_filter.
                rewrite NoDup_app in HH.
                destruct HH as [? [? HH]].
                exact HH.
            }
        }
        { exact Hdoms. }
        symmetry.
        rewrite list_to_map_app.
        rewrite list_to_map_app.
        rewrite list_filter_Forall_all.
        {
            
            admit.
        }
        {
            rewrite Forall_forall.
            intros x H1x H2x.
            rewrite elem_of_list_filter in H1x.
            destruct H1x as [H1x H3x].
            unfold subp_dom in H2x.
            unfold SubP in *.
            rewrite dom_list_to_map in H2x.
            rewrite elem_of_list_to_set in H2x.
            rewrite elem_of_list_fmap in H2x.
            rewrite fmap_app in HH.
            rewrite NoDup_app in HH.
            destruct HH as [? [HH ?]].
            destruct H2x as [y [H1y H2y]].
            destruct x as [x1 x2].
            destruct y as [y1 y2].
            
            ltac1:(simplify_eq/=).
            specialize (HH y1).
            ltac1:(ospecialize (HH _ _)).
            {
                rewrite elem_of_list_fmap.
                exists (y1, y2).
                simpl.
                split>[reflexivity|].
                exact H2y.
            }
            {
                rewrite elem_of_list_fmap.
                exists (y1, x2).
                split>[reflexivity|].
                exact H3x.
            }
            exact HH.
        }
    }
    {
        apply NoDup_fmap_fst.
        {
            intros x h1 h2 Hy1 Hy2.
            ltac1:(rewrite elem_of_list_filter in Hy1).
            ltac1:(rewrite elem_of_list_filter in Hy2).
            destruct Hy1 as [H1 H2].
            destruct Hy2 as [H3 H4].
            simpl in *.
            rewrite elem_of_map_to_list in H2.
            rewrite elem_of_map_to_list in H4.
            ltac1:(simplify_eq/=).
            reflexivity.
        }
        {
            apply NoDup_filter.
            apply NoDup_map_to_list.
        }
    }
Qed.


(* 
Lemma sub_compose_distr
    {Σ : StaticModel}
    (a b c : gmap variable (TermOver BuiltinOrVar))
    :
    dom b ## dom c ->
    subp_compose a (union b c) = union (subp_compose a b) (subp_compose a c)
.
Proof.
    intros Hdom.
    unfold subp_compose.
    unfold subp_normalize.
    rewrite map_filter_union.
    {
        rewrite map_filter_union.
        {
            rewrite <- map_union_assoc.
            (* rewrite map_filter_filter. *)
            (* rewrite map_filter_filter. *)
            rewrite map_filter_union.
            {
                (* rewrite map_filter_filter. *)
                simpl.
                unfold subp_dom in *.
                unfold SubP in *.
                set (fun kv => t_over (bov_variable kv.1) <> kv.2) as P1.
                (* ltac1:(rewrite map_filter_and). *)
                Unset Printing Notations.
                Set Printing Parentheses.
                ltac1:(set (fun '(i, x) => @t_over symbol _ (bov_variable i) <> x /\ i ∉ dom (b ∪ c)) as f).
                (* Set Printing Implicit. *)
                ltac1:(set (fun x => ((t_over (bov_variable x.1) <> x.2 /\ x.1 ∉ dom b) /\ (@t_over symbol BuiltinOrVar (bov_variable x.1) <> x.2 /\ x.1 ∉ dom c))) as g).
                assert(Hfg: f = g).
                {
                    apply functional_extensionality.
                    intros x.
                    subst.
                    destruct x.
                    simpl.
                    apply propositional_extensionality.
                    rewrite dom_union.
                    rewrite elem_of_union.
                    split.
                    {
                        intros [H1 H2].
                        apply not_or_and in H2.
                        destruct H2 as [H2 H3].
                        ltac1:(unfold g).
                        ltac1:(naive_solver).
                    }
                    {
                        intros [[H1 H2][H3 H4]].
                        simpl in *.
                        split; try ltac1:(naive_solver).
                    }    
                }
                assert(Hfg': filter f a = filter g a).
                {
                    apply map_filter_ext.
                    intros i x Hix.
                    rewrite Hfg.
                    reflexivity.
                }
                (* Set Printing Implicit. *)
                ltac1:(rewrite Hfg').
                ltac1:(unfold g).
                rewrite map_filter_and.
                Search filter and.
                (* Check bfilter. *)
                ltac1:(rewrite Hfg).
                (* Search filter and. *)
                (* erewrite functional_extensionality. *)
                (* About map_filter_ext. *)
                (* About map_filter_strong_ext_1. *)
                (* rewrite (map_filter_strong_ext_1 _ f). *)
                (* About map_filter_ext. *)
                (* Search filter. *)
            }
            {
                apply map_disjoint_spec.
                intros i x y Hx Hy.
                rewrite lookup_fmap in Hy.
                rewrite map_lookup_filter in Hx.
                unfold SubP in *.
                destruct (a !! i) eqn:Hai;
                    ltac1:(rewrite Hai in Hx);
                    ltac1:(simplify_eq/=).
                rewrite option_guard_decide in Hx.
                destruct ((c) !! i) eqn:Hci;
                    ltac1:(simplify_eq/=).
                apply elem_of_dom_2 in Hci as Hci'.
                unfold subp_dom in *.
                unfold SubP in *.
                ltac1:(case_match; naive_solver).        
            }
        }
        {
            apply map_disjoint_spec.
            intros i x y Hx Hy.
            rewrite lookup_fmap in Hy.
            rewrite map_lookup_filter in Hx.
            unfold SubP in *.
            destruct (a !! i) eqn:Hai;
                ltac1:(rewrite Hai in Hx);
                ltac1:(simplify_eq/=).
            rewrite option_guard_decide in Hx.
            destruct ((b) !! i) eqn:Hbi;
                ltac1:(simplify_eq/=).
            apply elem_of_dom_2 in Hbi as Hbi'.
            unfold subp_dom in *.
            unfold SubP in *.
            ltac1:(case_match; naive_solver).    
        }
    }
    {
        apply map_disjoint_spec.
        intros i x y Hx Hy.
        rewrite lookup_fmap in Hy.
        rewrite map_lookup_filter in Hx.
        unfold SubP in *.
        destruct (a !! i) eqn:Hai;
            ltac1:(rewrite Hai in Hx);
            ltac1:(simplify_eq/=).
        rewrite option_guard_decide in Hx.
        destruct ((b ∪ c) !! i) eqn:Hbci;
            ltac1:(simplify_eq/=).
        apply elem_of_dom_2 in Hbci as Hbci'.
        unfold subp_dom in *.
        unfold SubP in *.
        ltac1:(case_match; naive_solver).
    }
Qed. *)

Lemma to_serial_then_to_parallel
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    subp_is_normal m ->
    subp_restrict (dom m) (make_parallel (make_serial m)) = m
.
Proof.
    intros 
        (* Hnoloop  *)
        Hnorm.
    unfold make_serial.
    rewrite make_parallel_app.
    rewrite make_parallel_map_to_list.
    ltac1:(rewrite make_parallel_map_to_list).
    rewrite map_union_comm.
    {
        (* THIS is useless *)
        rewrite subp_union_is_compose__sometimes_1.
        {

        }
        {

        } 
    }
    {
        apply map_disjoint_compose_inverse.
    }
    rewrite subp_union_is_compose__sometimes_1.
    { 
        rewrite <- subp_compose_assoc.
        {
            (* rewrite <- (restrict_id m) at 5. *)
            unfold SubP in *.
            Check restrict_id.
            rewrite <- (restrict_id m (dom m)) at 5>[|ltac1:(set_solver)].
            apply restrict_more with (vars := dom m ∪ subp_codom m).
            { ltac1:(set_solver). }
            (* Check restrict_more. *)
            (* Search subp_restrict. *)
            (* erewrite restrict_equiv_1. *)
            (* apply restrict_equiv. *)
            (* Check compose_renaming_inverse_restrict. *)
            rewrite restrict_equiv_1 with (c := subp_id).
            {
                rewrite subp_id_compose.
                {
                    rewrite restrict_id.
                    { reflexivity. }
                    { ltac1:(set_solver). }
                }
                {
                    exact Hnorm.
                }
            }
            {
                ltac1:(set_solver).
            }
            {
                rewrite subp_restrict_id_2.
                rewrite compose_renaming_inverse_restrict.
                {
                    reflexivity.
                }
                {
                    apply renaming_for_ok.
                }
                {
                    assert (H1 := map_img_renaming_for_dom m).
                    assert (H2 := map_img_renaming_for_codom m).
                    ltac1:(set_solver).
                }
            }
            
        }
        {
            apply renaming_is_normal.
        }
    }
    {
        (* This surely cannot be true *)
        apply map_eq.
        intros i.
        rewrite lookup_fmap.
        destruct (subp_compose (rlift (renaming_for m)) m !! i) eqn:Heq.
        {
            simpl.
            apply f_equal.
            rewrite subp_app_almost_closed.
            { reflexivity. }
            {
                rewrite dom_rlift_inverse.
                assert (Htmp1 := map_img_renaming_for_dom (m)).
                assert (Htmp2 := map_img_renaming_for_codom (m)).
                assert (Htmp3 := dom_subp_compose_subseteq (rlift (renaming_for m)) m).


                unfold subp_compose in Heq.
                unfold subp_normalize in Heq.
                unfold SubP in *.

                rewrite map_lookup_filter in Heq.
                rewrite lookup_union in Heq.
                rewrite map_lookup_filter in Heq.
                rewrite lookup_fmap in Heq.
                simpl in Heq.
                rewrite bind_Some in Heq.
                destruct Heq as [y [H1y H2y]].
                rewrite union_Some in H1y.
                unfold SubP in *.
                destruct (rlift (renaming_for m) !! i) eqn:Heq.
                {
                    rewrite option_guard_decide in H2y.
                    ltac1:(case_match; simplify_eq/=).
                    clear H.
                    ltac1:(rewrite Heq in H1y).
                    simpl in H1y.
                    rewrite option_guard_decide in H1y.
                    ltac1:(repeat case_match; simplify_eq/=).
                    {
                        destruct H1y as [H1y|[HContra ?]].
                        {
                            ltac1:(simplify_eq/=).
                            clear H.
                            unfold rlift in Heq.
                            unfold SubP in *.
                            rewrite lookup_fmap in Heq.
                            rewrite fmap_Some in Heq.
                            destruct Heq as [x [H1x H2x]].
                            subst.
                            unfold vars_of; simpl.
                            unfold vars_of; simpl.
                            rewrite disjoint_singleton_l.
                            intros HContra.
                            (* .
                            assert (x ∈ subp_codom m).
                            {
                                unfold subp_codom.
                                unfold SubP in *.
                                
                            }
                            ltac1:(set_solver). *)
                        }
                        {
                            inversion HContra.
                        }
                    }
                    {
                        clear H.
                        destruct H1y as [H1y|[HContra ?]].
                        {
                            ltac1:(simplify_eq/=).
                        }
                        {
                            clear HContra.
(* 
                            lazy_match! goal with
                            | [|- ?l ## _] =>
                                lazy_match! (Constr.type (Control.hyp @Htmp2)) with
                                | (_ ## ?r) => assert(Htmp4: $l ⊆ $r)
                                end
                            end.
                            {
                                
                            } *)
                            ltac1:(set_solver).
                        }
                    }
                }
                {
                    ltac1:(rewrite Heq in H1y).
                    simpl in H1y.
                    destruct H1y as [H1y | [_ H1y]].
                    {
                        inversion H1y.
                    }
                    {
                        rewrite option_guard_decide in H2y.
                        ltac1:(case_match; simplify_eq/=).
                        clear H.
 
                        rewrite fmap_Some in H1y.
                        destruct H1y as [z [H1z H2z]].
                        subst.
                        unfold rlift in Heq.
                        unfold SubP in *.
                        rewrite lookup_fmap in Heq.
                        rewrite fmap_None in Heq.
                        unfold subp_codom in Htmp2.
                        unfold SubP in *.
                        unfold renaming_for in Heq.
                        rewrite <- not_elem_of_list_to_map in Heq.
                        rewrite fst_zip in Heq.
                        apply elem_of_dom_2 in H1z.
                        rewrite elem_of_elements in Heq.
                        ltac1:(contradiction Heq).
                        rewrite length_fresh_var_seq.
                        ltac1:(lia).
                    }
                }

                (* apply elem_of_dom_2 in Heq. *)
                (* ltac1:(set_solver). *)
                Search subp_compose.
                assert (vars_of t ⊆ subp_codom m).
                {
                    unfold subp_compose in Heq.
                    unfold subp_normalize in Heq.
                    admit.
                }
                
                ltac1:(set_solver).
            }
        }
        {
            reflexivity.
        }
    }
    {

    }
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
