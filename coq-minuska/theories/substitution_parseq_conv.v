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
    (avoid0 : gset variable)
    (sub_mm : SubP)
    :
    (gmap variable variable)
:=
    let rhss : list (TermOver BuiltinOrVar) := snd <$> map_to_list sub_mm in
    let avoid : list variable := elements (avoid0 ∪ (union_list (vars_of <$> rhss))) in
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
    (avoid0 : gset variable)
    (s : SubP)
    :
    renaming_ok (renaming_for avoid0 s)
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

(* Definition make_serial
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
. *)

Definition make_serial0
    {Σ : StaticModel}
    (s : gmap variable (TermOver BuiltinOrVar))
    (avoid : gset variable)
    :
    list (variable*(TermOver BuiltinOrVar))%type
:=
    let r := renaming_for avoid s in
    let rinv := r_inverse r in
    (map_to_list (subp_compose s (rlift rinv)))
    ++
    (map_to_list (rlift r))
.

Definition make_serial
    {Σ : StaticModel}
    (s : gmap variable (TermOver BuiltinOrVar))
    :
    list (variable*(TermOver BuiltinOrVar))%type
:=
    make_serial0 s ∅
.


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
            unfold RestrictP in *.
            destruct (b !! i) eqn:Hbi.
            {
                simpl in *.
                rewrite option_guard_decide.
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

Ltac2 clear_decide () :=
    repeat (
        lazy_match! goal with
        | [h: (decide _ = _) |- _] => clear $h
        end
    )
.

Ltac2 cases () := repeat (ltac1:(case_match); clear_decide ()).

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
    unfold RestrictP in *.
    simpl in *.
    rewrite map_lookup_filter in H2.
    rewrite map_lookup_filter in H2.
    destruct (a !! i) eqn:Hai, (b !! i) eqn:Hbi.
    {
        simpl.
        simpl in *.
        simpl in H2.
        rewrite option_guard_decide in H2.
        rewrite option_guard_decide in H2.
        cases (); ltac1:(simplify_eq/=); try reflexivity.
        rewrite option_guard_decide.
        rewrite option_guard_decide.
        cases (); ltac1:(simplify_eq/=; try set_solver).
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
                unfold RestrictP in *.
                simpl in *.
                cases (); ltac1:(simplify_eq/=; try set_solver).
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
                    unfold RestrictP; simpl.
                    cases (); ltac1:(simplify_eq/=; try naive_solver).
                    rewrite option_guard_decide in H2.
                    rewrite option_guard_decide in H2.
                    cases (); ltac1:(simplify_eq/=; try naive_solver).
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
                unfold RestrictP. simpl.
                destruct (b !! i) eqn:Hbi; simpl; try reflexivity.
                rewrite option_guard_decide.
                rewrite map_lookup_filter.
                rewrite Hbi.
                simpl.
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
                rewrite map_lookup_filter.
                rewrite Hbi.
                reflexivity.
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
    (avoid0 : gset variable)
    :
    dom (renaming_for avoid0 a) = subp_dom a
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
    (avoid0 : gset variable)
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    subp_is_normal (rlift (renaming_for avoid0 m))
.
Proof.
    rewrite subp_is_normal_spec.
    intros k v Hkv HContra.
    subst v.
    unfold rlift in Hkv.
    rewrite lookup_fmap in Hkv.
    destruct (renaming_for avoid0 m !! k) eqn:Hrmk.
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


Lemma inverse_of_renaming_is_normal
    {Σ : StaticModel}
    (avoid0 : gset variable)
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    subp_is_normal (rlift (r_inverse (renaming_for avoid0 m)))
.
Proof.
    rewrite subp_is_normal_spec.
    intros k v Hkv HContra.
    subst v.
    unfold rlift in Hkv.
    rewrite lookup_fmap in Hkv.
    destruct (r_inverse (renaming_for avoid0 m) !! k) eqn:Hrmk.
    {
        simpl in Hkv.
        ltac1:(simplify_eq/=).
        unfold renaming_for in Hrmk.
        unfold r_inverse in Hrmk.
        ltac1:(rewrite - elem_of_list_to_map in Hrmk).
        {
            rewrite <- list_fmap_compose.
            unfold pair_swap.
            unfold compose.
            simpl.
            rewrite map_to_list_to_map.
            rewrite snd_zip.
            apply NoDup_fresh_var_seq.
            rewrite length_fresh_var_seq.
            ltac1:(lia).
            rewrite fst_zip.
            apply NoDup_elements.
            rewrite length_fresh_var_seq.
            ltac1:(lia).
        }
        rewrite elem_of_list_fmap in Hrmk.
        destruct Hrmk as [[y z][H1 H2]].
        unfold pair_swap in H1.
        simpl in H1.
        ltac1:(simplify_eq/=).
        rewrite map_to_list_to_map in H2.
        {
            apply elem_of_zip_l in H2 as H3.
            apply elem_of_zip_r in H2 as H4.
            clear H2.
            apply elem_of_fresh_var_seq in H4.
            ltac1:(set_solver).
        }
        {
            rewrite fst_zip.
            apply NoDup_elements.
            rewrite length_fresh_var_seq.
            ltac1:(lia).
        }
    }
    {
        inversion Hkv.
    }
Qed.

Lemma map_img_renaming_for_dom
    {Σ : StaticModel}
    (m : gmap variable (TermOver BuiltinOrVar))
    (avoid0 : gset variable)
    :
    map_img (renaming_for avoid0 m) ## dom m
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
    (avoid0 : gset variable)
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    map_img (renaming_for avoid0 m) ## subp_codom m
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

Lemma dom_rinverse
    {Σ : StaticModel}
    (r : gmap variable variable)
    :
    dom ((r_inverse r)) = map_img r
.
Proof.
    unfold subp_dom.
    (* unfold rlift. *)
    unfold r_inverse.
    unfold SubP in *.
    (* rewrite dom_fmap_L. *)
    rewrite dom_list_to_map_L.
    rewrite <- list_fmap_compose.
    unfold compose.
    simpl.
    rewrite map_img_alt_L.
    reflexivity.
Qed.


Lemma map_disjoint_compose_inverse
    {Σ : StaticModel}
    (avoid0 : gset variable)
    (m : gmap variable (TermOver BuiltinOrVar))
:
    subp_compose (rlift (renaming_for avoid0 m)) m
    ##ₘ rlift (r_inverse (renaming_for avoid0 m))
.
Proof.
    apply map_disjoint_spec.
    intros i x y Hx Hy.
    assert(Hdom := dom_subp_compose_subseteq (rlift (renaming_for avoid0 m)) m).
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
        rewrite elem_of_union in H2.
        apply not_or_and in H2.
        destruct H2 as [? H2].
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

Lemma subp_app_insert_2
    {Σ : StaticModel}
    (sub_mm : SubP)
    (x : variable)
    (v : TermOver BuiltinOrVar)
    (φ : TermOver BuiltinOrVar)
    :
    vars_of v ## subp_dom sub_mm ->
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
                    rewrite subp_app_almost_closed.
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

Definition make_parallel0
    {Σ : StaticModel}
    (init : gmap variable (TermOver BuiltinOrVar))
    (sub : list (variable*(TermOver BuiltinOrVar))%type)
    : (gmap variable (TermOver BuiltinOrVar))
:=
    foldr (fun a b => subp_compose ({[a.1 := a.2]}) b) init sub
.

Lemma subp_compose_empty_r
    {Σ : StaticModel}
    (a : gmap variable (TermOver BuiltinOrVar))
:
    subp_is_normal a ->
    subp_compose a ∅ = a
.
Proof.
    intros Hna.
    unfold subp_compose.
    rewrite fmap_empty.
    rewrite (right_id empty union).
    rewrite map_filter_id.
    {
        apply Hna.
    }
    {
        intros i x H1 H2.
        simpl in *.
        unfold subp_dom in H2.
        unfold SubP in *.
        rewrite dom_empty in H2.
        rewrite elem_of_empty in H2.
        exact H2.
    }
Qed.

Definition subs_is_normal
    {Σ : StaticModel}
    (a : list (variable*(TermOver BuiltinOrVar))%type)
    : Prop
:=
    Forall (fun x => t_over (bov_variable x.1) <> x.2) a
.

Lemma subp_compose_com
    {Σ : StaticModel}
    (a b : gmap variable (TermOver BuiltinOrVar))
:
    a ##ₘ b ->
    subp_codom b ## subp_dom a ->
    subp_codom a ## subp_dom b ->
    subp_is_normal a ->
    subp_is_normal b ->
    subp_compose a b = subp_compose b a
.
Proof.
    intros HH1 HH2 HH3 HH4 HH5.
    ltac1:(rewrite <- subp_union_is_compose__sometimes_1).
    {
        ltac1:(rewrite <- subp_union_is_compose__sometimes_1).
        {
            rewrite map_union_comm.
            {
                reflexivity.
            }
            {
                symmetry.
                assumption.
            }
        }
        {
            apply subp_compose_helper_1.
            assumption.
        }
        {
            assumption.
        }
        {
            assumption.
        }
    }
    {
        apply subp_compose_helper_1.
        unfold subp_dom.
        assumption.
    }
    {
        assumption.
    }
    {
        assumption.
    }
Qed.


Lemma subp_compose_empty_l
    {Σ : StaticModel}
    (a : gmap variable (TermOver BuiltinOrVar))
:
    subp_is_normal a ->
    subp_compose ∅ a = a
.
Proof.
    intros Hna.
    unfold subp_compose.
    rewrite map_filter_empty.
    rewrite (left_id empty union).
    ltac1:(rewrite subp_app_empty').
    rewrite map_fmap_id.
    apply Hna.
Qed.


Lemma subp_is_normal_normalize
    {Σ : StaticModel}
    a
    :
    subp_is_normal (subp_normalize a).
Proof.
    unfold subp_is_normal.
    unfold subp_normalize.
    rewrite map_filter_id.
    { reflexivity. }
    {
        intros i x Hx Hc.
        simpl in *.
        subst x.
        rewrite map_lookup_filter in Hx.
        rewrite bind_Some in Hx.
        destruct Hx as [y [H1y H2y]].
        rewrite option_guard_decide in H2y.
        cases (); ltac1:(simplify_eq/=).
    }
Qed.


Lemma make_parallel0_normal
    {Σ : StaticModel}
    init
    (sub : list (variable*(TermOver BuiltinOrVar))%type)
    :
    subp_is_normal init ->
    subp_is_normal (make_parallel0 init sub)
.
Proof.
    destruct sub; intros Hni.
    {
        simpl. exact Hni.
    }
    {
        simpl.
        unfold subp_compose.
        apply subp_is_normal_normalize.
    }
Qed.


(* Sadly, its precondition is too strong *)
Lemma make_parallel0_compose
    {Σ : StaticModel}
    (init : gmap variable (TermOver BuiltinOrVar))
    (sub : list (variable*(TermOver BuiltinOrVar))%type)
:
    subp_is_normal init ->
    subs_is_normal sub ->
    make_parallel0 init sub = subp_compose (make_parallel0 ∅ sub) init
.
Proof.
    intros Hni Hns.
    unfold make_parallel0 at 1.
    revert init Hni Hns.
    induction sub; intros init Hni Hns.
    {
        simpl.
        rewrite subp_compose_empty_l.
        { reflexivity. }
        { exact Hni. }
    }
    {
        simpl.
        assert (Hna : subp_is_normal {[a.1 := a.2]}).
        {
            unfold subs_is_normal in *.
            rewrite Forall_cons in Hns.
            destruct Hns as [Hna Hns].
            unfold subp_is_normal.
            unfold subp_normalize.
            rewrite map_filter_singleton.
            cases (); try reflexivity.
            simpl in n.
            apply dec_stable in n.
            destruct a as [a b].
            simpl in *.
            subst b.
            ltac1:(contradiction Hna).
            reflexivity.
        }
        rewrite IHsub.
        {
            unfold SubP in *.
            ltac1:(rewrite <- subp_compose_assoc).
            {
                reflexivity.
            }
            {
                apply make_parallel0_normal.
                unfold subp_is_normal.
                unfold subp_normalize.
                rewrite map_filter_empty.
                reflexivity.
            }
        }
        {
            exact Hni.
        }
        {
            unfold subs_is_normal in *.
            rewrite Forall_cons in Hns.
            destruct Hns as [? Hns].
            exact Hns.
        }
    }
Qed.

Definition make_parallel
    {Σ : StaticModel}
    (sub : list (variable*(TermOver BuiltinOrVar))%type)
    : (gmap variable (TermOver BuiltinOrVar))
:=
    make_parallel0 ∅ sub
.

Lemma make_parallel_normal
    {Σ : StaticModel}
    (sub : list (variable*(TermOver BuiltinOrVar))%type)
    :
    subp_is_normal (make_parallel sub)
.
Proof.
    apply make_parallel0_normal.
    unfold subp_is_normal.
    unfold subp_normalize.
    rewrite map_filter_empty.
    reflexivity.
Qed.

Lemma map_img_subp_compose
    {Σ : StaticModel}
    (a b : gmap variable (TermOver BuiltinOrVar))
:
    map_img (subp_compose a b) ⊆ @map_img _ _ _ _ (listset (TermOver BuiltinOrVar)) _ _ _  a ∪ (map_img (subp_app a <$> b))
.
Proof.
    unfold subp_compose.
    unfold subp_normalize.
    eapply transitivity.
    {
        apply map_img_filter_subseteq.
    }
    {
        eapply transitivity.
        {
            apply map_img_union_subseteq.
        }
        {
            apply union_mono.
            {
                apply map_img_filter_subseteq.
            }
            {
                apply reflexivity.
            }
        }
    }
Qed.

(* Lemma subp_codom_make_parallel0
    {Σ : StaticModel}
    init
    (s : list (variable*(TermOver BuiltinOrVar))%type)
:
    subp_codom (make_parallel0 init s) = subp_codom init ∪ union_list (vars_of <$> s.*2)
.
Proof.
    unfold make_parallel0.
    unfold subp_codom, SubP in *.
    revert init.
    induction s; intros init.
    {
        simpl.
        ltac1:(set_solver).
    }
    {
        simpl.
        Check map_img_subp_compose.
        Search map_img subp_compose.
        ltac1:(rewrite IHs).
    }
Qed.


Lemma subp_codom_make_parallel
    {Σ : StaticModel}
    (s : list (variable*(TermOver BuiltinOrVar))%type)
:
    subp_codom (make_parallel s) = union_list (vars_of <$> s.*2)
.
Proof.
    unfold make_parallel.
Qed. *)

Lemma make_parallel_app
    {Σ : StaticModel}
    (s1 s2 : list (variable*(TermOver BuiltinOrVar))%type)
    :
    subs_is_normal s1 ->
    make_parallel (s1 ++ s2) = subp_compose (make_parallel s1) (make_parallel s2)
.
Proof.
    intros HH1.
    unfold make_parallel at 1.
    unfold make_parallel0.
    rewrite foldr_app.
    ltac1:(fold (make_parallel0 ∅ s2)).
    ltac1:(fold (make_parallel s2)).
    ltac1:(fold (make_parallel0 (make_parallel s2) s1)).
    rewrite make_parallel0_compose.
    {
        fold (make_parallel s1).
        reflexivity.
    }
    {
        apply make_parallel_normal.
    }
    {
        exact HH1.
    }
Qed.

Lemma make_parallel_perm
    {Σ : StaticModel}
    (a b : list (variable*(TermOver BuiltinOrVar))%type)
    init
    :
    subs_is_normal a ->
    subs_is_normal b ->
    NoDup a.*1 ->
    NoDup b.*1 ->
    (list_to_set a.*1) ## ⋃ (vars_of <$> b.*2) ->
    (list_to_set b.*1) ## ⋃ (vars_of <$> a.*2) ->
    a ≡ₚ b ->
    make_parallel0 init a = make_parallel0 init b
.
Proof.
    intros Hna Hnb Hda Hdb Hab Hba Hp.
    revert init Hna Hnb Hda Hdb Hab Hba.
    induction Hp; intros init Hna Hnb Hda Hdb Hab Hba.
    {
        simpl. reflexivity.
    }
    {
        simpl.
        unfold subs_is_normal in *.
        rewrite Forall_cons in Hna.
        rewrite Forall_cons in Hnb.
        rewrite fmap_cons in Hab.
        rewrite fmap_cons in Hab.
        rewrite fmap_cons in Hab.
        rewrite union_list_cons in Hab.
        rewrite list_to_set_cons in Hab.
        rewrite fmap_cons in Hba.
        rewrite fmap_cons in Hba.
        rewrite fmap_cons in Hba.
        rewrite union_list_cons in Hba.
        rewrite list_to_set_cons in Hba.

        rewrite IHHp.
        { reflexivity. }
        {
            apply Hna.
        }
        {
            apply Hnb.
        }
        {
            rewrite fmap_cons in Hda.
            rewrite NoDup_cons in Hda.
            destruct Hda as [Hx Hl].
            exact Hl.
        }
        {
            rewrite fmap_cons in Hdb.
            rewrite NoDup_cons in Hdb.
            destruct Hdb as [Hx Hl'].
            exact Hl'.
        }
        {
            clear - Hab.
            ltac1:(set_solver).
        }
        {
            clear - Hba.
            ltac1:(set_solver).
        }
    }
    {
        simpl.
        unfold subs_is_normal in *.
        rewrite Forall_cons in Hna.
        rewrite Forall_cons in Hnb.
        destruct Hna as [H1 H2].
        destruct Hnb as [H3 H4].
        rewrite Forall_cons in H2.
        destruct H2 as [H7 H8].
        rewrite Forall_cons in H4.
        destruct H4 as [H9 H10].
        rewrite fmap_cons in Hda.
        rewrite fmap_cons in Hda.
        rewrite NoDup_cons in Hda.
        rewrite NoDup_cons in Hda.
        rewrite fmap_cons in Hdb.
        rewrite fmap_cons in Hdb.
        rewrite NoDup_cons in Hdb.
        rewrite NoDup_cons in Hdb.
        destruct Hda as [H11 [H12 H13]].
        destruct Hdb as [H14 [H15 H16]].
        rewrite elem_of_cons in H11.
        rewrite elem_of_cons in H14.
        apply not_or_and in H11.
        apply not_or_and in H14.
        destruct H11 as [H17 H18].
        destruct H14 as [H19 H20].
        rewrite fmap_cons in Hab.
        rewrite fmap_cons in Hab.
        rewrite fmap_cons in Hab.
        rewrite fmap_cons in Hab.
        rewrite fmap_cons in Hab.
        rewrite fmap_cons in Hab.
        rewrite union_list_cons in Hab.
        rewrite union_list_cons in Hab.
        rewrite list_to_set_cons in Hab.
        rewrite list_to_set_cons in Hab.
        rewrite fmap_cons in Hba.
        rewrite fmap_cons in Hba.
        rewrite fmap_cons in Hba.
        rewrite fmap_cons in Hba.
        rewrite fmap_cons in Hba.
        rewrite fmap_cons in Hba.
        rewrite union_list_cons in Hba.
        rewrite union_list_cons in Hba.
        rewrite list_to_set_cons in Hba.
        rewrite list_to_set_cons in Hba.

        rewrite <- subp_compose_assoc.
        {
            rewrite (subp_compose_com {[y.1 := y.2]} {[x.1 := x.2]}).
            {
                rewrite subp_compose_assoc.
                {
                    reflexivity.
                }
                {
                    rewrite subp_is_normal_spec.
                    intros k v H5 H6.
                    ltac1:(simplify_eq/=).
                    destruct (decide (k = y.1)).
                    {
                        subst.
                        rewrite lookup_singleton in H5.
                        ltac1:(simplify_eq/=).
                    }
                    {
                        rewrite lookup_singleton_ne in H5.
                        { inversion H5. }
                        { ltac1:(congruence). }
                    }
                }
            }
            {
                rewrite map_disjoint_spec.
                intros k v v' H5 H6.
                destruct x as [x1 x2], y as [y1 y2].
                simpl in *.
                destruct (decide(k = y1)), (decide(k = x1));
                    ltac1:(simplify_eq/=).
                {
                    rewrite lookup_singleton in H5.
                    rewrite lookup_singleton_ne in H6>[|ltac1:(congruence)].
                    ltac1:(simplify_eq/=).
                }
                {
                    rewrite lookup_singleton in H6.
                    rewrite lookup_singleton_ne in H5>[|ltac1:(congruence)].
                    ltac1:(simplify_eq/=).
                }
                {
                    rewrite lookup_singleton_ne in H5>[|ltac1:(congruence)].
                    rewrite lookup_singleton_ne in H6>[|ltac1:(congruence)].
                    ltac1:(simplify_eq/=).
                }
            }
            {
                unfold subp_dom, subp_codom, SubP in *.
                rewrite map_img_singleton.
                rewrite dom_singleton.
                rewrite elements_singleton.
                simpl.
                rewrite (right_id empty union).
                clear - Hab.
                ltac1:(set_solver).
            }
            {
                unfold subp_dom, subp_codom, SubP in *.
                rewrite map_img_singleton.
                rewrite dom_singleton.
                rewrite elements_singleton.
                simpl.
                rewrite (right_id empty union).
                clear - Hba.
                ltac1:(set_solver).
            }
            {
                rewrite subp_is_normal_spec.
                intros k v H1v H2v.
                subst v.
                destruct (decide (y.1 = k));
                    ltac1:(simplify_eq/=).
                {
                    rewrite lookup_singleton in H1v.
                    ltac1:(simplify_eq/=).
                }
                {
                    rewrite lookup_singleton_ne in H1v.
                    { ltac1:(simplify_eq/=). }
                    {
                        ltac1:(congruence).
                    }
                }
            }
            {
                rewrite subp_is_normal_spec.
                intros k v H1v H2v.
                subst v.
                destruct (decide (x.1 = k));
                    ltac1:(simplify_eq/=).
                {
                    rewrite lookup_singleton in H1v.
                    ltac1:(simplify_eq/=).
                }
                {
                    rewrite lookup_singleton_ne in H1v.
                    { ltac1:(simplify_eq/=). }
                    {
                        ltac1:(congruence).
                    }
                }
            }
        }
        {
            rewrite subp_is_normal_spec.
            intros k v H1v H2v.
            subst v.
            destruct (decide (x.1 = k));
                ltac1:(simplify_eq/=).
            {
                rewrite lookup_singleton in H1v.
                ltac1:(simplify_eq/=).
            }
            {
                rewrite lookup_singleton_ne in H1v.
                { ltac1:(simplify_eq/=). }
                {
                    ltac1:(congruence).
                }
            }
        }
    }
    {
        assert (subs_is_normal l').
        {
            unfold subs_is_normal.
            rewrite Hp2.
            exact Hnb.
        }
        rewrite IHHp1.
        {
            rewrite IHHp2.
            {
                reflexivity.
            }
            { assumption. }
            { assumption. }
            {
                rewrite Hp2.
                assumption.
            }
            {
                assumption.
            }
            {
                rewrite <- Hp1.
                exact Hab.
            }
            {
                rewrite <- Hp1.
                exact Hba.
            }
        }
        { assumption. }
        { assumption. }
        { assumption. }
        {
            rewrite <- Hp1.
            assumption.
        }
        {
            rewrite Hp2.
            assumption.
        }
        {
            rewrite Hp2.
            assumption.
        }
    }
Qed.

Lemma subp_codom_subp_compose
    {Σ : StaticModel}
    (a b : gmap variable (TermOver BuiltinOrVar))
    :
    dom a ## dom b ->
    dom a ## subp_codom b ->
    subp_is_normal a ->
    subp_is_normal b ->
    subp_codom a ∪ subp_codom b ⊆ subp_codom (subp_compose a b)
.
Proof.
    intros Hab H'bb Ha Hb.
    unfold subp_codom,subp_compose,SubP.
    rewrite elem_of_subseteq.
    intros x Hx.
    rewrite elem_of_union in Hx.
    rewrite elem_of_union_list in Hx.
    rewrite elem_of_union_list in Hx.
    rewrite elem_of_union_list.
    destruct Hx as [Hx|Hx].
    {
        destruct Hx as [X [H1X H2X]].
        exists X.
        split>[|assumption].
        rewrite elem_of_list_fmap in H1X.
        rewrite elem_of_list_fmap.
        destruct H1X as [y [H1y H2y]].
        exists y.
        split>[assumption|].
        rewrite elem_of_elements in H2y.
        rewrite elem_of_elements.
        unfold subp_normalize.
        subst.
        rewrite elem_of_map_img in H2y.
        destruct H2y as [i Hi].
        rewrite elem_of_map_img.
        exists i.
        rewrite map_lookup_filter.
        rewrite bind_Some.
        exists y.
        simpl.
        rewrite subp_is_normal_spec in Ha.
        rewrite subp_is_normal_spec in Hb.
        rewrite option_guard_decide.
        cases (); try ltac1:(naive_solver).
        split>[|reflexivity].
        rewrite lookup_union.
        rewrite map_lookup_filter.
        rewrite lookup_fmap.
        rewrite Hi.
        simpl.
        rewrite option_guard_decide.
        destruct (b !! i) eqn:Hbi;
            cases (); try reflexivity.
        {
            apply dec_stable in n0.
            unfold subp_dom in n0.
            apply elem_of_dom_2 in Hi.
            ltac1:(exfalso).
            clear - Hab n0 Hi.
            ltac1:(set_solver).
        }
        {
            apply dec_stable in n0.
            apply not_elem_of_dom in Hbi.
            ltac1:(contradiction Hbi).
        }
    }
    {
        destruct Hx as [X [H1X H2X]].
        exists X.
        split>[|assumption].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst.
        rewrite elem_of_list_fmap.
        exists y.
        split>[reflexivity|].
        rewrite elem_of_elements in H2y.
        rewrite elem_of_elements.
        rewrite elem_of_map_img in H2y.
        rewrite elem_of_map_img.
        destruct H2y as [i Hi].
        exists i.
        unfold subp_normalize.
        rewrite map_lookup_filter.
        rewrite bind_Some.
        exists y.
        rewrite option_guard_decide.
        simpl.
        rewrite subp_is_normal_spec in Hb.
        cases (); try ltac1:(naive_solver).
        split>[|reflexivity].
        rewrite lookup_union.
        rewrite lookup_fmap.
        rewrite map_lookup_filter.
        rewrite Hi.
        simpl.
        destruct (a !! i) eqn:Hai;
            cases ();
            try ltac1:(simplify_eq/=).
        {
            ltac1:(exfalso).
            apply elem_of_dom_2 in Hi.
            apply elem_of_dom_2 in Hai.
            clear - Hi Hai Hab.
            ltac1:(set_solver).
        }
        {
            rewrite (left_id None union).
            apply f_equal.
            rewrite subp_app_almost_closed.
            { reflexivity. }
            {
                apply elem_of_dom_2 in Hi as Hdb.
                
                assert (Htmp: vars_of y ⊆ subp_codom b).
                {
                    unfold subp_codom.
                    rewrite elem_of_subseteq.
                    intros x0 Hx0.
                    rewrite elem_of_union_list.
                    exists (vars_of y).
                    split>[|exact Hx0].
                    rewrite elem_of_list_fmap.
                    exists y.
                    split>[reflexivity|].
                    rewrite elem_of_elements.
                    unfold SubP in *.
                    rewrite elem_of_map_img.
                    exists i.
                    exact Hi.
                }
                unfold subp_dom, SubP.
                clear - Htmp H'bb Hdb.
                ltac1:(set_solver).
            }

        }
    }
Qed.

Lemma vars_of_subp_app
    {Σ : StaticModel}
    (a : gmap variable (TermOver BuiltinOrVar))
    (q : TermOver BuiltinOrVar)
    :
    vars_of (subp_app a q) ⊆ subp_codom a ∪ vars_of q
.
Proof.
    revert a.
    induction q; intros aa.
    {
        simpl.
        destruct a; simpl.
        {
            ltac1:(set_solver).
        }
        {
            cases ().
            {
                apply union_subseteq_l'.
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
                exact H.
            }
            {
                ltac1:(set_solver).
            }
        }
    }
    {
        simpl.
        rewrite vars_of_t_term.
        rewrite vars_of_t_term.
        rewrite elem_of_subseteq.
        intros x Hx.
        rewrite Forall_forall in H.
        rewrite elem_of_union_list in Hx.
        destruct Hx as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst.
        rewrite elem_of_list_fmap in H2y.
        destruct H2y as [z [H1z H2z]].
        subst.
        specialize (H _ H2z aa).
        eapply elem_of_weaken in H2X>[|apply H].
        rewrite elem_of_union in H2X.
        rewrite elem_of_union.
        destruct H2X as [H2X|H2X].
        {
            left.
            exact H2X.
        }
        {
            right.
            rewrite elem_of_union_list.
            exists (vars_of z).
            split>[|exact H2X].
            rewrite elem_of_list_fmap.
            exists z.
            split>[reflexivity|].
            exact H2z.
        }
    }
Qed.

Lemma subp_codom_subp_compose_2
    {Σ : StaticModel}
    (a b : gmap variable (TermOver BuiltinOrVar))
    :
    subp_codom (subp_compose a b) ⊆ subp_codom a ∪ subp_codom b
.
Proof.
    unfold subp_codom,subp_compose,SubP.
    rewrite elem_of_subseteq.
    intros x Hx.
    rewrite elem_of_union_list in Hx.
    rewrite elem_of_union.
    destruct Hx as [X [H1X H2X]].
    rewrite elem_of_list_fmap in H1X.
    destruct H1X as [y [H1y H2y]].
    subst X.
    rewrite elem_of_elements in H2y.
    rewrite elem_of_map_img in H2y.
    destruct H2y as [i Hi].
    unfold subp_normalize in Hi.
    rewrite map_lookup_filter in Hi.
    rewrite bind_Some in Hi.
    destruct Hi as [p Hp].
    destruct Hp as [H1p H2p].
    rewrite option_guard_decide in H2p.
    cases (); ltac1:(simplify_eq/=).
    rewrite lookup_union in H1p.
    rewrite union_Some in H1p.
    destruct H1p as [H1p|H1p].
    {
        rewrite map_lookup_filter in H1p.
        rewrite bind_Some in H1p.
        destruct H1p as [q [H1q H2q]].
        simpl in *.
        rewrite option_guard_decide in H2q.
        cases (); ltac1:(simplify_eq/=).
        
        left.
        rewrite elem_of_union_list.
        exists (vars_of y).
        split>[|assumption].
        rewrite elem_of_list_fmap.
        exists (y).
        split>[reflexivity|].
        rewrite elem_of_elements.
        rewrite elem_of_map_img.
        exists i.
        exact H1q.
    }
    {
        rewrite map_lookup_filter in H1p.
        rewrite bind_None in H1p.
        destruct H1p as [[H1p |H1p] H2p].
        {
            rewrite lookup_fmap in H2p.
            rewrite fmap_Some in H2p.
            destruct H2p as [q [H1q H2q]].
            subst.
            eapply elem_of_weaken in H2X>[|apply vars_of_subp_app].
            rewrite elem_of_union in H2X.
            destruct H2X as [H2X|H2X].
            {
                left.
                unfold subp_codom in H2X.
                exact H2X.
            }
            {
                right.
                rewrite elem_of_union_list.
                exists (vars_of q).
                split>[|exact H2X].
                rewrite elem_of_list_fmap.
                exists q.
                split>[reflexivity|].
                rewrite elem_of_elements.
                rewrite elem_of_map_img.
                exists i.
                exact H1q.
            }
        }
        {
            rewrite lookup_fmap in H2p.
            rewrite fmap_Some in H2p.
            destruct H2p as [q [H1q H2q]].
            subst.
            destruct H1p as [y [H1y H2y]].
            rewrite option_guard_decide in H2y.
            cases (); ltac1:(simplify_eq/=).
            apply dec_stable in n0.
            eapply elem_of_weaken in H2X>[|apply vars_of_subp_app].
            rewrite elem_of_union in H2X.
            destruct H2X as [H|H].
            {
                left.
                exact H.
            }
            {
                right.
                rewrite elem_of_union_list.
                exists (vars_of q).
                split>[|exact H].
                rewrite elem_of_list_fmap.
                exists q.
                split>[reflexivity|].
                rewrite elem_of_elements.
                rewrite elem_of_map_img.
                exists i.
                exact H1q.
            }
        }
    }
Qed.
(* 
Lemma subp_codom_insert_notin {Σ : StaticModel} i x m:
    i ∉ dom m ->
    x ∉ @map_img _ _ _ _ (listset _) _ _ _ m ->
    subp_codom (<[i:=x]> m) = vars_of x ∪ subp_codom m
.
Proof.
    intros Him Hxim.
    unfold subp_codom, SubP.
    rewrite map_img_insert.
    rewrite delete_notin.
    {
        rewrite elements_union_singleton.
        {
            rewrite fmap_cons.
            rewrite union_list_cons.
            reflexivity.
        }
        {
            exact Hxim.
        }
    }
    {
        apply not_elem_of_dom_1.
        exact Him.
    }
Qed. *)


Lemma subp_codom_insert {Σ : StaticModel} i x m:
    i ∉ dom m ->
    (* x ∉ @map_img _ _ _ _ (listset _) _ _ _ m -> *)
    subp_codom (<[i:=x]> m) = vars_of x ∪ subp_codom m
.
Proof.
    intros Him.
    unfold subp_codom, SubP.
    rewrite map_img_insert.
    rewrite delete_notin.
    {
        unfold SubP in *.
        destruct (decide (x ∈ (@map_img _ _ _ _ (listset _) _ _ _ m))).
        {
            assert(H1: {[x]} ∪ map_img m ≡ (@map_img _ _ _ _ (listset _) _ _ _ m)) by ltac1:(set_solver).
            (* rewrite H1. *)
            assert (H2: elements (@map_img _ _ _ _ (listset _) _ _ _ m) ≡ₚ elements ({[x]} ∪ (@map_img _ _ _ _ (listset _) _ _ _ m))).
            {
                rewrite H1.
                reflexivity.
            }
            assert (H3: 
                (fmap (@vars_of (TermOver BuiltinOrVar) variable _ _ _) (elements (@map_img _ _ _ _ (listset _) _ _ _ m)))
                 ≡ₚ
                 (fmap (@vars_of (TermOver BuiltinOrVar) variable _ _ _) (elements ({[x]} ∪ (@map_img _ _ _ _ (listset _) _ _ _ m))))).
            {
                rewrite H2 at 1.
                reflexivity.
            }
            assert (H4: vars_of x ⊆ ⋃ ((fmap (@vars_of (TermOver BuiltinOrVar) variable _ _ _) (elements ({[x]} ∪ (@map_img _ _ _ _ (listset _) _ _ _ m)))))).
            {
                rewrite elem_of_subseteq.
                intros x0 Hx0.
                rewrite elem_of_union_list.
                exists (vars_of x).
                split>[|assumption].
                rewrite elem_of_list_fmap.
                exists x.
                split>[reflexivity|].
                rewrite elem_of_elements.
                ltac1:(set_solver).
            }

            (* apply (antisymmetry subseteq). *)
            (* ltac1:(set_solver). *)
            rewrite <- H3 at 1.
            apply set_eq.
            intros x0.
            split.
            {
                ltac1:(set_solver).
            }
            {
                intros HH.
                rewrite elem_of_union in HH.
                destruct HH as [HH|HH].
                {
                    eapply elem_of_weaken.
                    apply HH.
                    rewrite H3.
                    apply H4.
                }
                {
                    exact HH.
                }
            }
            
        }
        {
            rewrite elements_union_singleton.
            {
                rewrite fmap_cons.
                rewrite union_list_cons.
                reflexivity.
            }
            {
                assumption.
            }

        }
    }
    {
        apply not_elem_of_dom_1.
        exact Him.
    }
Qed.



Lemma make_parallel_correct
    {Σ : StaticModel}
    (sub : SubS)
    (φ : TermOver BuiltinOrVar)
    :
    subp_app (make_parallel sub) φ = subs_app (reverse sub) φ
.
Proof.
    revert φ.
    induction sub; intros φ; simpl.
    {
        ltac1:(rewrite subp_app_empty).
        reflexivity.
    }
    {
        unfold SubP in *.
        destruct a; simpl in *.
        unfold SubP in *.
        rewrite subp_compose_correct.
        unfold compose.
        ltac1:(rewrite subp_app_insert_2).
        {
            unfold subp_dom, SubP in *.
            rewrite dom_empty.
            ltac1:(set_solver).
        }
        ltac1:(rewrite subp_app_empty').
        simpl.
        rewrite IHsub.
        {
            rewrite reverse_cons.
            rewrite subs_app_app.
            simpl.
            reflexivity.
        }
    }
Qed.

Lemma helper_lemma' {Σ : StaticModel}:
  forall x m t, t_over (bov_variable x) = subp_app m t ->
  exists y, t = t_over (bov_variable y) /\ (m !! y = Some (t_over (bov_variable x)) \/ y = x)
.
Proof.
    intros x' m' t' HH.
    destruct t'; simpl in HH.
    {
        destruct a; simpl in HH.
        {
            ltac1:(simplify_eq/=).
        }
        {
            cases (); ltac1:(simplify_eq/=).
            {
                exists x.
                split>[reflexivity|].
                left.
                assumption.
            }
            {
                exists x.
                split>[reflexivity|].
                right.
                reflexivity.
            }
        }
    }
    {
        ltac1:(simplify_eq/=).
    }
Qed.


Lemma make_parallel0_map_to_list
    {Σ : StaticModel}
    (init s : gmap variable (TermOver BuiltinOrVar))
    :
    subp_is_normal s ->
    subp_is_normal init ->
    (subp_dom s) ## subp_codom init ->
    (subp_dom s) ## subp_dom init ->
    (subp_codom s) ## subp_dom init ->
    (subp_codom s) ## subp_dom s ->
    make_parallel0 init (map_to_list s) = subp_compose init s
.
Proof.
    revert init.
    ltac1:(induction s using map_ind); intros init Hsnorm Hinit Hinit2 Hinit3 Hinit4 Hinit5.
    {
        unfold make_parallel.
        unfold SubP in *.
        unfold make_parallel0.
        rewrite map_to_list_empty.
        simpl.
        rewrite subp_compose_empty_r.
        { reflexivity. }
        { exact Hinit. }
    }
    {
        (* Check subp_codom_insert_notin. *)
        (* Search subp_codom insert. *)
        unfold make_parallel.
        rewrite make_parallel_perm with (b := (i,x)::map_to_list m).
        {
            simpl.
            rewrite IHs.
            {
                unfold subp_compose at 1 3.
                (* rewrite fmap_insert. *)
                rewrite <- insert_empty.
                unfold SubP in *.
                ltac1:(rewrite subp_app_insert0).
                {
                    unfold subp_dom.
                    unfold SubP in *.
                    rewrite dom_empty.
                    ltac1:(set_solver).
                }
                {
                    ltac1:(rewrite subp_app_empty').
                    unfold compose.
                    rewrite insert_empty.
                    rewrite map_filter_singleton.
                    simpl.
                    unfold subp_dom, SubP in *.
                    cases ().
                    {
                        rewrite fmap_insert.
                        unfold subp_normalize.
                        rewrite map_filter_union.
                        {
                            rewrite map_filter_singleton.
                            simpl.
                            rewrite map_filter_union.
                            {
                                rewrite map_filter_insert.
                                simpl.
                                cases ().
                                {
                                    rewrite subp_app_almost_closed.
                                    {
                                        (* clear. *)
                                        rewrite dom_insert_L.
                                        rewrite map_filter_fmap.
                                        simpl.
                                        (* About map_filter_id. *)
                                        rewrite (map_filter_id _ init).
                                        {
                                            apply subp_normalize_normal in Hinit as Hinit'.
                                            unfold subp_normalize in Hinit'.
                                            ltac1:(rewrite Hinit').
                                            clear Hinit'.
                                            rewrite insert_union_singleton_l.
                                            rewrite map_union_assoc.
                                            rewrite (map_union_comm init).
                                            {
                                                rewrite <- map_union_assoc.
                                                f_equal.
                                                unfold subp_is_normal in Hinit.
                                                rewrite <- Hinit at 2.
                                                unfold subp_normalize.
                                                rewrite <- map_filter_union.
                                                {
                                                    ltac1:(replace (init) with ((filter (λ kv : variable * TermOver BuiltinOrVar, kv.1 ∉ subp_dom m) init)) at 2).
                                                    {
                                                        ltac1:(
                                                            replace
                                                                ((λ x0 : TermOver BuiltinOrVar, TermOverBoV_subst x0 i x) <$>
                                                                    filter (λ '(i0, x0), t_over (bov_variable i0) ≠ TermOverBoV_subst x0 i x)
                                                                (subp_compose init m))
                                                            with (
                                                                filter (fun a => t_over (bov_variable a.1) <> a.2)
                                                                    ((fun a => TermOverBoV_subst a i x) <$> (subp_compose init m))
                                                            )
                                                        ).
                                                        {
                                                            unfold SubP in *.
                                                            ltac1:(apply map_filter_strong_ext).
                                                            {
                                                                intros j y.
                                                                simpl.
                                                                split.
                                                                {
                                                                    intros [HH1 HH2].
                                                                    split>[assumption|].
                                                                    rewrite lookup_fmap in HH2.
                                                                    rewrite fmap_Some in HH2.
                                                                    destruct HH2 as [z [H1z H2z]].
                                                                    subst y.
                                                                    (* rewrite lookup_union. *)
                                                                    
                                                                    (* rewrite subst_notin2. *)
                                                                    {
                                                                        apply elem_of_dom_2 in H1z as H1z''.
                                                                        unfold subp_compose in H1z.
                                                                        unfold subp_normalize in H1z.
                                                                        rewrite map_lookup_filter in H1z.
                                                                        rewrite bind_Some in H1z.
                                                                        destruct H1z as [z' [H1z' H2z']].
                                                                        rewrite option_guard_decide in H2z'.
                                                                        cases (); ltac1:(simplify_eq/=).


                                                                        (* rewrite lookup_union. *)
                                                                        rewrite subst_notin2.
                                                                        {
                                                                            
                                                                            ltac1:(apply H1z').
                                                                        }
                                                                        {
                                                                            assert (Hinit4' := Hinit4).
                                                                            ltac1:(rewrite subp_codom_insert in Hinit4).
                                                                            {
                                                                                unfold SubP in *.
                                                                                apply not_elem_of_dom_2.
                                                                                exact H.
                                                                            }
                                                                            {
                                                                                intros HContra.
                                                                                ltac1:(rewrite subp_codom_insert in Hinit5).
                                                                                {
                                                                                    unfold SubP in *.
                                                                                    apply not_elem_of_dom_2.
                                                                                    exact H.
                                                                                }
                                                                                {
                                                                                    assert(HC: i ∈ subp_codom (subp_compose init m)).
                                                                                    {
                                                                                        unfold subp_codom,subp_compose,SubP.
                                                                                        rewrite elem_of_union_list.
                                                                                        exists (vars_of z).
                                                                                        split>[|assumption].
                                                                                        rewrite elem_of_list_fmap.
                                                                                        exists z.
                                                                                        split>[reflexivity|].
                                                                                        rewrite elem_of_elements.
                                                                                        rewrite elem_of_map_img.
                                                                                        exists j.
                                                                                        unfold subp_normalize.
                                                                                        rewrite map_lookup_filter.
                                                                                        rewrite H1z'.
                                                                                        simpl.
                                                                                        rewrite option_guard_decide.
                                                                                        cases (); try reflexivity.
                                                                                        ltac1:(simplify_eq/=).
                                                                                    }
                                                                                    (*  *)
                                                                                    assert (Htmp := subp_codom_subp_compose_2 init m).
                                                                                    eapply elem_of_weaken in Htmp>[|apply HC].
                                                                                    rewrite elem_of_union in Htmp.
                                                                                    destruct Htmp as [Htmp|Htmp].
                                                                                    {
                                                                                        rewrite dom_insert in Hinit2.
                                                                                        rewrite dom_insert in Hinit3.
                                                                                        ltac1:(set_solver).
                                                                                    }
                                                                                    {
                                                                                        rewrite dom_insert in Hinit5.
                                                                                        clear - Htmp Hinit5.
                                                                                        ltac1:(set_solver).
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                                {
                                                                    intros [HH1 HH2].
                                                                    split>[assumption|].
                                                                    rewrite lookup_union in HH2.
                                                                    rewrite map_lookup_filter in HH2.
                                                                    rewrite lookup_fmap.
                                                                    rewrite union_Some in HH2.
                                                                    destruct HH2 as [HH2|HH2].
                                                                    {
                                                                        rewrite bind_Some in HH2.
                                                                        destruct HH2 as [q [H1q H2q]].
                                                                        rewrite option_guard_decide in H2q.
                                                                        cases (); ltac1:(simplify_eq/=).
                                                                        rewrite fmap_Some.
                                                                        exists y.
                                                                        split.
                                                                        {
                                                                            unfold subp_compose.
                                                                            unfold subp_normalize.
                                                                            rewrite map_lookup_filter.
                                                                            rewrite bind_Some.
                                                                            exists y.
                                                                            rewrite option_guard_decide.
                                                                            simpl.
                                                                            split.
                                                                            {
                                                                                rewrite lookup_union.
                                                                                rewrite map_lookup_filter.
                                                                                rewrite union_Some.
                                                                                left.
                                                                                rewrite bind_Some.
                                                                                exists y.
                                                                                split>[exact H1q|].
                                                                                rewrite option_guard_decide.
                                                                                simpl.
                                                                                cases (); try reflexivity.
                                                                                ltac1:(contradiction).
                                                                            }
                                                                            { 
                                                                                cases (); try ltac1:(congruence).
                                                                                ltac1:(contradiction).
                                                                            }
                                                                        }
                                                                        {
                                                                            rewrite subst_notin2.
                                                                            { reflexivity. }
                                                                            {
                                                                                assert (Hinit4' := Hinit4).
                                                                                ltac1:(rewrite subp_codom_insert in Hinit4).
                                                                                {
                                                                                    unfold SubP in *.
                                                                                    apply not_elem_of_dom_2.
                                                                                    exact H.
                                                                                }
                                                                                {
                                                                                    intros HContra.
                                                                                    ltac1:(rewrite subp_codom_insert in Hinit5).
                                                                                    {
                                                                                        unfold SubP in *.
                                                                                        apply not_elem_of_dom_2.
                                                                                        exact H.
                                                                                    }
                                                                                    {
                                                                                        assert(HC: i ∈ subp_codom (init)).
                                                                                        {
                                                                                            unfold subp_codom,SubP.
                                                                                            rewrite elem_of_union_list.
                                                                                            exists (vars_of y).
                                                                                            split>[|assumption].
                                                                                            rewrite elem_of_list_fmap.
                                                                                            exists y.
                                                                                            split>[reflexivity|].
                                                                                            rewrite elem_of_elements.
                                                                                            rewrite elem_of_map_img.
                                                                                            exists j.
                                                                                            exact H1q.
                                                                                        }
                                                                                        rewrite dom_insert in Hinit2.
                                                                                        clear - Hinit2 HC.
                                                                                        ltac1:(set_solver).
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                    {
                                                                        destruct HH2 as [HH2 HH3].
                                                                        rewrite lookup_fmap in HH3.
                                                                        rewrite bind_None in HH2.
                                                                        rewrite fmap_Some in HH3.
                                                                        destruct HH3 as [x0 [H1x0 H2x0]].
                                                                        ltac1:(simplify_eq/=).
                                                                        destruct HH2 as [HH2|HH2].
                                                                        {
                                                                            rewrite fmap_Some.
                                                                            exists (subp_app init x0).
                                                                            split.
                                                                            {
                                                                                unfold subp_compose.
                                                                                unfold subp_normalize.
                                                                                rewrite map_lookup_filter.
                                                                                rewrite lookup_union.
                                                                                rewrite lookup_fmap.
                                                                                rewrite H1x0.
                                                                                rewrite map_lookup_filter.
                                                                                ltac1:(rewrite HH2).
                                                                                simpl.
                                                                                rewrite option_guard_decide.
                                                                                cases (); try reflexivity.
                                                                                ltac1:(contradiction).
                                                                            }
                                                                            {
                                                                                rewrite subst_notin2.
                                                                                { reflexivity. }
                                                                                {
                                                                                    intros HContra.
                                                                                    assert (Ht1 := vars_of_subp_app init x0).
                                                                                    rewrite dom_insert in Hinit2.
                                                                                    rewrite dom_insert in Hinit3.
                                                                                    assert (Hix0: i ∈ vars_of x0).
                                                                                    {
                                                                                        ltac1:(set_solver).
                                                                                    }
                                                                                    assert (i ∈ subp_codom m).
                                                                                    {
                                                                                        unfold subp_codom.
                                                                                        rewrite elem_of_union_list.
                                                                                        exists (vars_of x0).
                                                                                        rewrite elem_of_list_fmap.
                                                                                        split>[|assumption].
                                                                                        exists x0.
                                                                                        split>[reflexivity|].
                                                                                        rewrite elem_of_elements.
                                                                                        ltac1:(rewrite elem_of_map_img).
                                                                                        exists j.
                                                                                        exact H1x0.
                                                                                    }
                                                                                    rewrite dom_insert in Hinit5.
                                                                                    assert (Hii: i ∉ dom init).
                                                                                    {
                                                                                        ltac1:(set_solver).
                                                                                    }
                                                                                    apply not_elem_of_dom_1 in Hii.
                                                                                    assert (i ∉ dom m).
                                                                                    (* destruct (decide (subp_app init )) *)
                                                                                    {
                                                                                        intros HContra'.
                                                                                        apply n. clear n.
                                                                                        (* Search (dom (subp_compose _ _)). *)
                                                                                        unfold subp_compose.
                                                                                        rewrite elem_of_dom.
                                                                                        ltac1:(rewrite elem_of_dom in HContra').
                                                                                        destruct HContra' as [u Hu].
                                                                                        unfold subp_normalize.
                                                                                        exists (subp_app init u).
                                                                                        rewrite map_lookup_filter.
                                                                                        rewrite lookup_union.
                                                                                        rewrite map_lookup_filter.
                                                                                        rewrite Hii.
                                                                                        simpl.
                                                                                        rewrite (left_id None union).
                                                                                        rewrite lookup_fmap.
                                                                                        rewrite Hu.
                                                                                        simpl.
                                                                                        rewrite option_guard_decide.
                                                                                        cases (); try reflexivity.
                                                                                        apply dec_stable in n.
                                                                                        rewrite subp_is_normal_spec in Hsnorm.
                                                                                        ltac1:(exfalso).
                                                                                        (* clear - Hsnorm Hu n. *)
                                                                                        apply helper_lemma' in n.
                                                                                        destruct n as [y [H1y H2y]].
                                                                                        subst u.
                                                                                        destruct H2y as [H2y|H2y].
                                                                                        {
                                                                                            ltac1:(simplify_eq/=).
                                                                                        }
                                                                                        {
                                                                                            subst y.
                                                                                            ltac1:(simplify_eq/=).
                                                                                        }
                                                                                    }
                                                                                    ltac1:(rewrite subp_codom_insert in Hinit4).
                                                                                    {
                                                                                        assumption.
                                                                                    }
                                                                                    ltac1:(rewrite subp_codom_insert in Hinit5).
                                                                                    {
                                                                                        assumption.
                                                                                    }
                                                                                    clear - Hinit5 H0.
                                                                                    ltac1:(set_solver).
                                                                                }
                                                                            }
                                                                        }
                                                                        {
                                                                            destruct HH2 as [x1 [H1x2 H2x1]].
                                                                            rewrite option_guard_decide in H2x1.
                                                                            cases (); ltac1:(simplify_eq/=).
                                                                            clear n2.
                                                                            ltac1:(exfalso).
                                                                            apply elem_of_dom_2 in H1x2.
                                                                            apply elem_of_dom_2 in H1x0.
                                                                            clear - H1x2 H1x0 Hinit3.
                                                                            rewrite dom_insert in Hinit3.
                                                                            ltac1:(set_solver).
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                        {
                                                            rewrite map_filter_fmap.
                                                            simpl.
                                                            reflexivity.
                                                        }
                                                    }
                                                    {
                                                        rewrite map_filter_id.
                                                        { reflexivity. }
                                                        {

                                                            intros j y Hy Hy'.
                                                            simpl in *.
                                                            unfold subp_dom in Hy'.
                                                            apply elem_of_dom_2 in Hy.
                                                            rewrite dom_insert in Hinit3.
                                                            clear - Hinit3 Hy Hy'.
                                                            ltac1:(set_solver).
                                                        }
                                                    }
                                                }
                                                {
                                                    apply map_disjoint_spec.
                                                    intros j y1 y2 Hy1 Hy2.
                                                    rewrite lookup_fmap in Hy2.
                                                    rewrite fmap_Some in Hy2.
                                                    destruct Hy2 as [z [H1z H2z]].
                                                    subst y2.
                                                    apply elem_of_dom_2 in Hy1.
                                                    apply elem_of_dom_2 in H1z.
                                                    clear - Hy1 H1z Hinit3.
                                                    rewrite dom_insert in Hinit3.
                                                    ltac1:(set_solver).
                                                }
                                                
                                            }
                                            {
                                                apply map_disjoint_spec.
                                                intros j y1 y2 Hy1 Hy2.
                                                destruct (decide (j = i)).
                                                {
                                                    subst.
                                                    rewrite lookup_singleton in Hy2.
                                                    ltac1:(simplify_eq/=).
                                                    apply elem_of_dom_2 in Hy1.
                                                    rewrite dom_insert in Hinit3.
                                                    clear - Hinit3 Hy1.
                                                    ltac1:(set_solver).
                                                }
                                                {
                                                    rewrite lookup_singleton_ne in Hy2.
                                                    { ltac1:(simplify_eq/=). }
                                                    {
                                                        ltac1:(congruence).
                                                    }
                                                }
                                            }
                                        }
                                        {
                                            intros j y Hy Hy'.
                                            simpl in *.
                                            apply elem_of_dom_2 in Hy.
                                            rewrite dom_insert in Hinit3.
                                            clear - Hy Hy' Hinit3.
                                            ltac1:(set_solver).
                                        }
                                    }
                                    {
                                        unfold subp_dom,SubP.
                                        ltac1:(rewrite subp_codom_insert in Hinit4).
                                        {
                                            unfold SubP in *.
                                            apply not_elem_of_dom_2.
                                            exact H.
                                        }
                                        clear - Hinit4.
                                        ltac1:(set_solver).
                                    }
                                }
                                {
                                    apply dec_stable in n1.
                                    apply helper_lemma' in n1.
                                    destruct n1 as [y [H1y H2y]].
                                    subst x.
                                    destruct H2y as [H2y|H2y].
                                    {
                                        rewrite dom_insert in Hinit2.
                                        assert (Hii: i ∈  subp_codom init).
                                        {
                                            unfold subp_codom,SubP.
                                            rewrite elem_of_union_list.
                                            exists (vars_of (t_over (bov_variable i))).
                                            unfold vars_of; simpl.
                                            unfold vars_of; simpl.
                                            split>[|clear; ltac1:(set_solver)].
                                            rewrite elem_of_list_fmap.
                                            exists (t_over (bov_variable i)).
                                            split>[reflexivity|].
                                            rewrite elem_of_elements.
                                            rewrite elem_of_map_img.
                                            exists y.
                                            exact H2y.
                                        }
                                        ltac1:(exfalso).
                                        clear - Hii Hinit2.
                                        ltac1:(set_solver).
                                    }
                                    {
                                        subst.
                                        ltac1:(contradiction n0).
                                        reflexivity.
                                    }
                                }
                                {
                                    apply dec_stable in n0.
                                    subst x.
                                    rewrite dom_insert in Hinit2.
                                    rewrite dom_insert in Hinit3.
                                    ltac1:(rewrite subp_codom_insert in Hinit5).
                                    {
                                        unfold SubP.
                                        apply not_elem_of_dom_2.
                                        exact H.
                                    }
                                    ltac1:(rewrite subp_codom_insert in Hinit4).
                                    {
                                        unfold SubP.
                                        apply not_elem_of_dom_2.
                                        exact H.
                                    }
                                    unfold vars_of in Hinit4; simpl in Hinit4.
                                    unfold vars_of in Hinit4; simpl in Hinit4.
                                    unfold vars_of in Hinit5; simpl in Hinit5.
                                    unfold vars_of in Hinit5; simpl in Hinit5.
                                    rewrite dom_insert in Hinit5.
                                    clear - Hinit5.
                                    ltac1:(set_solver).
                                }
                                {
                                    apply dec_stable in n0.
                                    apply dec_stable in n1.
                                    subst x.
                                    apply helper_lemma' in n1.
                                    destruct n1 as [y [H1y H2y]].
                                    destruct H2y as [H2y|H2y].
                                    {
                                        inversion H1y; subst; clear H1y.
                                        rewrite dom_insert in Hinit2.
                                        rewrite dom_insert in Hinit3.
                                        rewrite dom_insert in Hinit5.
                                        ltac1:(rewrite subp_codom_insert in Hinit4).
                                        {
                                            unfold SubP.
                                            apply not_elem_of_dom_2.
                                            exact H.
                                        }
                                        ltac1:(rewrite subp_codom_insert in Hinit5).
                                        {
                                            unfold SubP.
                                            apply not_elem_of_dom_2.
                                            exact H.
                                        }
                                        unfold vars_of in Hinit5; simpl in Hinit5.
                                        unfold vars_of in Hinit5; simpl in Hinit5.
                                        ltac1:(exfalso).
                                        clear - Hinit5.
                                        ltac1:(set_solver).
                                    }
                                    {
                                        rewrite dom_insert in Hinit2.
                                        rewrite dom_insert in Hinit3.
                                        rewrite dom_insert in Hinit5.
                                        ltac1:(rewrite subp_codom_insert in Hinit4).
                                        {
                                            unfold SubP.
                                            apply not_elem_of_dom_2.
                                            exact H.
                                        }
                                        ltac1:(rewrite subp_codom_insert in Hinit5).
                                        {
                                            unfold SubP.
                                            apply not_elem_of_dom_2.
                                            exact H.
                                        }
                                        unfold vars_of in Hinit5; simpl in Hinit5.
                                        unfold vars_of in Hinit5; simpl in Hinit5.
                                        clear - Hinit5.
                                        ltac1:(set_solver).
                                    }
                                }
                            }
                            {
                                apply map_disjoint_spec.
                                intros i0 x0 y0 Hx0 Hy0.
                                destruct (decide (i0 = i)).
                                {
                                    subst.
                                    ltac1:(rewrite subp_codom_insert in Hinit5).
                                    {
                                        unfold SubP.
                                        apply not_elem_of_dom_2.
                                        exact H.
                                    }
                                    rewrite dom_insert in Hinit5.
                                    ltac1:(rewrite subp_codom_insert in Hinit4).
                                    {
                                        unfold SubP.
                                        apply not_elem_of_dom_2.
                                        exact H.
                                    }
                                    rewrite dom_insert in Hinit3.
                                    rewrite dom_insert in Hinit2.
                                    rewrite map_lookup_filter in Hx0.
                                    rewrite bind_Some in Hx0.
                                    destruct Hx0 as [x1 [H1x2 H2x1]].
                                    apply elem_of_dom_2 in H1x2.
                                    clear - H1x2 Hinit3.
                                    ltac1:(set_solver).
                                }
                                {
                                    rewrite dom_insert in Hinit5.
                                    rewrite lookup_insert_ne in Hy0>[|ltac1:(congruence)].
                                    rewrite lookup_fmap in Hy0.
                                    rewrite fmap_Some in Hy0.
                                    destruct Hy0 as [x1 [H1x1 H2x1]].
                                    subst.
                                    rewrite map_lookup_filter in Hx0.
                                    rewrite bind_Some in Hx0.
                                    destruct Hx0 as [x2 [H1x2 H2x2]].
                                    simpl in *.
                                    rewrite option_guard_decide in H2x2.
                                    cases (); ltac1:(simplify_eq/=).
                                    rewrite dom_insert in n1.
                                    apply elem_of_dom_2 in H1x1.
                                    clear - H1x1 n1.
                                    ltac1:(set_solver).
                                }
                            }
                        }
                        {
                            apply map_disjoint_spec.
                            intros i' x' y' Hx' Hy'.
                            destruct (decide (i' = i)).
                            {
                                subst.
                                rewrite lookup_singleton in Hx'.
                                ltac1:(simplify_eq/=).
                                rewrite lookup_fmap in Hy'.
                                rewrite fmap_Some in Hy'.
                                destruct Hy' as [x [H1x H2x]].
                                ltac1:(simplify_eq/=).
                                apply elem_of_dom_2 in H1x.
                                ltac1:(contradiction n).
                            }
                            {
                                rewrite lookup_singleton_ne in Hx'.
                                inversion Hx'.
                                ltac1:(congruence).
                            }
                        }
                    }
                    {
                        apply dec_stable in n.
                        eapply elem_of_weaken in n>[|apply dom_subp_compose_subseteq].
                        rewrite dom_insert in Hinit3.
                        rewrite elem_of_union in n.
                        destruct n as [Hn|Hn].
                        {
                            clear - Hn Hinit3.
                            ltac1:(set_solver).
                        }
                        {
                            apply not_elem_of_dom_2 in H.
                            clear - H Hn.
                            ltac1:(set_solver).
                        }
                    }
                }
            }
            {
                rewrite subp_is_normal_spec.
                rewrite subp_is_normal_spec in Hsnorm.
                intros.
                destruct (decide (k = i)).
                {
                    subst.
                    intros HContra.
                    subst.
                    rewrite H in H0.
                    inversion H0.
                }
                {
                    apply Hsnorm.
                    rewrite lookup_insert_ne.
                    assumption.
                    ltac1:(congruence).
                }
            }
            {
                assumption.
            }
            {
                unfold subp_dom, SubP in *.
                rewrite dom_insert in Hinit2.
                clear - Hinit2.
                ltac1:(set_solver).
            }
            {
                unfold subp_dom, SubP in *.
                rewrite dom_insert in Hinit3.
                ltac1:(set_solver).
            }
            {
                unfold subp_dom, SubP in *.
                ltac1:(rewrite subp_codom_insert in Hinit4).
                {
                    unfold SubP.
                    apply not_elem_of_dom_2.
                    exact H.
                }
                { ltac1:(set_solver). }
            }
            {
                unfold subp_dom, SubP in *.
                ltac1:(rewrite subp_codom_insert in Hinit5).
                {
                    unfold SubP.
                    apply not_elem_of_dom_2.
                    exact H.
                }
                rewrite dom_insert in Hinit5.
                ltac1:(set_solver).
            }
        }
        {
            unfold subs_is_normal.
            rewrite subp_is_normal_spec in Hsnorm.
            rewrite Forall_forall.
            intros.
            apply Hsnorm.
            destruct x0.
            rewrite elem_of_map_to_list in H0.
            simpl.
            exact H0.
        }
        {
            unfold subs_is_normal.
            rewrite subp_is_normal_spec in Hsnorm.
            rewrite Forall_forall.
            intros.
            apply Hsnorm.
            destruct x0.
            simpl.
            rewrite elem_of_cons in H0.
            destruct H0 as [H0|H0].
            {
                ltac1:(simplify_eq/=).
                rewrite lookup_insert.
                reflexivity.
            }
            {
                rewrite elem_of_map_to_list in H0.
                rewrite lookup_insert_ne.
                {
                    exact H0.
                }
                {
                    intros HContra.
                    subst v.
                    ltac1:(rewrite H in H0).
                    inversion H0.
                }
            }
        }
        {
            apply NoDup_fst_map_to_list.
        }
        {
            rewrite fmap_cons.
            rewrite NoDup_cons.
            simpl.
            split>[|apply NoDup_fst_map_to_list].
            rewrite elem_of_list_fmap.
            intros [y [H1y H2y]].
            subst.
            destruct y.
            ltac1:(rewrite elem_of_map_to_list in H2y).
            simpl in H.
            rewrite H in H2y.
            inversion H2y.
        }
        {
            rewrite map_to_list_insert.
            {
                rewrite fmap_cons.
                rewrite fmap_cons.
                simpl.
                unfold subp_dom, SubP in *.
                rewrite dom_insert in Hinit2.
                rewrite dom_insert in Hinit3.
                ltac1:(rewrite subp_codom_insert in Hinit4).
                {
                    unfold SubP.
                    apply not_elem_of_dom_2.
                    exact H.
                }
                ltac1:(rewrite subp_codom_insert in Hinit5).
                {
                    unfold SubP.
                    apply not_elem_of_dom_2.
                    exact H.
                }
                rewrite dom_insert in Hinit5.
                unfold subp_codom in Hinit4.
                unfold subp_codom in Hinit5.
                apply not_elem_of_dom_2 in H.
                clear IHs.
                (* ltac1:(set_solver). *)
                rewrite elem_of_disjoint.
                intros x0 H1x0 H2x0.
                rewrite elem_of_union in H1x0.
                rewrite elem_of_union in H2x0.
                destruct H1x0 as [H1x0|H1x0].
                {
                    rewrite elem_of_singleton in H1x0.
                    subst x0.
                    destruct H2x0 as [H2x0|H2x0].
                    {
                        ltac1:(set_solver).
                    }
                    {
                        rewrite elem_of_union_list in H2x0.
                        destruct H2x0 as [X [H1X H2X]].
                        rewrite elem_of_list_fmap in H1X.
                        destruct H1X as [y [H1y H2y]].
                        subst.
                        rewrite elem_of_list_fmap in H2y.
                        destruct H2y as [z [H1z H2z]].
                        subst.
                        destruct z as [z1 z2].
                        simpl in *.
                        rewrite elem_of_map_to_list in H2z.
                        assert (i ∈ ⋃ (vars_of <$> elements (@map_img _ _ _ _ (listset _) _ _ _ m))).
                        {
                            rewrite elem_of_union_list.
                            exists (vars_of z2).
                            split>[|exact H2X].
                            rewrite elem_of_list_fmap.
                            exists z2.
                            split>[reflexivity|].
                            rewrite elem_of_elements.
                            rewrite elem_of_map_img.
                            exists z1.
                            exact H2z.
                        }
                        ltac1:(set_solver).
                    }
                }
                {
                    rewrite elem_of_list_to_set in H1x0.
                    rewrite elem_of_list_fmap in H1x0.
                    destruct H1x0 as [[y y'][H1y H2y]].
                    simpl in *.
                    rewrite elem_of_map_to_list in H2y.
                    subst.
                    destruct H2x0 as [H2x0|H2x0].
                    {
                        apply elem_of_dom_2 in H2y.
                        ltac1:(set_solver).
                    }
                    {
                        rewrite elem_of_union_list in H2x0.
                        destruct H2x0 as [X [H1X H2X]].
                        rewrite elem_of_list_fmap in H1X.
                        destruct H1X as [y'' [H1y'' H2y'']].
                        subst.
                        rewrite elem_of_list_fmap in H2y''.
                        destruct H2y'' as [z [H1z H2z]].
                        subst.
                        destruct z as [z1 z2].
                        simpl in *.
                        rewrite elem_of_map_to_list in H2z.
                        assert (y ∈ ⋃ (vars_of <$> elements (@map_img _ _ _ _ (listset _) _ _ _ m))).
                        {
                            rewrite elem_of_union_list.
                            exists (vars_of z2).
                            split>[|exact H2X].
                            rewrite elem_of_list_fmap.
                            exists z2.
                            split>[reflexivity|].
                            rewrite elem_of_elements.
                            rewrite elem_of_map_img.
                            exists z1.
                            exact H2z.
                        }
                        apply elem_of_dom_2 in H2y.
                        ltac1:(set_solver).
                    }
                }
            }
            { exact H. }
        }
        {
            rewrite fmap_cons.
            simpl.
            rewrite map_to_list_insert.
            {
                rewrite fmap_cons.
                rewrite fmap_cons.
                simpl.

                unfold subp_dom, SubP in *.
                rewrite dom_insert in Hinit2.
                rewrite dom_insert in Hinit3.
                ltac1:(rewrite subp_codom_insert in Hinit4).
                {
                    unfold SubP.
                    apply not_elem_of_dom_2.
                    exact H.
                }
                ltac1:(rewrite subp_codom_insert in Hinit5).
                {
                    unfold SubP.
                    apply not_elem_of_dom_2.
                    exact H.
                }
                rewrite dom_insert in Hinit5.
                unfold subp_codom in Hinit4.
                unfold subp_codom in Hinit5.
                apply not_elem_of_dom_2 in H.
                clear IHs.
                (* ltac1:(set_solver). *)
                rewrite elem_of_disjoint.
                intros x0 H1x0 H2x0.
                rewrite elem_of_union in H1x0.
                rewrite elem_of_union in H2x0.
                destruct H1x0 as [H1x0|H1x0].
                {
                    rewrite elem_of_singleton in H1x0.
                    subst x0.
                    destruct H2x0 as [H2x0|H2x0].
                    {
                        ltac1:(set_solver).
                    }
                    {
                        rewrite elem_of_union_list in H2x0.
                        destruct H2x0 as [X [H1X H2X]].
                        rewrite elem_of_list_fmap in H1X.
                        destruct H1X as [y [H1y H2y]].
                        subst.
                        rewrite elem_of_list_fmap in H2y.
                        destruct H2y as [z [H1z H2z]].
                        subst.
                        destruct z as [z1 z2].
                        simpl in *.
                        rewrite elem_of_map_to_list in H2z.
                        assert (i ∈ ⋃ (vars_of <$> elements (@map_img _ _ _ _ (listset _) _ _ _ m))).
                        {
                            rewrite elem_of_union_list.
                            exists (vars_of z2).
                            split>[|exact H2X].
                            rewrite elem_of_list_fmap.
                            exists z2.
                            split>[reflexivity|].
                            rewrite elem_of_elements.
                            rewrite elem_of_map_img.
                            exists z1.
                            exact H2z.
                        }
                        ltac1:(set_solver).
                    }
                }
                {
                    rewrite elem_of_list_to_set in H1x0.
                    rewrite elem_of_list_fmap in H1x0.
                    destruct H1x0 as [[y y'][H1y H2y]].
                    simpl in *.
                    rewrite elem_of_map_to_list in H2y.
                    subst.
                    destruct H2x0 as [H2x0|H2x0].
                    {
                        apply elem_of_dom_2 in H2y.
                        ltac1:(set_solver).
                    }
                    {
                        rewrite elem_of_union_list in H2x0.
                        destruct H2x0 as [X [H1X H2X]].
                        rewrite elem_of_list_fmap in H1X.
                        destruct H1X as [y'' [H1y'' H2y'']].
                        subst.
                        rewrite elem_of_list_fmap in H2y''.
                        destruct H2y'' as [z [H1z H2z]].
                        subst.
                        destruct z as [z1 z2].
                        simpl in *.
                        rewrite elem_of_map_to_list in H2z.
                        assert (y ∈ ⋃ (vars_of <$> elements (@map_img _ _ _ _ (listset _) _ _ _ m))).
                        {
                            rewrite elem_of_union_list.
                            exists (vars_of z2).
                            split>[|exact H2X].
                            rewrite elem_of_list_fmap.
                            exists z2.
                            split>[reflexivity|].
                            rewrite elem_of_elements.
                            rewrite elem_of_map_img.
                            exists z1.
                            exact H2z.
                        }
                        apply elem_of_dom_2 in H2y.
                        ltac1:(set_solver).
                    }
                }
            }
            { exact H. }
        }
        {
            rewrite map_to_list_insert.
            { reflexivity. }
            { exact H. }
        }
    }
Qed.

Lemma make_parallel_map_to_list
    {Σ : StaticModel}
    (s : gmap variable (TermOver BuiltinOrVar))
    :
    subp_is_normal s ->
    (subp_codom s) ## subp_dom s ->
    make_parallel (map_to_list s) = s
.
Proof.
    intros H1 H2.
    unfold make_parallel.
    rewrite make_parallel0_map_to_list.
    {
        rewrite subp_compose_empty_l.
        { reflexivity. }
        { exact H1. }
    }
    {
        exact H1.
    }
    {
        unfold subp_is_normal.
        unfold subp_normalize.
        rewrite map_filter_empty.
        reflexivity.
    }
    {
        unfold subp_codom.
        unfold SubP in *.
        rewrite map_img_empty.
        rewrite elements_empty.
        simpl.
        ltac1:(set_solver).
    }
    {
        unfold subp_dom.
        unfold SubP.
        rewrite dom_empty.
        ltac1:(set_solver).
    }
    {
        unfold subp_dom.
        unfold SubP.
        rewrite dom_empty.
        ltac1:(set_solver).
    }
    {
        exact H2.
    }
Qed.

Lemma subp_codom_renaming_for_disjoint_dom_m
    {Σ : StaticModel}
    avoid0 m
:
    subp_codom (rlift (renaming_for avoid0 m)) ## dom m
.
Proof.
    unfold subp_codom.
    unfold renaming_for.
    unfold rlift.
    rewrite elem_of_disjoint.
    intros x H1x H2x.
    rewrite elem_of_union_list in H1x.
    destruct H1x as [X [H1X H2X]].
    rewrite elem_of_list_fmap in H1X.
    destruct H1X as [y [H1y H2y]].
    rewrite elem_of_elements in H2y.
    unfold SubP in *.
    rewrite elem_of_map_img in H2y.
    destruct H2y as [i Hi].
    rewrite lookup_fmap in Hi.
    rewrite fmap_Some in Hi.
    destruct Hi as [z [H1z H2z]].
    subst.
    rewrite <- elem_of_list_to_map in H1z.
    {
        unfold vars_of in H2X; simpl in H2X.
        unfold vars_of in H2X; simpl in H2X.
        rewrite elem_of_singleton in H2X.
        subst z.
        apply elem_of_zip_r in H1z.
        apply elem_of_fresh_var_seq in H1z.
        rewrite elem_of_app in H1z.
        rewrite elem_of_elements in H1z.
        ltac1:(set_solver).
    }
    {
        rewrite fst_zip.
        apply NoDup_elements.
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
Qed.

Lemma subp_codom_make_parallel0
    {Σ : StaticModel}
    m s
    :
    subp_codom (make_parallel0 m s) ⊆ subp_codom m ∪ subt_codom s
.
Proof.
    unfold subp_codom.
    (* unfold make_parallel0. *)
    revert m.
    induction s; intros m.
    {
        simpl.
        ltac1:(set_solver).
    }
    {
        simpl.
        assert (H1 := map_img_subp_compose {[a.1 := a.2]} (make_parallel0 m s)).
        rewrite map_img_singleton in H1.
        unfold subt_codom.
        rewrite fmap_cons.
        rewrite fmap_cons.
        rewrite union_list_cons.
        rewrite elem_of_subseteq.
        intros x Hx.
        rewrite elem_of_union_list in Hx.
        destruct Hx as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst.
        rewrite elem_of_elements in H2y.
        eapply elem_of_weaken in H2y>[|apply H1].
        rewrite elem_of_union in H2y.
        rewrite elem_of_union.
        destruct H2y as [H2y|H2y].
        {
            right.
            ltac1:(set_solver).
        }
        {
            clear H1.
            rewrite elem_of_map_img in H2y.
            destruct H2y as [i Hi].
            rewrite lookup_fmap in Hi.
            rewrite fmap_Some in Hi.
            destruct Hi as [z [H1z H2z]].
            subst.
            specialize (IHs m).
            rewrite elem_of_subseteq in IHs.
            (* rewrite subp_app_singleton in H2X. *)
            (* Check subp_app_insert_2. *)
            rewrite <- insert_empty in H2X.
            ltac1:(rewrite subp_app_insert_2 in H2X).
            {
                unfold subp_dom, SubP.
                rewrite dom_empty.
                ltac1:(set_solver).
            }
            ltac1:(rewrite subp_app_empty in H2X).
            simpl in H2X.
            destruct (decide (a.1 ∈ vars_of z)).
            {
                rewrite vars_of_TermOverBoV_subst in H2X.
                {
                    rewrite elem_of_union in H2X.
                    destruct H2X as [H2X|H2X].
                    {
                        right.
                        ltac1:(set_solver).
                    }
                    {
                        rewrite elem_of_difference in H2X.
                        destruct H2X as [Hxz Hxa].
                        specialize (IHs x).
                        ltac1:(ospecialize (IHs _)).
                        {
                            rewrite elem_of_union_list.
                            exists (vars_of z).
                            split>[|assumption].
                            rewrite elem_of_list_fmap.
                            exists z.
                            split>[reflexivity|].
                            rewrite elem_of_elements.
                            ltac1:(rewrite elem_of_map_img).
                            exists i.
                            exact H1z.
                        }
                        unfold subt_codom in IHs.
                        ltac1:(set_solver).
                    }
                }
                {
                    assumption.
                }
            }
            {
                rewrite subst_notin2 in H2X>[|ltac1:(congruence)].
                specialize (IHs x).
                ltac1:(ospecialize (IHs _)).
                {
                    rewrite elem_of_union_list.
                    exists (vars_of z).
                    split>[|assumption].
                    rewrite elem_of_list_fmap.
                    exists z.
                    split>[reflexivity|].
                    rewrite elem_of_elements.
                    ltac1:(rewrite elem_of_map_img).
                    exists i.
                    exact H1z.
                }
                unfold subt_codom in IHs.
                ltac1:(set_solver).
            }
        }
    }
Qed.


Lemma subp_dom_inverse {Σ : StaticModel} r:
    renaming_ok r ->
    subp_dom (rlift (r_inverse r)) = subp_codom (rlift r)
.
Proof.
    intros Hrok.
    unfold subp_dom, subp_codom, rlift, r_inverse, SubP in *.
    rewrite dom_fmap_L.
    unfold pair_swap.
    (* Search map_img fmap. *)
    apply set_eq.
    intros x.
    rewrite elem_of_dom.
    rewrite elem_of_union_list.
    split.
    {
        intros [y Hy].
        rewrite <- elem_of_list_to_map in Hy.
        {
            rewrite elem_of_list_fmap in Hy.
            destruct Hy as [[z1 z2][H1z H2z]].
            ltac1:(simplify_eq/=).
            rewrite elem_of_map_to_list in H2z.
            exists ({[z2]}).
            split>[|ltac1:(set_solver)].
            rewrite elem_of_list_fmap.
            exists (t_over (bov_variable z2)).
            split.
            {
                reflexivity.
            }
            {
                rewrite elem_of_elements.
                rewrite elem_of_map_img.
                exists z1.
                rewrite lookup_fmap.
                rewrite H2z.
                simpl.
                reflexivity.
            }
        }
        {
            rewrite <- list_fmap_compose.
            unfold compose.
            simpl.
            apply renaming_ok_nodup.
            exact Hrok.
        }
    }
    {
        intros [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst.
        rewrite elem_of_elements in H2y.
        rewrite elem_of_map_img in H2y.
        destruct H2y as [i Hi].
        rewrite lookup_fmap in Hi.
        rewrite fmap_Some in Hi.
        destruct Hi as [z [H1z H2z]].
        subst.
        unfold vars_of in H2X; simpl in H2X.
        unfold vars_of in H2X; simpl in H2X.
        rewrite elem_of_singleton in H2X.
        subst.
        exists i.
        rewrite <- elem_of_list_to_map.
        {
            rewrite elem_of_list_fmap.
            exists (i, z).
            split>[reflexivity|].
            rewrite elem_of_map_to_list.
            exact H1z.
        }
        {
            rewrite <- list_fmap_compose.
            unfold compose.
            simpl.
            apply renaming_ok_nodup.
            exact Hrok.   
        }
    }
Qed.

Lemma subp_codom_inverse {Σ : StaticModel} r:
    renaming_ok r ->
    subp_codom (rlift (r_inverse r)) = subp_dom (rlift r)
.
Proof.
    intros Hrok.
    rewrite <- (r_inverse_inverse r) at 2.
    symmetry.
    rewrite subp_dom_inverse.
    reflexivity.
    apply r_inverse_ok.
    exact Hrok.
    exact Hrok.
Qed.

Lemma subt_codom_map_to_list
    {Σ : StaticModel}
    m
    :
    subt_codom (map_to_list m) = subp_codom m
.
Proof.
    unfold subt_codom,subp_codom, SubP in *.
    (* rewrite <- list_fmap_compose. *)
    apply set_eq.
    intros x.
    rewrite elem_of_union_list.
    rewrite elem_of_union_list.
    split; intros [X HX].
    {
        destruct HX as [H1X H2X].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        rewrite elem_of_list_fmap in H2y.
        destruct H2y as [z [H1z H2z]].
        subst.
        destruct z.
        rewrite elem_of_map_to_list in H2z.
        simpl in *.
        exists (vars_of t).
        split>[|assumption].
        rewrite elem_of_list_fmap.
        exists t.
        split>[reflexivity|].
        rewrite elem_of_elements.
        rewrite elem_of_map_img.
        exists v.
        exact H2z.
    }
    {
        destruct HX as [H1X H2X].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst.
        rewrite elem_of_elements in H2y.
        rewrite elem_of_map_img in H2y.
        destruct H2y as [i Hi].
        exists (vars_of y).
        split>[|assumption].
        rewrite elem_of_list_fmap.
        exists y.
        split>[reflexivity|].
        rewrite elem_of_list_fmap.
        exists (i, y).
        split>[reflexivity|].
        rewrite elem_of_map_to_list.
        exact Hi.
    }
Qed.

Lemma to_serial_then_to_parallel
    {Σ : StaticModel}
    (avoid0 : gset variable)
    (m : gmap variable (TermOver BuiltinOrVar))
    :
    dom m ## subp_codom m ->
    subp_is_normal m ->
    subp_restrict (dom m) (make_parallel (make_serial0 m avoid0)) = m
.
Proof.
    intros 
        Hdocodo
        Hnorm.
    (* TODO extract lemma *)
    assert(Hhelp: subp_codom (rlift (r_inverse (renaming_for avoid0 m)))
        ## subp_dom (rlift (r_inverse (renaming_for avoid0 m)))).
    {
        assert (Htmp2 := map_img_renaming_for_dom m avoid0).
        assert (Htmp3 := map_img_renaming_for_codom avoid0 m).
        rewrite elem_of_disjoint.
        intros x H1x H2x.
        unfold subp_codom,subp_dom,SubP in *.
        rewrite elem_of_union_list in H1x.
        destruct H1x as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst.
        rewrite elem_of_elements in H2y.
        rewrite elem_of_map_img in H2y.
        destruct H2y as [i H1i].
        rewrite elem_of_dom in H2x.
        destruct H2x as [z Hz].
        unfold rlift in *.
        rewrite lookup_fmap in H1i.
        rewrite lookup_fmap in Hz.
        rewrite fmap_Some in H1i.
        rewrite fmap_Some in Hz.
        destruct H1i as [z' [H1z' H2z']].
        destruct Hz as [z'' [H1z'' H2z'']].
        subst.
        unfold r_inverse in *.
        rewrite <- elem_of_list_to_map in H1z''.
        {
            rewrite <- elem_of_list_to_map in H1z'.
            {
                rewrite elem_of_list_fmap in H1z'.
                rewrite elem_of_list_fmap in H1z''.
                destruct H1z' as [[a a'][H1a H2a]].
                destruct H1z'' as [[b b'][H1b H2b]].
                unfold pair_swap in *.
                simpl in *.
                ltac1:(simplify_eq/=).
                unfold vars_of in H2X; simpl in H2X.
                unfold vars_of in H2X; simpl in H2X.
                rewrite elem_of_singleton in H2X.
                subst b'.
                rewrite elem_of_map_to_list in H2a.
                rewrite elem_of_map_to_list in H2b.

                
                assert(H1: a ∈ @map_img _ _ _ _ (gset _) _ _ _ (renaming_for avoid0 m)).
                {
                    rewrite elem_of_map_img.
                    exists b.
                    apply H2b.
                }


                unfold renaming_for in H2b.
                rewrite <- elem_of_list_to_map in H2b.
                {
                    apply elem_of_zip_l in H2b.
                    rewrite elem_of_elements in H2b.
                    ltac1:(rewrite elem_of_dom in H2b).
                    destruct H2b as [x Hx].

                    unfold renaming_for in H2a.
                    rewrite <- elem_of_list_to_map in H2a.
                    {
                        apply elem_of_zip_l in H2a.
                        rewrite elem_of_elements in H2a.
                        rewrite elem_of_disjoint in Htmp2.
                        apply (Htmp2 a).
                        {
                            exact H1.
                        } 
                        {
                            exact H2a.
                        }
                    }
                    {
                        rewrite fst_zip.
                        apply NoDup_elements.
                        rewrite length_fresh_var_seq.
                        ltac1:(lia).
                    }
                }
                {
                    rewrite fst_zip.
                    apply NoDup_elements.
                    rewrite length_fresh_var_seq.
                    ltac1:(lia).
                }
            }
            {
                rewrite <- list_fmap_compose.
                unfold pair_swap, compose.
                simpl.
                unfold renaming_for.
                rewrite map_to_list_to_map.
                {
                    rewrite snd_zip.
                    apply NoDup_fresh_var_seq.
                    rewrite length_fresh_var_seq.
                    ltac1:(lia).
                }
                {
                    rewrite fst_zip.
                    apply NoDup_elements.
                    rewrite length_fresh_var_seq.
                    ltac1:(lia).
                }    
            }

        }
        {
            rewrite <- list_fmap_compose.
            unfold pair_swap, compose.
            simpl.
            unfold renaming_for.
            rewrite map_to_list_to_map.
            {
                rewrite snd_zip.
                apply NoDup_fresh_var_seq.
                rewrite length_fresh_var_seq.
                ltac1:(lia).
            }
            {
                rewrite fst_zip.
                apply NoDup_elements.
                rewrite length_fresh_var_seq.
                ltac1:(lia).
            }
        }
    }
    unfold make_serial0.
    rewrite make_parallel_app.
    {
        rewrite make_parallel_map_to_list.
        {
            ltac1:(rewrite make_parallel_map_to_list).
            {
                unfold SubP in *.
                apply renaming_is_normal.
            }
            {
                rewrite subp_codom_inverse in Hhelp.
                rewrite subp_dom_inverse in Hhelp.
                ltac1:(set_solver).
                apply renaming_for_ok.
                apply renaming_for_ok.
            }
            {
                ltac1:(rewrite subp_compose_assoc).
                {
                    apply inverse_of_renaming_is_normal.
                }
                {
                    assert (Htmp1 := compose_renaming_inverse_restrict (renaming_for avoid0 m) (dom m ∪ subp_codom m)).
                    ltac1:(ospecialize (Htmp1 _)).
                    {
                        apply renaming_for_ok.
                    }
                    rewrite dom_renaming_for in Htmp1.
                    unfold subp_dom in Htmp1.
                    ltac1:(ospecialize (Htmp1 _)).
                    {
                        clear Htmp1.
                        unfold SubP in *.
                        assert (Htmp2 := map_img_renaming_for_dom m avoid0).
                        assert (Htmp3 := map_img_renaming_for_codom avoid0 m).
                        ltac1:(set_solver).
                    }

                    ltac1:(rewrite <- subp_restrict_id_2 with (vars := subp_dom m ∪ subp_codom m) in Htmp1).
                    unfold subp_dom, SubP in *.
                    rewrite <- restrict_id with (vars := subp_dom m).
                    {
                        unfold subp_dom, SubP in *.
                        apply restrict_more with (vars := dom m ∪ (subp_codom m)).
                        {
                            clear.
                            ltac1:(set_solver).
                        }
                        eapply restrict_equiv_2 in Htmp1.
                        erewrite Htmp1.
                        {
                            rewrite subp_compose_id.
                            { reflexivity. }
                            { exact Hnorm. }
                        }
                    }
                    {
                        unfold subp_dom, SubP.
                        apply reflexivity.
                    }
                }
            }
        }
        {
            apply subp_is_normal_normalize.
        }
        {
            assert (Htmp2 := subp_codom_subp_compose_2 (rlift (renaming_for avoid0 m)) m).
            assert (Htmp3 := dom_subp_compose_subseteq (rlift (renaming_for avoid0 m)) m).
            
            assert (Htmp4: subp_codom (rlift (renaming_for avoid0 m)) ∪ subp_codom m ## dom (rlift (renaming_for avoid0 m)) ∪ dom m).
            {
                assert (Htmp5 := subp_codom_renaming_for_disjoint_dom_m avoid0 m).
                unfold subp_dom, SubP in *.
                unfold rlift at 2.
                rewrite dom_fmap.
                rewrite dom_renaming_for.
                unfold subp_dom.
                ltac1:(set_solver).
            }
            unfold subp_dom,subp_dom, SubP in *.
            ltac1:(set_solver).
        }
    }
    {
        assert (subp_is_normal (subp_compose (rlift (renaming_for avoid0 m)) m)).
        {
            apply subp_is_normal_normalize.
        }
        rewrite subp_is_normal_spec in H.
        (* Search subp_compose subp_is_normal. *)
        unfold subs_is_normal.
        rewrite Forall_forall.
        intros [x p] H1x H2x.
        simpl in *.
        subst p.
        rewrite elem_of_map_to_list in H1x.
        apply (H x (t_over (bov_variable x)) H1x eq_refl).
    }
    {
        rewrite <- dom_alt.
        rewrite subp_codom_inverse in Hhelp.
        {
            rewrite subp_dom_inverse in Hhelp.
            {
                (* THIS DOES NOT MAKE ANY SENSE *)
                rewrite subp_dom_renaming_for in Hhelp.
            }
            {
                apply renaming_for_ok.
            }
        }
        {
            apply renaming_for_ok.
        }
        assert (Htmp1 := dom_subp_compose_subseteq (rlift (renaming_for avoid0 m)) m).
        assert (Htmp0 := subp_codom_make_parallel0 ∅ (map_to_list ((rlift (r_inverse (renaming_for avoid0 m)))))).
        unfold make_parallel.
        assert (Htmp3: subt_codom (map_to_list (rlift (r_inverse (renaming_for avoid0 m)))) ## dom m).
        {
            clear Htmp0 Htmp1.
            rewrite subp_codom_inverse in Hhelp.
            {
                rewrite subp_dom_inverse in Hhelp.
                {
                    unfold subp_dom in Hhelp.
                    unfold rlift in Hhelp at 1.
                    unfold SubP in *.
                    rewrite dom_fmap in Hhelp.
                    rewrite dom_renaming_for in Hhelp.
                    (* Check subt_codom_map_to_list. *)
                    ltac1:(rewrite subt_codom_map_to_list).
                    rewrite subp_codom_inverse.
                    {
                        unfold subp_dom.
                        unfold SubP in *.
                        unfold rlift.
                        rewrite dom_fmap.
                        rewrite dom_renaming_for.
                        (* Search subp_dom renaming_for. *)
                    }
                    {
                        apply renaming_for_ok.
                    }
                    (* Search subt_codom. *)
                    (* unfold subt_codom. *)
                    Search subp_codom renaming_for.
                }
                {
                    apply renaming_for_ok.    
                }
            }
            {
                apply renaming_for_ok.
            }
        }
        unfold subp_codom in Htmp0 at 2.
        unfold SubP in *.
        rewrite map_img_empty in Htmp0.
        rewrite elements_empty in Htmp0.
        simpl in Htmp0.
        rewrite (left_id empty union) in Htmp0.
        unfold rlift in Htmp1 at 2.
        rewrite dom_fmap in Htmp1.
        ltac1:(rewrite dom_renaming_for in Htmp1).
        ltac1:(set_solver).
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


(* 
Lemma NoDup_1_renaming_for
    {Σ : StaticModel}
    (sub_mm : gmap variable (TermOver BuiltinOrVar))
    :
    NoDup (fst <$> (renaming_for sub_mm))
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
Qed. *)

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
(* 
Check subp_app_restrict.
Lemma subp_app_restrict
    {Σ : StaticModel}
    (a : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    :
    subp_app (subp_restrict vars a) = subp_app a
. *)

(* Lemma subt_closed_make_serial
    {Σ : StaticModel}
    (a : gmap variable (TermOver BuiltinOrVar))
    :
    subt_closed (make_serial a)
.
Proof.
    unfold subt_closed.
    Search make_serial.
    unfold make_serial.
    intros k [x p] H.
    simpl.
    (* unfold subp_compose,subp_normalize in H. *)
    unfold SubP,SubS in *.
    Search map_to_list.
    Search (map_to_list _ !! _ = _).
    rewrite lookup_map_to_list in H.
    Set Printing Implicit.
    ltac1:(rewrite - elem_of_map_to_list in H).
Qed. *)



Lemma renaming_for_avoid
    {Σ : StaticModel}
    (avoid0 : gset variable)
    (a : gmap variable (TermOver BuiltinOrVar))
    :
    avoid0 ## map_img (renaming_for avoid0 a)
.
Proof.
    unfold renaming_for.
    rewrite elem_of_disjoint.
    intros x H1x H2x.
    rewrite elem_of_map_img in H2x.
    destruct H2x as [y Hy].
    ltac1:(rewrite - elem_of_list_to_map in Hy).
    {
        rewrite fst_zip.
        apply NoDup_elements.
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
    apply elem_of_zip_r in Hy.
    apply elem_of_fresh_var_seq in Hy.
    rewrite elem_of_app in Hy.
    apply not_or_and in Hy.
    destruct Hy as [H1 H2].
    rewrite elem_of_elements in H2.
    ltac1:(set_solver).
Qed.

(* Lemma to_parallel_then_to_serial
    {Σ : StaticModel}
    (avoid0 : gset variable)
    s
    :
    (make_serial0 (make_parallel s) avoid0) ≡ₚ s
.
Proof.
    unfold make_parallel.
    unfold make_serial0.
Qed. *)

Lemma in_sub_impl_not_in_dom_rlift_inverse_renaming {Σ : StaticModel} a avoid x:
    x ∈ dom a ->
    x ∉ dom (rlift (r_inverse (renaming_for avoid a)))
.
Proof.
    intros HH.
    rewrite dom_rlift_inverse.
    assert (Htmp := map_img_renaming_for_dom a avoid).
    ltac1:(set_solver).
Qed.
(* 
Lemma make_serial_lookup
    {Σ : StaticModel}
    (a : gmap variable (TermOver BuiltinOrVar))
    (vars : gset variable)
    (x : variable)
    (p : TermOver BuiltinOrVar)
    :
    subp_is_normal a ->
    a !! x = Some p ->
    (x, p) ∈ (make_serial0 a vars)
.
Proof.
    intros Hna Haxp.
    unfold make_serial0.
    rewrite elem_of_map_to_list.
    unfold subp_compose at 1.
    unfold subp_normalize at 1.
    rewrite map_lookup_filter.
    rewrite bind_Some.
    simpl.
    assert (p <> t_over (bov_variable x)).
    {
        intros ?.
        subst p.
        unfold subp_is_normal in Hna.
        rewrite <- Hna in Haxp.
        unfold subp_normalize in Haxp.
        rewrite map_lookup_filter in Haxp.
        rewrite bind_Some in Haxp.
        destruct Haxp as [p [H1p H2p]].
        rewrite option_guard_decide in H2p.
        cases (); ltac1:(simplify_eq/=).
    }
    exists p.
    rewrite option_guard_decide.
    cases ().
    {
        split>[|reflexivity].
        rewrite lookup_union.
        rewrite union_Some.
        right.
        split.
        {
            rewrite map_lookup_filter.
            simpl.
            rewrite bind_None.
            left.
            apply elem_of_dom_2 in Haxp.
            apply not_elem_of_dom_1.
            apply in_sub_impl_not_in_dom_rlift_inverse_renaming.
            exact Haxp.
        }
        {
            rewrite lookup_fmap.
            rewrite fmap_Some.
            exists p.
            split.
            {
                unfold subp_compose.
                unfold subp_normalize.
                rewrite map_lookup_filter.
                rewrite bind_Some.
                exists p.
                simpl.
                rewrite option_guard_True.
                {
                    rewrite lookup_union.
                    split>[|reflexivity].
                    rewrite union_Some.
                    left.
                    rewrite map_lookup_filter.
                    rewrite bind_Some.
                    exists p.
                    rewrite option_guard_decide.
                    split.
                    {

                    }
                    {
                        simpl.
                        cases (); try reflexivity.
                        apply dec_stable in n0.
                    }
                    right.
                    split.
                    {
                        rewrite map_lookup_filter.
                        rewrite bind_None.
                        left.
                        apply elem_of_dom_2 in Haxp.
                        apply not_elem_of_dom_1.
                        unfold rlift.
                        rewrite dom_fmap.
                        rewrite dom_renaming_for.
                        unfold subp_dom.
                        Search renaming_for.
                    }
                    {

                    }
                }
                {
                    ltac1:(congruence).
                }
                
            }
            {
                rewrite subp_app_almost_closed.
                { reflexivity. }
                {
                    unfold subp_dom.
                    (* unfold SubP in *. *)
                    rewrite dom_rlift_inverse.
                    assert(Htmp1 := map_img_renaming_for_codom vars a).
                    unfold subp_codom in *; unfold SubP in *.
                    rewrite elem_of_disjoint.
                    intros y H1y H2y.
                    rewrite elem_of_disjoint in Htmp1.
                    specialize (Htmp1 y H2y).
                    apply Htmp1. clear Htmp1.
                    rewrite elem_of_union_list.
                    exists (vars_of p).
                    split>[|assumption].
                    rewrite elem_of_list_fmap.
                    exists p.
                    split>[reflexivity|].
                    rewrite elem_of_elements.
                    rewrite elem_of_map_img.
                    exists x.
                    exact Haxp.
                }
            }
        }
    }
    {
        ltac1:(exfalso).
        apply dec_stable in n.
        subst p.
        ltac1:(contradiction).
    }
    (* unfold subp_is_normal in Hna. *)
    (* rewrite *)

Qed. *)
(* I need to ensure that make_serial0 creates a non-looping substitution
   and then I can assume it with the ugly lemma above.
 *)
(* TODO *)
Lemma make_serial_correct
    {Σ : StaticModel}
    (a : gmap variable (TermOver BuiltinOrVar))
    (φ : TermOver BuiltinOrVar)
    (vars : gset variable)
:
    subp_is_normal a ->
    vars_of φ ⊆ vars ->
    subs_app (make_serial0 a vars) φ = subp_app a φ
.
Proof.
    intros Hnormal Hvars.
    unfold SubP in *.
    unfold TermOver in *.
    (* TODO need to avoid vars of ϕ when creating the serial substitution *)

    revert a Hnormal Hvars.
    induction φ; intros aa Hnormal Hvars.
    {
        simpl.
        destruct a.
        {
            rewrite subs_app_builtin.
            reflexivity.
        }
        {
            unfold SubP in *.
            destruct (aa !! x) eqn:Haax.
            {
                ltac1:(rewrite Haax).
                rewrite <- make_parallel_correct.
                {

                }
                {
                    Search make_serial.
                }
            }
            {
                ltac1:(rewrite Haax).
                rewrite subs_app_untouched.
                { reflexivity. }
                {

                    unfold make_serial.
                    unfold vars_of; simpl.
                    unfold vars_of; simpl.
                    rewrite disjoint_singleton_l.
                    rewrite elem_of_list_to_set.
                    rewrite elem_of_list_fmap.
                    intros [[y p] [H1 H2]].
                    subst.
                    simpl in *.
                    apply elem_of_map_to_list in H2.
                    apply elem_of_dom_2 in H2.
                    eapply elem_of_weaken in H2>[|apply dom_subp_compose_subseteq].
                    rewrite elem_of_union in H2.
                    destruct H2 as [H|H].
                    {
                        unfold rlift in H.
                        unfold SubP in *.
                        rewrite dom_fmap in H.
                        unfold r_inverse in H.
                        rewrite elem_of_dom in H.
                        destruct H as [q Hq].
                        ltac1:(rewrite - elem_of_list_to_map in Hq).
                        {
                            rewrite <- list_fmap_compose.
                            unfold compose.
                            simpl.
                            apply renaming_ok_nodup.
                            apply renaming_for_ok.
                        }
                        rewrite elem_of_list_fmap in Hq.
                        destruct Hq as [[z1 z2][H1z H2z]].
                        unfold pair_swap in *.
                        ltac1:(simplify_eq/=).
                        rewrite elem_of_map_to_list in H2z.
                        assert (Htmp := renaming_for_avoid vars aa).
                        unfold SubP in *.
                        assert (z2 ∈ (@map_img _ _ _ _ (gset variable) _ _ _ ) (renaming_for vars aa)).
                        {
                            eapply elem_of_map_img_2.
                            apply H2z.
                        }
                        unfold vars_of in Hvars; simpl in Hvars.
                        unfold vars_of in Hvars; simpl in Hvars.
                        ltac1:(set_solver).
                    }
                    {
                        unfold subp_compose, subp_normalize in H.
                        unfold SubP in *.
                        rewrite elem_of_dom in H.
                        destruct H as [q Hq].
                        rewrite map_lookup_filter in Hq.
                        rewrite bind_Some in Hq.
                        destruct Hq as [q' [H1 H2]].
                        simpl in *.
                        rewrite option_guard_decide in H2.
                        cases (); ltac1:(simplify_eq/=).
                        rewrite lookup_union in H1.
                        rewrite union_Some in H1.
                        destruct H1 as [H|H].
                        {
                            rewrite map_lookup_filter in H.
                            rewrite bind_Some in H.
                            destruct H as [x [H1x H2x]].
                            simpl in *.
                            rewrite option_guard_decide in H2x.
                            cases (); ltac1:(simplify_eq/=).
                            unfold subp_dom, SubP in *.

                            apply elem_of_dom_2 in H1x.
                            ltac1:(rename H1x into H).
                            unfold rlift in H.
                            unfold SubP in *.
                            rewrite dom_fmap in H.
                            unfold r_inverse in H.
                            rewrite elem_of_dom in H.
                            destruct H as [q' Hq'].
                            ltac1:(rewrite - elem_of_list_to_map in Hq').
                            {
                                rewrite fst_zip.
                                apply NoDup_elements.
                                rewrite length_fresh_var_seq.
                                ltac1:(lia).
                            }
                            apply elem_of_zip_l in Hq'.
                            rewrite elem_of_elements in Hq'.
                            ltac1:(contradiction).
                        }
                        {
                            destruct H as [? H].
                            rewrite lookup_fmap in H.
                            ltac1:(rewrite Haax in H).
                            simpl in H.
                            inversion H.
                        }
                    }
                }
            }
        }
    }

    Check make_parallel_correct.
    
    rewrite <- (to_serial_then_to_parallel a) at 2.
    {

        (* not this way *)
        (* rewrite restrict_more with (vars := dom a ∪ vars_of φ)(b := a). *)
        
        Search subp_restrict.
        rewrite subp_app_restrict.
        { rewrite make_parallel_correct; admit. }
        {

        }
    }
    {
        exact Hnormal.
    }


    ltac1:(rewrite <- (restrict_id a (dom a)) at 1).
    (* Search subp_restrict dom. *)
    ltac1:(rewrite <- (subp_app_restrict a (dom a))).
    Check make_parallel_correct.
    rewrite <- make_parallel_correct.
    {

    }
    {
        Search subt_closed.
    }
Qed. *)
