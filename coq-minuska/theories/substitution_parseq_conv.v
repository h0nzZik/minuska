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

(* TODO use fold *)
Fixpoint subT_to_subTMM
    {Σ : StaticModel}
    (sub : SubS)
    : SubP
:=
    match sub with
    | [] => ∅
    | e::es =>
        let subes := subT_to_subTMM es in
        <[e.1 := e.2]>subes
    end
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


Definition renaming_for
    {Σ : StaticModel}
    (sub_mm : SubP)
    :
    list (variable*variable)
:=
    let rhss : list (TermOver BuiltinOrVar) := snd <$> map_to_list sub_mm in
    let avoid : list variable := elements (union_list (vars_of <$> rhss)) in
    let to_be_renamed : list variable := elements (dom sub_mm) in
    (* [] *)
    zip to_be_renamed (fresh_var_seq (to_be_renamed ++ avoid) (length to_be_renamed))
.

Definition subTMM_to_subT
    {Σ : StaticModel}
    (sub_mm : SubP)
    :
    SubS
:=
    let subl : list (variable*(TermOver BuiltinOrVar)) := map_to_list sub_mm in
    let renaming := renaming_for sub_mm in
    let rnmap : gmap variable variable := list_to_map renaming in
    let subl_renamed : list (variable*(TermOver BuiltinOrVar)) := (fun kv => match rnmap !! kv.1 with None => kv | Some y => (y, kv.2) end) <$> subl in
    subl_renamed ++ ((fun xy => (xy.1, t_over (bov_variable xy.2)))<$> renaming)
.


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


Lemma subT_to_subTMM_correct
    {Σ : StaticModel}
    (sub : SubS)
    (φ : TermOver BuiltinOrVar)
    :
    subt_closed sub ->
    subp_app (subT_to_subTMM sub) φ = subs_app sub φ
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
Lemma subTMM_to_subT_correct
    {Σ : StaticModel}
    (sub_mm : SubP)
    (φ : TermOver BuiltinOrVar)
:
    subs_app (subTMM_to_subT sub_mm) φ = subp_app sub_mm φ
.
Proof.
    unfold subTMM_to_subT.
    remember (renaming_for sub_mm) as rn.
    unfold renaming_for in Heqrn.
    remember ((elements (dom sub_mm) ++ elements (⋃ (vars_of <$> (map_to_list sub_mm).*2)))) as avoid.
    assert (Havoid : ((elements (dom sub_mm) ++ elements (⋃ (vars_of <$> (map_to_list sub_mm).*2)))) ⊆ avoid) by ltac1:(set_solver).
    clear Heqavoid.

    subst rn.
    revert avoid Havoid.
    induction φ; intros avoid Havoid.
    {
        simpl in *.
        destruct a.
        {
            simpl in *.
            rewrite subs_app_builtin.
            reflexivity.
        }
        {
            remember (map_to_list sub_mm) as sub_mm'.
            
            assert (Hlen: (length (elements (dom (@list_to_map variable (TermOver BuiltinOrVar) (gmap variable (TermOver BuiltinOrVar)) _ _ sub_mm')))) = length sub_mm').
            {
                rewrite dom_list_to_map.
                rewrite elements_list_to_set.
                rewrite length_fmap.
                reflexivity.
                subst sub_mm'.
                unfold SubP in *.
                apply NoDup_fst_map_to_list.
            }
            
            assert (Hsub_mm'_nodup : NoDup (fst <$> sub_mm')).
            {
                subst sub_mm'.
                unfold SubP in *.
                apply NoDup_fst_map_to_list.
            }
            ltac1:(apply (f_equal (@list_to_map variable (TermOver BuiltinOrVar) (gmap variable (TermOver BuiltinOrVar)) _ _)) in Heqsub_mm').
            ltac1:(rewrite list_to_map_to_list in Heqsub_mm').
            subst sub_mm.
            ltac1:(rewrite Hlen).
            clear Hlen.
            revert avoid Havoid.
            induction sub_mm'; intros avoid Havoid.
            {
                simpl in *.
                ltac1:(rewrite lookup_empty dom_empty_L elements_empty).
                simpl.
                reflexivity.
            }
            {
                simpl.
                destruct a as [y t].
                
                simpl in *.
                destruct (decide (x = y)).
                {
                    subst y.
                    ltac1:(rewrite lookup_insert).
                    (* ltac1:(case_match).
                    {

                    }
                    {

                    } *)
                    (* Unset Printing Notations. *)
                    (* ltac1:(rewrite subs_app_app). *)
                    destruct (list_to_map
                        (zip (elements (dom (<[x:=t]> (list_to_map sub_mm'))))
                        (fresh avoid
                        :: fresh_var_seq (fresh avoid :: avoid) (length sub_mm')))
                        !! x
                    ) eqn:Heq1.
                    {
                        fold (@fmap list list_fmap) in *.
                        (* rewrite decide_True>[|reflexivity]. *)
                        (* rewrite subs_app_app. *)
                        ltac1:(ospecialize (IHsub_mm' _)).
                        {
                            inversion Hsub_mm'_nodup; subst.
                            assumption.
                        }
                        specialize (IHsub_mm' (avoid)).
                        ltac1:(ospecialize (IHsub_mm' _)).
                        {
                            ltac1:(rewrite dom_list_to_map).
                            ltac1:(rewrite dom_insert_L in Havoid).
                            ltac1:(rewrite dom_list_to_map in Havoid).
                            ltac1:(set_solver).
                        }
                        rewrite subs_app_app.
                        rewrite subs_app_app in IHsub_mm'.
                        destruct (decide (v = x)).
                        {
                            subst v.
                            simpl in *.
                            (* This is a contradiction, as according to Havoid we have [x ∈ avoid],
                               and according to Heq1, [x] is one of the freshly generated (thus non-avoid) variables.
                            *)
                        }
                        {
                            ltac1:(rewrite dom_insert_L).
                            ltac1:(rewrite dom_list_to_map_L).
                            destruct (((@list_to_map variable variable (gmap variable variable) _ _
                                (zip (elements ({[x]} ∪ ((list_to_set sub_mm'.*1):(gset variable))))
                                (fresh avoid
                                :: fresh_var_seq (fresh avoid :: avoid)
                                (length sub_mm')))):(gmap variable variable)) !! ((x)))
                                eqn:Heqxx.
                            {
                                (*  *)
                                rewrite subs_app_nodup_2 with (y := v0).
                                {
                                    simpl.
                                }
                                {

                                    (* rewrite <- list_fmap_compose.
                                    lazy_match! goal with
                                    | [|- NoDup ( ?f <$> _)] => assert (Hfst : $f = fst)
                                    end.
                                    {
                                        unfold compose.
                                        apply functional_extensionality.
                                        intros [x' p'].
                                        simpl.
                                        ltac1:(case_match); simpl in *.
                                    } *)
                                    rewrite <- list_fmap_compose.
                                    lazy_match! goal with
                                    | [|- NoDup ( ?f <$> _)] => assert (Hfst : $f = (fun kv =>
                                        let found := list_find (eq (kv.1)) ((elements ({[x]} ∪ ((list_to_set sub_mm'.*1):(gset variable))))) in
                                        match found with
                                        | None => kv.1
                                        | Some (n, _) => fresh_nth avoid n
                                        end
                                    ))
                                    end.
                                    {
                                        apply functional_extensionality.
                                        intros [x' p'].
                                        simpl.
                                        clear - Hsub_mm'_nodup.
                                        remember (elements ({[x]} ∪ ((list_to_set sub_mm'.*1):(gset variable)))) as els.
                                        assert (Hels: {[x]} ∪ (list_to_set sub_mm'.*1 : gset variable) ≡ (list_to_set els)).
                                        {
                                            rewrite Heqels.
                                            ltac1:(set_solver).
                                        }
                                        assert (Hne: NoDup els).
                                        {
                                            subst els.
                                            apply NoDup_elements.
                                        }
                                        (* clear Heqels. *)

                                        (* clear Hsub_mm'_nodup. *)

                                        (* < NEW TEST> *)
                                        ltac1:(repeat case_match; simpl in *; simplify_eq/=).
                                        {
                                            apply list_find_Some in H0.
                                            apply elem_of_list_to_map_2 in H.
                                            rewrite elem_of_list_lookup in H.
                                            destruct H as [n' Hn'].
                                            destruct H0 as [H1 [H2 H3]].
                                            apply lookup_of_zip_both_2 in Hn'.
                                            destruct Hn' as [H1n' H2n'].
                                            subst v0.
                                            assert (n' = n).
                                            {
                                                clear - Hne H1n' H1.
                                                symmetry.
                                                eapply NoDup_lookup.
                                                {
                                                    apply Hne.
                                                }
                                                {
                                                    apply H1.
                                                }
                                                {
                                                    apply H1n'.
                                                }
                                            }
                                            subst n'.
                                            assert (Htmp: fresh_var_seq avoid (S (length sub_mm')) !! n = Some v).
                                            {
                                                apply H2n'.
                                            }
                                            rewrite <- fresh_nth_iff in Htmp.
                                            {
                                                symmetry.
                                                exact Htmp.
                                            }
                                            {
                                                apply lookup_lt_Some in Htmp.
                                                rewrite length_fresh_var_seq in Htmp.
                                                ltac1:(lia).
                                            }
                                        }
                                        {
                                            apply elem_of_list_to_map_2 in H.
                                            rewrite elem_of_list_lookup in H.
                                            destruct H as [n' Hn'].
                                            apply lookup_of_zip_both_2 in Hn'.
                                            destruct Hn' as [H1n' H2n'].
                                            apply list_find_None in H0.
                                            rewrite Forall_forall in H0.
                                            specialize (H0 x').
                                            rewrite elem_of_list_lookup in H0.
                                            specialize (H0 (ex_intro _ _ H1n')).
                                            ltac1:(contradiction H0).
                                            reflexivity.
                                        }
                                        {
                                            apply list_find_Some in H0.
                                            destruct H0 as [H1 [H2 H3]].
                                            subst v.
                                            apply not_elem_of_list_to_map_2 in H.
                                            rewrite elem_of_list_lookup in H.
                                            ltac1:(contradiction H).
                                            exists n.
                                            rewrite fst_zip.
                                            exact H1.
                                            simpl.
                                            rewrite length_fresh_var_seq.
                                            apply lookup_lt_Some in H1.
                                            (* Search elements union. *)
                                            rewrite elements_union_singleton.
                                            simpl.
                                            rewrite elements_list_to_set.
                                            rewrite length_fmap.
                                            ltac1:(lia).
                                            rewrite NoDup_cons in Hsub_mm'_nodup.
                                            exact (proj2 Hsub_mm'_nodup).
                                            {
                                                rewrite elem_of_list_to_set.
                                                rewrite NoDup_cons in Hsub_mm'_nodup.
                                                exact (proj1 Hsub_mm'_nodup).
                                            }
                                        }
                                        { reflexivity. }
                                        (* </NEW TEST> *)
                                    }
                                    unfold compose.
                                    Search fmap.
                                    (* assert(Htmp := NoDup_1_renaming_for sub_mm'). *)
                                    clear.
                                    revert x avoid.
                                    induction sub_mm'; intros x avoid.
                                    {
                                        simpl.
                                        apply NoDup_nil.
                                        exact I.
                                    }
                                    {
                                        rewrite fmap_cons.
                                        rewrite fmap_cons.
                                        rewrite NoDup_cons.
                                        split.
                                        {

                                        }
                                        {
                                            simpl in *.
                                            (* ltac1:(replace (length (a::sub_mm')) with (S (length sub_mm')) by reflexivity). *)
                                            (* rewrite fresh_var_seq *)
                                            apply IHsub_mm'.
                                        }
                                    }
                                    apply NoDup_1_renaming_for.
                                    Search NoDup fmap.
                                }
                                {

                                }
                                {

                                }
                            }
                            {
                                (* Not found *)
                            }
                            (* In the absence of duplicated keys and variable-only values, subs_app behaves nicely and just returns the one value *)
                            erewrite subs_app_nodup_2.
                        }
                        
                        lazy_match! goal with
                        | [ |- subs_app _ ?p = _] =>
                            assert (exists z, $p = t_over (bov_variable z) /\ z ∈ (fresh avoid :: fresh_var_seq (fresh avoid :: avoid) (length sub_mm')))
                        end.
                        {

                            clear - Heq1 Hsub_mm'_nodup.
                            revert v avoid Heq1 Hsub_mm'_nodup.
                            induction sub_mm'; intros v avoid Heq1 Hsub_mm'_nodup.
                            {
                                simpl in *.
                                exists v.
                                (* split>[reflexivity|]. *)
                                ltac1:(rewrite dom_insert_L in Heq1).
                                ltac1:(rewrite union_empty_r_L in Heq1).
                                rewrite elements_singleton in Heq1.

                                ltac1:(rewrite - elem_of_list_to_map in Heq1).
                                {
                                    constructor.
                                    intros HContra.
                                    rewrite elem_of_nil in HContra.
                                    exact HContra.
                                    constructor.
                                }
                                simpl in Heq1.
                                rewrite elem_of_cons.
                                rewrite elem_of_cons in Heq1.
                                destruct (decide (v = x)); simpl in *.
                                {
                                    subst; simpl in *.
                                    destruct Heq1 as [Heq1|Heq1].
                                    {
                                        ltac1:(simplify_eq/=).
                                    }
                                }
                                {

                                }
                                ltac1:(set_solver).
                            }
                            {
                                simpl in *.


                                (* I have to find a different variable than [v] *)
                                ltac1:(setoid_rewrite <- elem_of_list_to_map in IHsub_mm').
                                ltac1:(setoid_rewrite elem_of_list_lookup in IHsub_mm').
                                ltac1:(rewrite dom_insert_L in IHsub_mm').
                                assert(Htmp: ∃ i' v', zip (elements ({[x]} ∪ dom (@list_to_map variable (TermOver BuiltinOrVar) (gmap (variable) (TermOver BuiltinOrVar)) _ _ sub_mm')))
                                        (fresh avoid
                                                :: fresh_var_seq (fresh avoid :: avoid)
                                                (length sub_mm'))
                                                !! i' =
                                        Some (x, v')).
                                {
                                    remember (list_find (eq x) (elements ({[x]} ∪ dom (@list_to_map variable (TermOver BuiltinOrVar) (gmap (variable) (TermOver BuiltinOrVar)) _ _ sub_mm')))) as found.
                                    destruct found.
                                    {
                                        symmetry in Heqfound.
                                        destruct p as [j v'].
                                        rewrite list_find_Some in Heqfound.
                                        destruct Heqfound as [HH1 [HH2 HH3]].
                                        subst v'.
                                        destruct ((fresh avoid :: fresh_var_seq (fresh avoid :: avoid) (length sub_mm')) !! j) eqn:Heq2.
                                        {
                                            exists j, v0.
                                            apply lookup_of_zip_both; assumption.
                                        }
                                        {
                                            ltac1:(exfalso).
                                            apply lookup_lt_Some in HH1.
                                            rewrite elements_union_singleton in HH1.
                                            simpl in HH1.
                                            apply lookup_ge_None in Heq2.
                                            simpl in Heq2.
                                            rewrite length_fresh_var_seq in Heq2.
                                            rewrite dom_list_to_map in HH1.
                                            rewrite elements_list_to_set in HH1.
                                            {
                                                rewrite length_fmap in HH1.
                                                ltac1:(lia).
                                            }
                                            {
                                                inversion Hsub_mm'_nodup;
                                                subst;
                                                clear Hsub_mm'_nodup.
                                                inversion H2; subst; clear H2.
                                                assumption.
                                            }
                                            rewrite elem_of_dom.
                                            intros [p Hp].
                                            ltac1:(rewrite - elem_of_list_to_map in Hp).
                                            {
                                                inversion Hsub_mm'_nodup;
                                                subst;
                                                clear Hsub_mm'_nodup.
                                                inversion H2; subst; clear H2.
                                                assumption.
                                            }
                                            {
                                                inversion Hsub_mm'_nodup;
                                                subst;
                                                clear Hsub_mm'_nodup.
                                                inversion H2; subst; clear H2.
                                                apply H1. clear H1.
                                                rewrite elem_of_cons.
                                                right.
                                                rewrite elem_of_list_fmap.
                                                exists (x, p).
                                                split>[reflexivity|].
                                                exact Hp.
                                            }
                                        }
                                    }
                                    {
                                        ltac1:(exfalso).
                                        symmetry in Heqfound.
                                        rewrite list_find_None in Heqfound.
                                        rewrite Forall_forall in Heqfound.
                                        specialize (Heqfound x ltac:(set_solver)).
                                        apply Heqfound.
                                        reflexivity.
                                    }
                                }
                                destruct Htmp as [i' [v' Htmp]].
                                specialize (IHsub_mm' v' avoid).
                                ltac1:(ospecialize (IHsub_mm' _ _)).
                                {
                                    exists i'.
                                    apply Htmp.
                                }
                                {
                                    rewrite NoDup_cons.
                                    rewrite NoDup_cons in Hsub_mm'_nodup.
                                    rewrite NoDup_cons in Hsub_mm'_nodup.
                                    ltac1:(set_solver).
                                }
                                destruct IHsub_mm' as [z [H1z H2z]].
                                exists z.
                                fold (@fmap list list_fmap) in *.
                                destruct a as [x' p'].
                                destruct H2z as [i Hi].
                                simpl in *.

                                remember (list_find (eq x') ((elements (dom (<[x:=t]> (<[x':=p']> ((list_to_map sub_mm'):(gmap variable (TermOver BuiltinOrVar))))))))) as Found.
                                destruct Found eqn:Hfound.
                                {
                                    destruct p as [i'' Hi''].
                                    symmetry in HeqFound.
                                    apply list_find_Some in HeqFound.
                                    destruct HeqFound as [H1 [H2 H3]].
                                    destruct i'' as [|i''].
                                    {
                                        simpl in *.
                                        subst Hi''.
                                        ltac1:(rewrite -> elem_of_list_to_map_1 with (x := (fresh avoid))).
                                        {
                                            split.
                                            {
                                                destruct (decide (x' = v)).
                                                {
                                                    subst v.
                                                    simpl in *.
                                                }
                                                {

                                                }
                                            }
                                            {
                                                apply elem_of_list_lookup_2 in Hi.
                                                clear - Hi.
                                                assert (Htmp := fresh_var_seq_mono (fresh avoid::avoid) (length sub_mm')).
                                                ltac1:(set_solver).
                                            }

                                        }
                                        {
                                            rewrite fst_zip.
                                            apply NoDup_elements.
                                            simpl.
                                            rewrite length_fresh_var_seq.
                                            ltac1:(rewrite dom_insert_L).
                                            ltac1:(rewrite dom_insert_L).
                                            rewrite NoDup_cons in Hsub_mm'_nodup.
                                            rewrite NoDup_cons in Hsub_mm'_nodup.
                                            destruct Hsub_mm'_nodup as [ND1 [ND2 ND3]].
                                            rewrite elements_disj_union.
                                            {
                                                rewrite elements_disj_union.
                                                {
                                                    rewrite length_app.
                                                    rewrite length_app.
                                                    rewrite elements_singleton.
                                                    rewrite elements_singleton.
                                                    simpl.
                                                    rewrite dom_list_to_map.
                                                    rewrite elements_list_to_set.
                                                    rewrite length_fmap.
                                                    ltac1:(lia).
                                                    ltac1:(naive_solver).
                                                }
                                                {
                                                    ltac1:(rewrite disjoint_singleton_l).
                                                    rewrite elem_of_dom.
                                                    intros [zz Hzz].
                                                    apply ND2.
                                                    clear ND2.
                                                    rewrite elem_of_list_fmap.
                                                    exists (x', zz).
                                                    simpl.
                                                    split>[reflexivity|].
                                                    ltac1:(rewrite - elem_of_list_to_map in Hzz).
                                                    {
                                                        assumption.
                                                    }
                                                    {
                                                        exact Hzz.
                                                    }
                                                }
                                            }
                                            {
                                                rewrite elem_of_cons in ND1.
                                                rewrite elem_of_list_fmap in ND1.
                                                rewrite elem_of_list_fmap in ND2.
                                                rewrite dom_list_to_map.
                                                rewrite disjoint_singleton_l.
                                                intros HContra.
                                                rewrite elem_of_union in HContra.
                                                destruct HContra as [HContra|HContra].
                                                {
                                                    rewrite elem_of_singleton in HContra.
                                                    subst x'.
                                                    apply ND1.
                                                    left.
                                                    reflexivity.
                                                }
                                                {
                                                    rewrite elem_of_list_to_set in HContra.
                                                    rewrite elem_of_list_fmap in HContra.
                                                    destruct HContra as [[u' w'] [Huw1 Huw2]].
                                                    subst.
                                                    simpl in *.
                                                    apply ND1.
                                                    right.
                                                    exists (u', w').
                                                    split>[reflexivity|].
                                                    exact Huw2.
                                                }
                                            }
                                        }
                                        {
                                            rewrite elem_of_list_lookup.
                                            exists 0.
                                            apply lookup_of_zip_both.
                                            {
                                                simpl.
                                                apply H1.
                                            }
                                            {
                                                simpl.
                                                reflexivity.
                                            }
                                        }
                                    }
                                    {
                                        simpl in *.
                                    }
                                    
                                    (* erewrite lookup_of_zip_both. *)
                                    (* exists i''. *)
                                    
                                }
                                {
                                    ltac1:(exfalso).
                                    symmetry in HeqFound.
                                    apply list_find_None in HeqFound.
                                    rewrite Forall_forall in HeqFound.
                                    specialize (HeqFound x').
                                    apply HeqFound. clear HeqFound.
                                    clear.
                                    rewrite elem_of_elements.
                                    rewrite elem_of_dom.
                                    destruct (decide (x' = x)).
                                    {
                                        subst x'.
                                        exists t.
                                        rewrite lookup_insert.
                                        reflexivity.
                                    }
                                    {
                                        exists (p').
                                        rewrite lookup_insert_ne.
                                        {
                                            rewrite lookup_insert.
                                            reflexivity.
                                        }
                                        { ltac1:(congruence). }
                                    }
                                    reflexivity.
                                }

                                destruct i.
                                {
                                    simpl in Hi.
                                    apply (inj Some) in Hi.
                                    subst z.
                                    ltac1:(erewrite elem_of_list_to_map_1).
                                    {

                                    }
                                    {

                                    }
                                    {
                                        rewrite elem_of_list_lookup.
                                        
                                    }
                                }
                                {
                                    simpl in Hi.
                                }
                                
                                Search list_to_map lookup.
                                Check elem_of_list_to_map.
                                ltac1:(rewrite - elem_of_list_to_map).
                                ltac1:(case_match).
                                {
                                    Search a.
                                }
                                {

                                }


                                specialize (IHsub_mm' v (avoid)).
                                simpl in *.
                                ltac1:(ospecialize (IHsub_mm' _)).
                                {
                                    ltac1:(rewrite - elem_of_list_to_map in Heq1).
                                    {
                                        repeat (rewrite NoDup_cons in Hsub_mm'_nodup).
                                        destruct Hsub_mm'_nodup as [HH1 [HH2 HH3]].
                                        rewrite fst_zip.
                                        apply NoDup_elements.
                                        simpl.
                                        rewrite length_fresh_var_seq.
                                        ltac1:(rewrite dom_insert_L).
                                        ltac1:(rewrite dom_insert_L).
                                        rewrite elements_union_singleton.
                                        {
                                            rewrite elements_union_singleton.
                                            {
                                                simpl.
                                                ltac1:(rewrite dom_list_to_map).
                                                rewrite elements_list_to_set.
                                                rewrite length_fmap.
                                                ltac1:(lia).
                                                assumption.
                                            }
                                            {
                                                fold (@fmap list list_fmap) in *.
                                                intros HContra.
                                                apply HH2. clear HH2.
                                                rewrite elem_of_dom in HContra.
                                                destruct HContra as [b Hb].
                                                rewrite elem_of_list_fmap.
                                                destruct a as [a1 a2].
                                                simpl in *.
                                                exists (a1, b).
                                                split>[reflexivity|].
                                                ltac1:(rewrite - elem_of_list_to_map in Hb).
                                                { exact HH3. }
                                                { exact Hb. }
                                            }    
                                        }
                                        {
                                            intros HContra.
                                            rewrite elem_of_union in HContra.
                                            destruct HContra as [HContra|HContra].
                                            {
                                                rewrite elem_of_singleton in HContra.
                                                subst x.
                                                fold (@fmap list list_fmap) in *.
                                                apply HH1.
                                                clear HH1.
                                                rewrite elem_of_cons.
                                                left.
                                                reflexivity.
                                            }
                                            {
                                                fold (@fmap list list_fmap) in *.
                                                rewrite elem_of_dom in HContra.
                                                destruct HContra as [b Hb].
                                                ltac1:(rewrite - elem_of_list_to_map in Hb).
                                                { exact HH3. }
                                                apply HH1.
                                                rewrite elem_of_cons.
                                                clear HH1.
                                                right. 
                                                rewrite elem_of_list_fmap.
                                                exists (x,b).
                                                split>[reflexivity|].
                                                exact Hb.
                                            }
                                        }
                                    }
                                    ltac1:(rewrite - elem_of_list_to_map).
                                    {
                                        simpl in *.
                                        repeat (rewrite NoDup_cons in Hsub_mm'_nodup).
                                        destruct Hsub_mm'_nodup as [HH1 [HH2 HH3]].
                                        rewrite fst_zip.
                                        ltac1:(rewrite dom_insert_L).
                                        ltac1:(rewrite elements_union_singleton).
                                        {
                                            fold (@fmap list list_fmap) in *.
                                            intros HContra.
                                            apply HH1.
                                            clear HH1.
                                            rewrite elem_of_cons.
                                            right.
                                            rewrite elem_of_list_fmap.
                                            rewrite elem_of_dom in HContra.
                                            destruct HContra as [p Hp].
                                            exists (x, p).
                                            split>[reflexivity|].
                                            ltac1:(rewrite - elem_of_list_to_map in Hp).
                                            { assumption. }
                                            { exact Hp. }
                                        }
                                        {
                                            rewrite NoDup_cons.
                                            fold (@fmap list list_fmap) in *.
                                            rewrite elem_of_elements.
                                            rewrite elem_of_dom.
                                            split.
                                            {
                                                intros HContra.
                                                destruct HContra as [p Hp].
                                                ltac1:(rewrite - elem_of_list_to_map in Hp).
                                                { assumption. }
                                                apply HH1. clear HH1.
                                                rewrite elem_of_cons.
                                                right.
                                                rewrite elem_of_list_fmap.
                                                exists (x, p).
                                                split>[reflexivity|].
                                                exact Hp.
                                            }
                                            {
                                                apply NoDup_elements.
                                            }
                                        }
                                        {
                                            simpl.
                                            ltac1:(rewrite dom_insert).
                                            rewrite elements_union_singleton.
                                            simpl.
                                            rewrite length_fresh_var_seq.
                                            ltac1:(rewrite dom_list_to_map_L).
                                            ltac1:(rewrite elements_list_to_set).
                                            assumption.
                                            rewrite length_fmap.
                                            ltac1:(lia).
                                            intros HContra.
                                            rewrite elem_of_dom in HContra.
                                            destruct HContra as [p Hp].
                                            ltac1:(rewrite - elem_of_list_to_map in Hp).
                                            assumption.
                                            fold (@fmap list list_fmap) in *.
                                            apply HH1.
                                            clear HH1.
                                            rewrite elem_of_cons.
                                            right.
                                            rewrite elem_of_list_fmap.
                                            exists (x,p).
                                            simpl.
                                            split>[reflexivity|].
                                            exact Hp.
                                        }
                                    }
                                    rewrite elem_of_list_lookup.
                                    rewrite elem_of_list_lookup in Heq1.
                                    destruct Heq1 as [i Hi].
                                    Search elem_of zip(* HERE *).
                                }
                            }
                        }
                        assert(Htmp :
                        
                        ).
                        rewrite IHsub_mm'.
                        
                    }
                    
                }
            }
        }
    }
Qed.
