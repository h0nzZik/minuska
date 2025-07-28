From Minuska Require Import
    prelude
    spec
    termoverbov_subst
    basic_properties
.


Lemma subst_notin
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of_to_l2r φ ->
    TermOverBoV_subst φ h ψ = φ
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        {
            intros _. reflexivity.
        }
        {
            destruct (decide (h = x)); simpl.
            {
                subst. intros HContra. ltac1:(exfalso). apply HContra.
                constructor.
            }
            {
                intros _. reflexivity.
            }
        }
    }
    {
        intros H2.
        f_equal.
        induction l; simpl.
        {
            reflexivity.
        }
        {
            apply Forall_cons in H.
            destruct H as [HH1 HH2].
            simpl in *.
            specialize (IHl HH2).
            rewrite elem_of_app in H2.
            apply Decidable.not_or in H2.
            destruct H2 as [H21 H22].
            specialize (IHl H22). clear H22.
            specialize (HH1 H21).
            rewrite HH1.
            rewrite IHl.
            reflexivity.
        }
    }
Qed.

Lemma subst_notin2 {Σ : StaticModel}
     : ∀ (h : variable) (φ ψ : TermOver BuiltinOrVar),
         h ∉ vars_of φ → TermOverBoV_subst φ h ψ = φ
.
Proof.
  intros h φ ψ. revert h ψ.
  induction φ; intros h ψ HH; simpl in * .
  {
    unfold vars_of in HH; simpl in HH.
    unfold vars_of in HH; simpl in HH.
    unfold vars_of_BoV in HH; simpl in HH.
    destruct a; simpl in *.
    { reflexivity. }
    {
      rewrite elem_of_singleton in HH.
      destruct (decide (h = x)) > [ltac1:(contradiction)|].
      reflexivity.
    }
  }
  {
    unfold vars_of in HH; simpl in HH.
    f_equal.
    revert H HH.
    induction l; intros H HH.
    {
      simpl. reflexivity.
    }
    {
      rewrite Forall_cons in H.
      destruct H as [H1 H2].
      specialize (IHl H2). clear H2.
      simpl in HH.
      simpl.
      rewrite elem_of_union in HH.
      apply Decidable.not_or in HH.
      destruct HH as [HH1 HH2].
      simpl in *.
      rewrite IHl.
      {
        rewrite H1.
        { reflexivity. }
        { exact HH1. }
      }
      {
        exact HH2.
      }
    }
  }
Qed.


Lemma size_subst_1
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    TermOver_size φ <= TermOver_size (TermOverBoV_subst φ h ψ)
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        { ltac1:(lia). }
        {
            destruct (decide (h = x)); simpl.
            {
                destruct ψ; simpl; ltac1:(lia).
            }
            {
                ltac1:(lia).
            }
        }
    }
    {
        revert H.
        induction l; intros H; simpl in *.
        { ltac1:(lia). }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            ltac1:(lia).
        }
    }
Qed.

Lemma size_subst_2
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∈ vars_of_to_l2r φ ->
    TermOver_size ψ <= TermOver_size (TermOverBoV_subst φ h ψ)
.
Proof.
    revert h ψ.
    induction φ; intros h ψ Hin; simpl in *.
    {
        destruct a.
        {
            inversion Hin.
        }
        {
            inversion Hin; subst; clear Hin.
            {
                destruct (decide (x = x))>[|ltac1:(contradiction)].
                ltac1:(lia).
            }
            {
                inversion H1.
            }
        }
    }
    {
        revert H Hin.
        induction l; intros H Hin; simpl in *.
        {
            inversion Hin.
        }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            destruct (decide (h ∈ vars_of_to_l2r a )) as [Hin'|Hnotin'].
            {
                specialize (H1 h ψ Hin'). clear Hin.
                ltac1:(lia).
            }
            {
                specialize (IHl ltac:(set_solver)).
                ltac1:(lia).
            }
        }
    }
Qed.


Lemma TermOverBoV_subst_once_size
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of ψ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    TermOver_size (TermOverBoV_subst φ h ψ) = Nat.pred (TermOver_size φ + TermOver_size ψ)
.
Proof.
    induction φ; simpl; intros Hnotinψ Hexactlyonce.
    {
        destruct a.
        {
            simpl in *. ltac1:(lia).
        }
        {
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h = x)).
            {
                simpl in *. reflexivity.
            }
            {
                simpl in *. ltac1:(lia).
            }
        }
    }
    {
        simpl in *.
        rewrite sum_list_with_compose.
        unfold compose.
        do 2 (rewrite sum_list_with_S).
        do 2 (rewrite length_map).
        do 2 (rewrite sum_list_fmap).
        rewrite length_fmap.

        assert (Hconcat: h ∈ concat (map vars_of_to_l2r l)).
        {
            clear -Hexactlyonce.
            induction l; simpl in *.
            { ltac1:(lia). }
            {
                rewrite filter_app in Hexactlyonce.
                rewrite length_app in Hexactlyonce.
                destruct (decide (h ∈ vars_of_to_l2r a)).
                {
                    rewrite elem_of_app. left. assumption.
                }
                {
                    ltac1:(ospecialize (IHl _)).
                    {
                        ltac1:(cut(length (filter (eq h) (vars_of_to_l2r a)) = 0)).
                        {
                            intros HH. ltac1:(lia).
                        }
                        rewrite length_zero_iff_nil.
                        remember (vars_of_to_l2r a) as l'.
                        clear Heql'.
                        clear -n.
                        induction l'.
                        {
                            reflexivity.
                        }
                        {
                            rewrite elem_of_cons in n.
                            apply Decidable.not_or in n.
                            destruct n as [H1 H2].
                            specialize (IHl' H2).
                            rewrite filter_cons.
                            destruct (decide (h = a)).
                            {
                                subst. ltac1:(contradiction).
                            }
                            {
                                apply IHl'.
                            }
                        }
                    }
                    {
                        rewrite elem_of_app. right. apply IHl.
                    }
                }
            }
        }
        rewrite elem_of_list_In in Hconcat.
        rewrite in_concat in Hconcat.
        destruct Hconcat as [x [H1x H2x]].
        rewrite in_map_iff in H1x.
        destruct H1x as [x0 [H1x0 H2x0]].
        subst.

        rewrite <- elem_of_list_In in H2x.
        rewrite elem_of_list_lookup in H2x.
        destruct H2x as [i Hi].

        rewrite <- elem_of_list_In in H2x0.
        assert (H2x0' := H2x0).
        rewrite elem_of_list_lookup in H2x0.
        destruct H2x0 as [j Hj].
        apply take_drop_middle in Hj.
        rewrite <- Hj.
        rewrite length_app.
        rewrite sum_list_with_app.
        rewrite map_app.
        rewrite sum_list_with_app.
        simpl.

        rewrite <- Hj in Hexactlyonce.
        rewrite map_app in Hexactlyonce. simpl in Hexactlyonce.
        rewrite concat_app in Hexactlyonce. simpl in Hexactlyonce.
        do 2 (rewrite filter_app in Hexactlyonce).
        do 2 (rewrite length_app in Hexactlyonce).
        simpl in Hexactlyonce.
        
        assert(Hnotintake: forall x2, x2 ∈ take j l -> h ∉ vars_of_to_l2r x2).
        {
            intros x2 Hx2.
            intros HContra.
            
            assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (take j l))))).
            {
                rewrite elem_of_list_lookup in Hx2.
                destruct Hx2 as [i0 Hx2].
                
                assert (Heq' := Hx2).
                apply take_drop_middle in Heq'.
                rewrite <- Heq'.
                rewrite map_app.
                rewrite concat_app.
                rewrite filter_app.
                simpl.
                rewrite filter_app.
                rewrite length_app.
                rewrite length_app.
                rewrite elem_of_list_lookup in HContra.
                destruct HContra as [k Hk].
                apply take_drop_middle in Hk.
                rewrite <- Hk.
                rewrite filter_app.
                rewrite length_app.
                rewrite filter_cons.
                destruct (decide (h = h))>[|ltac1:(contradiction)].
                simpl.
                ltac1:(lia).
            }
            apply take_drop_middle in Hi.
            rewrite <- Hi in Hexactlyonce.
            rewrite filter_app in Hexactlyonce.
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h=h))>[|ltac1:(contradiction)].
            rewrite length_app in Hexactlyonce.
            simpl in Hexactlyonce.
            unfold TermOver in *.
            ltac1:(lia).
        }

        assert(Hnotindrop: forall x2, x2 ∈ drop (S j) l -> h ∉ vars_of_to_l2r x2).
        {
            intros x2 Hx2.
            intros HContra.
            simpl in Hexactlyonce.
            assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (drop (S j) l))))).
            {
                rewrite elem_of_list_lookup in Hx2.
                destruct Hx2 as [i0 Hx2].
                
                assert (Heq' := Hx2).
                apply take_drop_middle in Heq'.
                rewrite <- Heq'.
                rewrite map_app.
                rewrite concat_app.
                rewrite filter_app.
                simpl.
                rewrite filter_app.
                rewrite length_app.
                rewrite length_app.
                rewrite elem_of_list_lookup in HContra.
                destruct HContra as [k Hk].
                apply take_drop_middle in Hk.
                rewrite <- Hk.
                rewrite filter_app.
                rewrite length_app.
                rewrite filter_cons.
                destruct (decide (h = h))>[|ltac1:(contradiction)].
                simpl.
                ltac1:(lia).
            }
            apply take_drop_middle in Hi.
            rewrite <- Hi in Hexactlyonce.
            rewrite filter_app in Hexactlyonce.
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h=h))>[|ltac1:(contradiction)].
            rewrite length_app in Hexactlyonce.
            simpl in Hexactlyonce.
            unfold TermOver in *.
            ltac1:(lia).
        }

        assert (HH1: (sum_list_with TermOver_size
                (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ)
                (take j l))  )
                = sum_list_with TermOver_size (take j l) ).
        {
            apply sum_list_with_eq_pairwise.
            {
                rewrite length_map.
                reflexivity.
            }
            {
                intros i0 x1 x2 Hx1 Hx2.
                ltac1:(replace map with (@fmap _ list_fmap) in Hx1 by reflexivity).
                rewrite list_lookup_fmap in Hx1.
                unfold TermOver in *.
                rewrite Hx2 in Hx1. simpl in Hx1. inversion Hx1; subst; clear Hx1.
                rewrite subst_notin.
                {
                    reflexivity.
                }
                {
                    intros HContra.
                    specialize (Hnotintake x2).
                    ltac1:(ospecialize (Hnotintake _)).
                    {
                        rewrite elem_of_list_lookup.
                        exists i0. exact Hx2.
                    }
                    apply Hnotintake. apply HContra.
                }
            }
        }

        assert (HH2: (sum_list_with TermOver_size
                (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ)
                (drop (S j) l))  )
                = sum_list_with TermOver_size (drop (S j) l) ).
        {
            apply sum_list_with_eq_pairwise.
            {
                rewrite length_map.
                reflexivity.
            }
            {
                intros i0 x1 x2 Hx1 Hx2.
                unfold TermOver in *.
                ltac1:(replace map with (@fmap _ list_fmap) in Hx1 by reflexivity).
                rewrite list_lookup_fmap in Hx1.
                rewrite Hx2 in Hx1. simpl in Hx1. inversion Hx1; subst; clear Hx1.
                rewrite subst_notin.
                {
                    reflexivity.
                }
                {

                    intros HContra.
                    specialize (Hnotindrop x2).
                    ltac1:(ospecialize (Hnotindrop _)).
                    {
                        rewrite elem_of_list_lookup.
                        exists i0. exact Hx2.
                    }
                    apply Hnotindrop. apply HContra.
                }
            }
        }
        unfold TermOver in *.
        rewrite HH1. clear HH1.
        rewrite HH2. clear HH2.
        remember (sum_list_with TermOver_size (take j l) ) as N1.
        remember (sum_list_with TermOver_size (drop (S j) l) ) as N2.
        rewrite length_take.
        rewrite length_drop.

        rewrite Forall_forall in H.
        specialize (H x0 H2x0' Hnotinψ).

        assert (Hnotintake': length (filter (eq h) (concat (map vars_of_to_l2r (take j l)))) = 0).
        {
            rewrite length_zero_iff_nil.
            apply list_filter_Forall_not.
            rewrite Forall_forall.
            intros x Hx HContra.
            subst x.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [x [H1x H2x]].
            rewrite in_map_iff in H1x.
            destruct H1x as [x1 [H1x1 H2x1]].
            rewrite <- elem_of_list_In in H2x.
            subst x.
            rewrite <- elem_of_list_In in H2x1.
            specialize (Hnotintake _ H2x1).
            apply Hnotintake. apply H2x.
        }

        assert (Hnotindrop': length (filter (eq h) (concat (map vars_of_to_l2r (drop (S j) l)))) = 0).
        {
            rewrite length_zero_iff_nil.
            apply list_filter_Forall_not.
            rewrite Forall_forall.
            intros x Hx HContra.
            subst x.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [x [H1x H2x]].
            rewrite in_map_iff in H1x.
            destruct H1x as [x1 [H1x1 H2x1]].
            rewrite <- elem_of_list_In in H2x.
            subst x.
            rewrite <- elem_of_list_In in H2x1.
            specialize (Hnotindrop _ H2x1).
            apply Hnotindrop. apply H2x.
        }
        unfold TermOver in *.
        specialize (H ltac:(lia)).
        rewrite H.
        assert (Htmp1 := TermOver_size_not_zero x0).
        unfold TermOver in *.
        rewrite length_app.
        simpl.
        rewrite length_drop.
        rewrite length_take.
        ltac1:(lia).
    }
Qed.


Lemma vars_of__TermOverBoV_subst__varless
    {Σ : StaticModel} c x v
    :
    vars_of v = ∅ ->
    vars_of (TermOverBoV_subst c x v) = vars_of c ∖ {[x]}
.
Proof.
    induction c; simpl in *; intros HH.
    {
        destruct a.
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            destruct (decide (x = x0)).
            {
                subst.
                ltac1:(set_solver).
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                ltac1:(set_solver).
            }
        }
    }
    {
        unfold TermOver in *.
        rewrite vars_of_t_term.
        rewrite vars_of_t_term.
        apply set_eq.
        revert HH H.
        induction l; intros HH H.
        {
            intros x0. simpl. ltac1:(set_solver).
        }
        {
            intros x0.
            specialize (IHl HH).
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            specialize (H1 HH).
            ltac1:(set_solver).
        }
    }
Qed.



Lemma subst_id
{Σ : StaticModel}
a x:
TermOverBoV_subst a x (t_over (bov_variable x)) = a
.
Proof.
induction a; simpl.
{
    ltac1:(repeat case_match); subst; reflexivity.
}
{
    f_equal.
    revert H.
    induction l; intros HH.
    {
    simpl. reflexivity.
    }
    {
    rewrite Forall_cons in HH. destruct HH as [HH1 HH2].
    specialize (IHl HH2). clear HH2.
    simpl. rewrite IHl. rewrite HH1. reflexivity.
    }
}
Qed.



Lemma vars_of_TermOverBoV_subst
    {Σ : StaticModel}
    (t t' : TermOver BuiltinOrVar)
    (x : variable)
:
    x ∈ vars_of t ->
    vars_of (TermOverBoV_subst t x t') =
    vars_of t' ∪ (vars_of t ∖ {[x]})
.
Proof.
    induction t; intros HH1; simpl in *.
    {
        unfold vars_of in HH1; simpl in HH1.
        unfold vars_of in HH1; simpl in HH1.
        unfold vars_of_BoV in HH1; simpl in HH1.
        destruct a; simpl in *.
        {
        rewrite elem_of_empty in HH1. inversion HH1.
        }
        {
        rewrite elem_of_singleton in HH1.
        subst x0.
        destruct (decide (x = x))>[|ltac1:(contradiction)].
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        ltac1:(set_solver).
        }
    }
    {
        revert HH1 H.
        unfold vars_of; simpl.
        induction l; intros HH1 HH2.
        {
        simpl. unfold vars_of; simpl. ltac1:(set_solver).
        }
        {
        rewrite Forall_cons in HH2. destruct HH2 as [HH2 HH3].
        simpl in HH1. rewrite elem_of_union in HH1.
        destruct (decide (x ∈ vars_of a)) as [Hin|Hnotin].
        {
            specialize (HH2 Hin). simpl.
            unfold vars_of; simpl.
            unfold vars_of in HH2; simpl in HH2.
            rewrite HH2. clear HH2.
            destruct (decide (x ∈ (⋃ (vars_of <$> l)))) as [Hin2 |Hnotin2].
            {
            specialize (IHl Hin2 HH3).
            unfold vars_of in IHl; simpl in IHl.
            unfold fmap in IHl.
            unfold fmap.
            rewrite IHl.
            unfold vars_of ; simpl.
            unfold vars_of ; simpl.
            ltac1:(set_solver).
            }
            {
            assert(Htmp: ((fun t'' => TermOverBoV_subst t'' x t')<$> l = l)).
            {
                clear -Hnotin2. revert Hnotin2.
                induction l; simpl; intros Hnotin2.
                { reflexivity. }
                {
                rewrite elem_of_union in Hnotin2.
                apply Decidable.not_or in Hnotin2.
                destruct Hnotin2 as [HH1 HH2].
                specialize (IHl HH2).
                unfold fmap in IHl.
                rewrite IHl.
                rewrite subst_notin2.
                { reflexivity. }
                { exact HH1. }
                }
            }
            unfold fmap in Htmp.
            ltac1:(replace (list_fmap) with (map)  in Htmp by reflexivity).
            rewrite Htmp.
            unfold vars_of . simpl.
            ltac1:(set_solver).
            }
        }
        {
            clear HH2.
            destruct HH1 as [HH1|HH1].
            {
            ltac1:(exfalso; apply Hnotin; apply HH1).
            }
            {
            specialize (IHl HH1 HH3).        
            unfold vars_of ; simpl.
            unfold vars_of  in IHl; simpl in IHl.
            rewrite subst_notin2.
            {
                unfold fmap in IHl; simpl in IHl.
                unfold vars_of ; simpl.
                unfold fmap.
                rewrite IHl.
                ltac1:(set_solver).  
            }
            {
                exact Hnotin.
            }
            }
        }
        }
    }
Qed.



Lemma vars_of_to_l2r_subst
    {Σ : StaticModel}
    (φ ψ : TermOver BuiltinOrVar)
    (h : variable)
    :
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    h ∉ vars_of_to_l2r ψ ->
    vars_of_to_l2r (TermOverBoV_subst φ h ψ)
    ≡ₚ ((filter (fun x => x <> h) (vars_of_to_l2r φ)) ++ (vars_of_to_l2r ψ))
.
Proof.
    intros Hinφ Hnotinψ.
    induction φ; simpl.
    {
        destruct a; simpl in *.
        {
            ltac1:(lia).
        }
        {
            rewrite filter_cons in Hinφ.
            rewrite filter_cons.
            destruct (decide (h = x)); simpl in *.
            {
                subst x.
                destruct (decide (h<>h))>[ltac1:(contradiction)|].
                rewrite filter_nil. simpl. reflexivity.
            }
            {
                ltac1:(lia).
            }
        }
    }
    {
        simpl in *.
        assert (H'inφ := Hinφ).
        assert (Hlen: length (filter (fun x => h ∈ vars_of_to_l2r x) l) = 1).
        {
            apply length_filter_eq__eq__length_filter_in__one in H'inφ.
            ltac1:(replace map with (@fmap _ list_fmap) in H'inφ by reflexivity).
            ltac1:(unshelve(erewrite filter_fmap in H'inφ)).
            {
                intros x.
                unfold compose.
                apply _.
            }
            rewrite length_fmap in H'inφ.
            apply H'inφ.
        }
        apply count_one_split in Hlen.
        destruct Hlen as [la1 [b1 [lc1 [HH'1 [HH'2 [HH'3 HH'4]]]]]].

        assert (Hvl := HH'1).
        apply (f_equal (fmap vars_of_to_l2r)) in Hvl.
        rewrite fmap_app in Hvl.
        rewrite fmap_cons in Hvl.
        ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
        rewrite Hvl.
        rewrite concat_app.
        rewrite concat_cons.
        rewrite filter_app.
        rewrite filter_app.
        rewrite HH'1.
        rewrite fmap_app.
        rewrite fmap_cons.
        rewrite fmap_app.
        rewrite concat_app.
        rewrite fmap_cons.
        rewrite concat_cons.

        assert (HJ1: Forall (λ x : variable, h ≠ x) (concat (vars_of_to_l2r <$> la1))).
        {
            rewrite Forall_forall.
            rewrite Forall_forall in HH'3.
            intros x Hx.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [l0 [H1 H2]].
            rewrite <- elem_of_list_In in H2.
            rewrite <- elem_of_list_In in H1.
            rewrite elem_of_list_fmap in H1.
            destruct H1 as [t [H1t H2t]].
            subst l0.
            specialize (HH'3 t H2t).
            clear -HH'3 H2.
            intros HContra. subst.
            apply HH'3. apply H2.
        }

        assert (HJ2 : Forall (λ x : variable, h ≠ x) (concat (vars_of_to_l2r <$> lc1))).
        {
            rewrite Forall_forall.
            rewrite Forall_forall in HH'4.
            intros x Hx.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [l0 [H1 H2]].
            rewrite <- elem_of_list_In in H2.
            rewrite <- elem_of_list_In in H1.
            rewrite elem_of_list_fmap in H1.
            destruct H1 as [t [H1t H2t]].
            subst l0.
            specialize (HH'4 t H2t).
            clear -HH'4 H2.
            intros HContra. subst.
            apply HH'4. apply H2.
        }


        rewrite HH'1 in H.
        rewrite Forall_app in H.
        rewrite Forall_cons in H.
        destruct H as [IHH1 [IH2 IH3]].


        ltac1:(ospecialize (IH2 _)).
        {

            rewrite HH'1 in H'inφ.
            ltac1:(replace map with (@fmap _ list_fmap) in H'inφ by reflexivity).
            rewrite fmap_app in H'inφ.
            rewrite fmap_cons in H'inφ.
            rewrite concat_app in H'inφ.
            rewrite concat_cons in H'inφ.
            rewrite filter_app in H'inφ.
            rewrite filter_app in H'inφ.
            rewrite length_app in H'inφ.
            rewrite length_app in H'inφ.
            assert (Hfil1 : length (filter (eq h) (concat (vars_of_to_l2r <$> la1))) = 0).
            {
                rewrite list_filter_Forall_not.
                { reflexivity. }
                {
                    assumption.
                }
            }
            assert (Hfil2 : length (filter (eq h) (concat (vars_of_to_l2r <$> lc1))) = 0).
            {
                rewrite list_filter_Forall_not.
                { reflexivity. }
                {
                    assumption.
                }
            }
            ltac1:(lia).
        }
        rewrite IH2. clear IH2.

        assert (Heq1: ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> la1) = la1).
        {
            clear -HH'3.
            induction la1.
            { reflexivity. }
            {
                rewrite Forall_cons in HH'3.
                destruct HH'3 as [H1 H2].
                specialize (IHla1 H2).
                rewrite fmap_cons.
                rewrite IHla1.
                rewrite subst_notin.
                { reflexivity. }
                { apply H1. }
            }
        }

        assert (Heq2: ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> lc1) = lc1).
        {
            clear -HH'4.
            induction lc1.
            { reflexivity. }
            {
                rewrite Forall_cons in HH'4.
                destruct HH'4 as [H1 H2].
                specialize (IHlc1 H2).
                rewrite fmap_cons.
                rewrite IHlc1.
                rewrite subst_notin.
                { reflexivity. }
                { apply H1. }
            }
        }
        rewrite Heq1. rewrite Heq2. clear Heq1 Heq2.

        assert (HJ1': filter (λ x : variable, x ≠ h) (concat (vars_of_to_l2r <$> la1)) = concat (vars_of_to_l2r <$> la1)).
        {
            clear -HJ1.
            rewrite list_filter_Forall_all.
            { reflexivity. }
            {
                eapply List.Forall_impl>[|apply HJ1].
                intros x Ha. simpl in Ha. ltac1:(congruence).
            }
        }

        assert (HJ2': filter (λ x : variable, x ≠ h) (concat (vars_of_to_l2r <$> lc1)) = concat (vars_of_to_l2r <$> lc1)).
        {
            clear -HJ2.
            rewrite list_filter_Forall_all.
            { reflexivity. }
            {
                eapply List.Forall_impl>[|apply HJ2].
                intros x Ha. simpl in Ha. ltac1:(congruence).
            }
        }

        rewrite HJ1'. clear HJ1 HJ1'.
        rewrite HJ2'. clear HJ2 HJ2'.
        clear.
        ltac1:(solve_Permutation).
    }
Qed.

