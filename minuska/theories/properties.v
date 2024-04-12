From Minuska Require Import
    prelude
    spec
    lowlang
.

Fixpoint vars_of_to_l2r
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    : list variable
:= 
    match t with
    | t_over (bov_builtin _) => []
    | t_over (bov_variable x) => [x]
    | t_term s l => concat (map vars_of_to_l2r l)
    end
.

Lemma vars_of_to_l2r_of_tob
    {Σ : StaticModel}
    (r : TermOver builtin_value)
    :
    vars_of_to_l2r (TermOverBuiltin_to_TermOverBoV r) = []
.
Proof.
    induction r; simpl.
    { reflexivity. }
    {
        revert H.
        induction l; intros H; simpl.
        { reflexivity. }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            rewrite IHl.
            unfold TermOverBuiltin_to_TermOverBoV  in *.
            rewrite H1.
            reflexivity.
        }
    }
Qed.


Lemma sat2B_uglify
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    : sat2B ρ t φ -> satisfies (fmap uglify' ρ) (uglify' t) (uglify' φ)
.
Proof.
    remember (TermOver_size φ) as sz.
    assert (Hsz: (TermOver_size φ) <= sz) by ltac1:(lia).
    clear Heqsz.
    revert t φ Hsz.
    induction sz; simpl; intros t φ Hsz.
    {
        destruct φ; simpl in Hsz; ltac1:(lia).
    }
    destruct φ; simpl in *; intros HH.
    {
        destruct a;
        ltac1:(simp sat2B in HH; unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar in HH); subst; simpl.
        {
            constructor. constructor.
        }
        {
            unfold satisfies; simpl.
            destruct t; simpl; constructor.
            { 
                constructor.
                unfold Valuation2 in *. unfold Valuation in *.
                rewrite lookup_fmap.
                ltac1:(rewrite HH). simpl. reflexivity.
            }
            {
                unfold satisfies; simpl.
                unfold Valuation2 in *. unfold Valuation in *.
                rewrite lookup_fmap.
                ltac1:(rewrite HH). simpl. reflexivity.
            }
        }
    }
    {
        destruct t;
            ltac1:(simp sat2B in HH).
        { inversion HH. }
        {
            destruct HH as [H1 [H2 H3]].
            constructor.
            fold (@uglify' (@symbol Σ)).
            subst s0.

            revert l0 H2 H3.

            ltac1:(induction l using rev_ind_T); intros l' H2 H3.
            {
                simpl in H2.
                destruct l'; simpl in *.
                {
                    constructor.
                }
                {
                    ltac1:(lia).
                }
            }
            {
                destruct (analyze_list_from_end l') as [Hana|Hana]; simpl in *.
                { 
                    subst.
                    rewrite app_length in H2. simpl in *.
                    ltac1:(lia).
                }
                {
                    destruct Hana as [l'0 [x0 Hana]].
                    subst l'.
                    rewrite app_length in H2. simpl in *.
                    unfold to_PreTerm''.
                    do 2 (rewrite map_app).
                    do 2 (rewrite fold_left_app).
                    simpl.
                    unfold helper.
                    destruct (uglify' x0) eqn:Hux0;
                        destruct (uglify' x) eqn:Hux;
                        simpl in *.
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        simpl in *.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x x0.
                        constructor.
                        {
                            apply IHl.
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                intros.
                                apply H3 with (i := i);
                                    rewrite lookup_app_l;
                                    try assumption.
                                {
                                    apply lookup_lt_Some in pf1.
                                    exact pf1.
                                }
                                {
                                    apply lookup_lt_Some in pf2.
                                    exact pf2.
                                }
                            }
                        }
                        {
                            specialize (H3 (length l) (prettify' ao) (prettify' ao0)).
                            rewrite lookup_app_r in H3>[|ltac1:(apply reflexivity)].
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            rewrite app_length in H2. simpl in H2.
                            apply Nat.add_cancel_r in H2.
                            rewrite lookup_app_r in H3>[|ltac1:(rewrite H2; apply reflexivity)].
                            ltac1:(rewrite H2 in H3).
                            rewrite Nat.sub_diag in H3.
                            specialize (H3 eq_refl).
                            specialize (IHsz (prettify' ao) (prettify' ao0)).
                            rewrite sum_list_with_app in Hsz. simpl in Hsz.
                            specialize (IHsz ltac:(lia) H3).
                            rewrite (uglify'_prettify') in IHsz.
                            rewrite (uglify'_prettify') in IHsz.
                            inversion IHsz; subst; clear IHsz.
                            assumption.
                        }
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        simpl in *.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x x0.
                        constructor.
                        {
                            apply IHl.
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                intros.
                                apply H3 with (i := i);
                                    rewrite lookup_app_l;
                                    try assumption.
                                {
                                    apply lookup_lt_Some in pf1.
                                    exact pf1.
                                }
                                {
                                    apply lookup_lt_Some in pf2.
                                    exact pf2.
                                }
                            }
                        }
                        {
                            specialize (H3 (length l) (prettify' ao) (t_over operand)).
                            rewrite app_length in H2. simpl in H2.
                            apply Nat.add_cancel_r in H2.
                            rewrite lookup_app_r in H3>[|ltac1:(apply reflexivity)].
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            rewrite lookup_app_r in H3>[|ltac1:(rewrite H2; apply reflexivity)].
                            ltac1:(rewrite H2 in H3).
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            specialize (IHsz (prettify' ao) (t_over operand)).
                            rewrite sum_list_with_app in Hsz. simpl in Hsz.
                            specialize (IHsz ltac:(simpl;lia) H3).
                            rewrite (uglify'_prettify') in IHsz.
                            inversion IHsz; subst; clear IHsz.
                            assumption.
                        }
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        simpl in *.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x x0.
                        constructor.
                        {
                            apply IHl.
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                intros.
                                apply H3 with (i := i);
                                    rewrite lookup_app_l;
                                    try assumption.
                                {
                                    apply lookup_lt_Some in pf1.
                                    exact pf1.
                                }
                                {
                                    apply lookup_lt_Some in pf2.
                                    exact pf2.
                                }
                            }
                        }
                        {
                            rewrite app_length in H2. simpl in H2.
                            rewrite Nat.add_cancel_r in H2.
                            specialize (H3 (length l) (t_over operand) (prettify' ao) ).
                            rewrite lookup_app_r in H3>[|ltac1:(apply reflexivity)].
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            
                            rewrite lookup_app_r in H3>[|ltac1:(rewrite H2; apply reflexivity)].
                            ltac1:(rewrite H2 in H3).
                            rewrite Nat.sub_diag in H3.
                            specialize (H3 eq_refl).
                            specialize (IHsz (t_over operand) (prettify' ao)).
                            rewrite sum_list_with_app in Hsz. simpl in Hsz.
                            specialize (IHsz ltac:(simpl;lia) H3).
                            rewrite (uglify'_prettify') in IHsz.
                            inversion IHsz; subst; clear IHsz.
                        }
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        simpl in *.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x x0.
                        constructor.
                        {
                            apply IHl.
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                intros.
                                apply H3 with (i := i);
                                    rewrite lookup_app_l;
                                    try assumption.
                                {
                                    apply lookup_lt_Some in pf1.
                                    exact pf1.
                                }
                                {
                                    apply lookup_lt_Some in pf2.
                                    exact pf2.
                                }
                            }
                        }
                        {
                            rewrite app_length in H2. simpl in H2.
                            rewrite Nat.add_cancel_r in H2.
                            specialize (H3 (length l) (t_over operand) (t_over operand0)).
                            rewrite lookup_app_r in H3>[|ltac1:(apply reflexivity)].
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            
                            rewrite lookup_app_r in H3>[|ltac1:(rewrite H2; lia)].
                            ltac1:(rewrite H2 in H3).
                            rewrite Nat.sub_diag in H3.
                            specialize (H3 eq_refl).
                            specialize (IHsz (t_over operand) (t_over operand0)).
                            rewrite sum_list_with_app in Hsz. simpl in Hsz.
                            specialize (IHsz ltac:(simpl;lia) H3).
                            inversion IHsz; subst; clear IHsz.
                            assumption.
                        }
                    }
                }
            }
        }
    }
Qed.

Lemma uglify_sat2B
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    : satisfies (fmap uglify' ρ) (uglify' t) (uglify' φ)
    -> sat2B ρ t φ
.
Proof.
    remember (TermOver_size φ) as sz.
    assert (Hsz: (TermOver_size φ) <= sz) by ltac1:(lia).
    clear Heqsz.
    revert t φ Hsz.
    induction sz; simpl; intros t φ Hsz.
    {
        destruct φ; simpl in Hsz; ltac1:(lia).
    }
    destruct φ; simpl in *; intros HH.
    {
        destruct t;
            simpl in HH;
            inversion HH; subst; clear HH.
        {
            inversion pf; subst; clear pf;
            ltac1:(simp sat2B);
            try reflexivity.
            unfold Valuation in *.
            unfold Valuation2 in *.
            rewrite lookup_fmap in H.
            destruct (ρ !! x) eqn:Hρx;
                simpl in *.
            {
                ltac1:(rewrite Hρx).
                ltac1:(rewrite Hρx in H).
                simpl in H.
                inversion H; subst; clear H.
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                reflexivity.
            }
            { ltac1:(rewrite Hρx in H). inversion H. }
        }
        {
            destruct a; simpl in *.
            {
                inversion X.
            }
            inversion X; subst; clear X.
            ltac1:(simp sat2B).
            unfold Valuation in *.
            unfold Valuation2 in *.
            rewrite lookup_fmap in H0.
            unfold TermOver in *.
            destruct (ρ!!x) eqn:Hρx; simpl in *.
            {
                inversion H0; subst; clear H0.
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                simpl.
                simpl in Hρx.
                rewrite <- (cancel prettify uglify' (t_term s l)).
                apply Hρx.
            }
            { inversion H0. }
        }
    }
    {
        destruct t; simpl in *; ltac1:(simp sat2B).
        {
            inversion HH.
        }
        unfold satisfies in HH; simpl in HH.
        inversion HH; subst; clear HH.
        unfold satisfies in pf; simpl in pf.
        revert l0 Hsz pf;
        ltac1:(induction l using rev_ind_T); simpl in *;
            intros l0 Hsz pf.
        {
            destruct (analyze_list_from_end l0); subst; simpl in *.
            {
                inversion pf; subst; clear pf.
                (repeat split).
                intros.
                rewrite lookup_nil in pf1. inversion pf1.
            }
            {
                inversion pf; subst; clear pf.
                destruct s1 as [l' [x HH]].
                subst.
                rewrite map_app in H1.
                rewrite to_PreTerm''_app in H1.
                simpl in H1.
                unfold helper in H1.
                destruct (uglify' x) eqn:Hux.
                { inversion H1. }
                { inversion H1. }
            }
        }
        {
            destruct (analyze_list_from_end l0) as [Hnil|Hcons]; subst; simpl in *.
            {
                inversion pf; subst; clear pf.
                unfold to_PreTerm'' in H2.
                rewrite map_app in H2.
                rewrite fold_left_app in H2.
                simpl in H2.
                unfold helper in H2.
                destruct (uglify' x) eqn:Hux; simpl in *.
                {
                    inversion H2.
                }
                {
                    inversion H2.
                }
            }
            {
                rewrite sum_list_with_app in Hsz. simpl in Hsz.
                rewrite map_app in pf.
                rewrite to_PreTerm''_app in pf.
                simpl in pf.
                unfold helper in pf.
                destruct Hcons as [l' [x0 Hcons]].
                subst l0.
                destruct (uglify' x) eqn:Hux; simpl in *.
                {
                    apply (f_equal prettify) in Hux.
                    rewrite (cancel prettify uglify') in Hux.
                    subst x.
                    simpl in *.
                    inversion pf; subst; clear pf.
                    {
                        subst. simpl in *.
                        unfold to_PreTerm'' in H1.
                        rewrite map_app in H1.
                        rewrite fold_left_app in H1.
                        simpl in H1.
                        unfold helper in H1.
                        destruct (uglify' x0) eqn:Hux0; simpl in *.
                        {
                            inversion H1.
                        }
                        {
                            inversion H1; subst; clear H1.
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0.
                            simpl in *.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IHl1 [IHl2 IHl3]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length).
                            simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            destruct (decide (i = length l)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(apply reflexivity)].
                                rewrite lookup_app_r in H2i>[|ltac1:(rewrite IHl2; apply reflexivity)].
                                ltac1:(rewrite IHl2 in H2i).
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                inversion H1i; subst; clear H1i.
                                inversion H2i; subst; clear H2i.
                                apply IHsz.
                                { simpl. ltac1:(lia). }
                                {
                                    inversion X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        eapply IHl3.
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in *.
                                        unfold TermOver in *.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in *.
                                    unfold TermOver in *.
                                    ltac1:(lia).
                                }
                            }
                        }
                    }
                    {
                        rewrite map_app in H1.
                        unfold to_PreTerm'' in H1.
                        rewrite fold_left_app in H1.
                        simpl in H1.
                        unfold helper in H1.
                        destruct (uglify' x0) eqn:Hux0; simpl in *.
                        {
                            inversion H1; subst; clear H1.
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0; simpl in *.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length).
                            simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            destruct (decide (length l = i)).
                            {
                                subst i.
                                unfold TermOver in *.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                inversion H1i; subst; clear H1i.
                                inversion H2i; subst; clear H2i.
                                apply IHsz.
                                { simpl. ltac1:(lia). }
                                {
                                    do 2 (rewrite uglify'_prettify' ).
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        eapply IH3l.
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        unfold TermOver in *.
                                        ltac1:(lia).                                        
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    unfold TermOver in *.
                                    ltac1:(lia).
                                }
                            }
                        }
                        {
                            inversion H1.
                        }
                    }
                }
                {
                    inversion pf; subst; clear pf.
                    {
                        apply (f_equal prettify) in Hux.
                        rewrite (cancel prettify uglify') in Hux.
                        subst x. simpl in *.
                        rewrite map_app in H1.
                        unfold to_PreTerm'' in H1.
                        rewrite fold_left_app in H1.
                        simpl in H1.
                        unfold helper in H1.
                        destruct (uglify' x0) eqn:Hux0; simpl in *.
                        {
                            inversion H1.
                        }
                        {
                            inversion H1; subst; clear H1.
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0. simpl in *.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length); simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            destruct (decide (length l = i)).
                            {
                                subst i.
                                unfold TermOver in *.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                inversion H1i; subst; clear H1i.
                                inversion H2i; subst; clear H2i.
                                apply IHsz.
                                { simpl. ltac1:(lia). }
                                {
                                    simpl.
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        eapply IH3l.
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        unfold TermOver in *.
                                        ltac1:(lia).                                        
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    unfold TermOver in *.
                                    ltac1:(lia).
                                }
                            }
                        }
                    }
                    {
                        unfold to_PreTerm'' in H1.
                        rewrite map_app in H1.
                        rewrite fold_left_app in H1.
                        simpl in H1.
                        unfold helper in H1.
                        destruct (uglify' x0) eqn:Hux0; simpl in *.
                        {
                            inversion H1; subst; clear H1.
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0.
                            apply (f_equal prettify) in Hux.
                            rewrite (cancel prettify uglify') in Hux.
                            subst x.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length); simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            destruct (decide (length l = i)).
                            {
                                subst i.
                                unfold TermOver in *.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                inversion H1i; subst; clear H1i.
                                inversion H2i; subst; clear H2i.
                                apply IHsz.
                                { simpl. ltac1:(lia). }
                                {
                                    simpl.
                                    rewrite uglify'_prettify'.
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        eapply IH3l.
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        unfold TermOver in *.
                                        ltac1:(lia).                                        
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    unfold TermOver in *.
                                    ltac1:(lia).
                                }
                            }
                        }
                        {
                            inversion H1.
                        }

                    }
                }
            }
        }
    }
Qed.


Lemma Expression2_Expression_evaluate
    {Σ : StaticModel}
    (ρ : Valuation2)
    (e : Expression2)
    :
    Expression2_evaluate ρ e =
    prettify <$> (Expression_evaluate (fmap uglify' ρ) (Expression2_to_Expression e))
.
Proof.
    induction e; simpl.
    {
        rewrite (cancel prettify uglify').
        reflexivity.
    }
    {
        rewrite lookup_fmap.
        unfold Valuation in *. unfold Valuation2 in *.
        unfold TermOver in *.
        destruct (ρ !! x) eqn:Hρx; simpl.
        {
            simpl.
            rewrite (cancel prettify uglify').
            reflexivity.
        }
        {
            reflexivity.
        }
    }
    {
        rewrite (cancel prettify uglify').
        reflexivity.
    }
    {
        rewrite IHe. clear IHe.
        rewrite option_fmap_bind.
        unfold compose.
        destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e))
            eqn:Heq; simpl.
        {
            rewrite (cancel prettify uglify').
            reflexivity.
        }
        {
            reflexivity.
        }
    }
    {
        rewrite IHe1.
        rewrite IHe2.
        rewrite option_fmap_bind.
        destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e1)) eqn:Heq1;
            simpl.
        {
            rewrite option_fmap_bind.
            destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e2)) eqn:Heq2;
                simpl.
            {

                rewrite (cancel prettify uglify').
                reflexivity.
            }
            {
                reflexivity.
            }
        }
        {
            reflexivity.
        }
    }
    {
        rewrite IHe1.
        rewrite IHe2.
        rewrite IHe3.

        rewrite option_fmap_bind.
        destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e1)) eqn:Heq1;
            simpl.
        {
            rewrite option_fmap_bind.
            destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e2)) eqn:Heq2;
                simpl.
            {
                rewrite option_fmap_bind.
                destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e3)) eqn:Heq3;
                    simpl.
                {
                    rewrite (cancel prettify uglify').
                    reflexivity.
                }
                {
                    reflexivity.
                }
            }
            {
                reflexivity.
            }
        }
        {
            reflexivity.
        }
    }
Qed.



Lemma sat2E_uglify
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver Expression2)
    :
    sat2E ρ t φ ->
    satisfies (fmap uglify' ρ) t (TermOver_map Expression2_to_Expression φ)
.
Proof.
    remember (TermOver_size φ) as sz.
    assert (Hsz: (TermOver_size φ) <= sz) by ltac1:(lia).
    clear Heqsz.
    revert t φ Hsz.
    induction sz; simpl; intros t φ Hsz.
    {
        destruct φ; simpl in Hsz; ltac1:(lia).
    }
    destruct φ; simpl in *; intros HH.
    {
        unfold satisfies; simpl.
        unfold satisfies; simpl.
        destruct (uglify' t) eqn:Hut.
        {
            apply (f_equal prettify) in Hut.
            rewrite (cancel prettify uglify') in Hut.
            subst t.
            constructor.
            unfold satisfies; simpl.
            ltac1:(simp sat2E in HH).
            simpl in *.
            rewrite Expression2_Expression_evaluate in HH.
            destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression a)) eqn:Heq;
                simpl in *.
            {
                injection HH as HH.
                apply (f_equal uglify' ) in HH.
                rewrite (cancel uglify' prettify) in HH.
                subst g.
                simpl.
                rewrite (uglify'_prettify').
                reflexivity.
            }
            {
                inversion HH.
            }
        }
        {
            apply (f_equal prettify) in Hut.
            rewrite (cancel prettify uglify') in Hut.
            subst t.
            simpl in HH.
            ltac1:(simp sat2E in HH).
            constructor.
            unfold satisfies; simpl.
            rewrite Expression2_Expression_evaluate in HH.
            destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression a)) eqn:Heq;
                simpl in *.
            {
                injection HH as HH.
                apply (f_equal uglify') in HH.
                rewrite (cancel uglify' prettify) in HH.
                subst g. simpl.
                reflexivity.
            }
            { inversion HH. }
        }
    }
    {
        destruct t; simpl in *.
        {
            ltac1:(simp sat2E in HH).
            inversion HH.
        }
        {
            ltac1:(simp sat2E in HH).
            destruct HH as [H1 [H2 H3]].
            subst s0.
            constructor.
            fold (@uglify' (@symbol Σ)).
            unfold to_PreTerm''.
            revert l0 H2 H3.
            ltac1:(induction l using rev_ind_T); intros l0 H2 H3.
            {
                destruct (analyze_list_from_end l0) as [Hempty|Hnempty]; simpl in *.
                {
                    subst l0. simpl. constructor.
                }
                {
                    destruct Hnempty as [l' [x Hnempty]].
                    subst l0.
                    rewrite app_length in H2.
                    simpl in H2.
                    ltac1:(lia).
                }
            }
            {
                destruct (analyze_list_from_end l0) as [Hempty|Hnempty]; simpl in *.
                {
                    subst l0. simpl.
                    rewrite app_length in H2.
                    simpl in H2.
                    ltac1:(lia).
                }
                {
                    destruct Hnempty as [l' [x0 Hnempty]].
                    subst l0.
                    rewrite app_length in H2.
                    simpl in H2.
                    
                    do 3 (rewrite map_app).
                    do 2 (rewrite fold_left_app).
                    simpl.
                    unfold helper'' at 1.
                    destruct (uglify' x0) eqn:Hux0.
                    {
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x0.
                        unfold helper'' at 2.
                        unfold TermOver in *.
                        destruct (uglify' (TermOver_map Expression2_to_Expression x)) eqn:Hux.
                        {
                            apply (f_equal prettify) in Hux.
                            rewrite (cancel prettify uglify') in Hux.
                            simpl in Hux.
                            rewrite sum_list_with_app in Hsz.
                            simpl in Hsz.
                            specialize (IHl ltac:(lia)).
                            assert (HH := H3 (length l) (prettify' ao) x).
                            rewrite lookup_app_r in HH>[|ltac1:(lia)].
                            rewrite Nat.sub_diag in HH.
                            simpl in HH.
                            specialize (HH eq_refl).
                            rewrite app_length in H2; simpl in H2.
                            rewrite lookup_app_r in HH>[|ltac1:(lia)].
                            rewrite Nat.add_cancel_r in H2.
                            rewrite H2 in HH.
                            rewrite Nat.sub_diag in HH.
                            simpl in HH.
                            specialize (HH eq_refl).
                            specialize (IHsz (prettify' ao) x).
                            specialize (IHsz ltac:(lia) HH).
                            unfold satisfies in IHsz; simpl in IHsz.
                            rewrite Hux in IHsz.
                            do 2 (rewrite (uglify'_prettify') in IHsz).
                            inversion IHsz; subst; clear IHsz.
                            constructor.
                            apply IHl.
                            { ltac1:(lia). }
                            {
                                intros i t' φ' H1i H2i.
                                apply H3 with (i := i).
                                {
                                    rewrite lookup_app_l.
                                    { exact H1i. }
                                    {
                                        apply lookup_lt_Some in H1i.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    rewrite lookup_app_l.
                                    { exact H2i. }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        ltac1:(lia).
                                    }
                                }
                            }
                            {
                                apply pf.
                            }
                        }
                        {
                            apply (f_equal prettify) in Hux.
                            rewrite (cancel prettify uglify') in Hux.
                            simpl in Hux.
                            rewrite sum_list_with_app in Hsz.
                            simpl in Hsz.
                            specialize (IHl ltac:(lia)).
                            assert (HH := H3 (length l) (prettify' ao) x).
                            rewrite lookup_app_r in HH>[|ltac1:(lia)].
                            rewrite Nat.sub_diag in HH.
                            simpl in HH.
                            specialize (HH eq_refl).
                            rewrite app_length in H2; simpl in H2.
                            rewrite lookup_app_r in HH>[|ltac1:(lia)].
                            rewrite Nat.add_cancel_r in H2.
                            rewrite H2 in HH.
                            rewrite Nat.sub_diag in HH.
                            simpl in HH.
                            specialize (HH eq_refl).
                            specialize (IHsz (prettify' ao) x).
                            specialize (IHsz ltac:(lia) HH).
                            unfold satisfies in IHsz; simpl in IHsz.
                            rewrite Hux in IHsz.
                            do 1 (rewrite (uglify'_prettify') in IHsz).
                            inversion IHsz; subst; clear IHsz.
                            constructor.
                            apply IHl.
                            { ltac1:(lia). }
                            {
                                intros i t' φ' H1i H2i.
                                apply H3 with (i := i).
                                {
                                    rewrite lookup_app_l.
                                    { exact H1i. }
                                    {
                                        apply lookup_lt_Some in H1i.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    rewrite lookup_app_l.
                                    { exact H2i. }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        ltac1:(lia).
                                    }
                                }
                            }
                            {
                                apply X.
                            }
                        }
                    }
                    {
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x0.
                        unfold TermOver in *.
                        unfold helper'' at 2.
                        destruct (uglify' (TermOver_map Expression2_to_Expression x)) eqn:Hux.
                        {
                            apply (f_equal prettify) in Hux.
                            rewrite (cancel prettify uglify') in Hux.
                            simpl in Hux.
                            rewrite sum_list_with_app in Hsz.
                            simpl in Hsz.
                            specialize (IHl ltac:(lia)).
                            simpl in H3.
                            assert (HH := H3 (length l) (t_over operand) x).
                            rewrite lookup_app_r in HH>[|ltac1:(lia)].
                            rewrite Nat.sub_diag in HH.
                            simpl in HH.
                            specialize (HH eq_refl).
                            rewrite app_length in H2; simpl in H2.
                            rewrite lookup_app_r in HH>[|ltac1:(lia)].
                            rewrite Nat.add_cancel_r in H2.
                            rewrite H2 in HH.
                            rewrite Nat.sub_diag in HH.
                            simpl in HH.
                            specialize (HH eq_refl).
                            specialize (IHsz (t_over operand) x).
                            specialize (IHsz ltac:(lia) HH).
                            unfold satisfies in IHsz; simpl in IHsz.
                            rewrite Hux in IHsz.
                            do 1 (rewrite (uglify'_prettify') in IHsz).
                            inversion IHsz; subst; clear IHsz.
                        }
                        {
                            apply (f_equal prettify) in Hux.
                            rewrite (cancel prettify uglify') in Hux.
                            simpl in Hux.
                            rewrite sum_list_with_app in Hsz.
                            simpl in Hsz.
                            specialize (IHl ltac:(lia)).
                            simpl in H3.
                            assert (HH := H3 (length l) (t_over operand) x).
                            rewrite lookup_app_r in HH>[|ltac1:(lia)].
                            rewrite Nat.sub_diag in HH.
                            simpl in HH.
                            specialize (HH eq_refl).
                            rewrite app_length in H2; simpl in H2.
                            rewrite lookup_app_r in HH>[|ltac1:(lia)].
                            rewrite Nat.add_cancel_r in H2.
                            rewrite H2 in HH.
                            rewrite Nat.sub_diag in HH.
                            simpl in HH.
                            specialize (HH eq_refl).
                            specialize (IHsz (t_over operand) x).
                            specialize (IHsz ltac:(lia) HH).
                            unfold satisfies in IHsz; simpl in IHsz.
                            rewrite Hux in IHsz.
                            do 0 (rewrite (uglify'_prettify') in IHsz).
                            inversion IHsz; subst; clear IHsz.
                            constructor.
                            apply IHl.
                            { ltac1:(lia). }
                            {
                                intros i t' φ' H1i H2i.
                                apply H3 with (i := i).
                                {
                                    rewrite lookup_app_l.
                                    { exact H1i. }
                                    {
                                        apply lookup_lt_Some in H1i.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    rewrite lookup_app_l.
                                    { exact H2i. }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        ltac1:(lia).
                                    }
                                }
                            }
                            {
                                apply pf.
                            }
                        }
                    }
                }
            }
        }
    }
Qed.

Lemma uglify_sat2E
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver Expression2)
    :
    satisfies (fmap uglify' ρ) t (TermOver_map Expression2_to_Expression φ) ->
    sat2E ρ t φ
.
Proof.
    remember (TermOver_size φ) as sz.
    assert (Hsz: (TermOver_size φ) <= sz) by ltac1:(lia).
    clear Heqsz.
    revert t φ Hsz.
    induction sz; simpl; intros t φ Hsz.
    {
        destruct φ; simpl in Hsz; ltac1:(lia).
    }
    destruct φ; simpl in *; intros HH.
    {
        unfold satisfies in HH; simpl in HH.
        unfold satisfies in HH; simpl in HH.
        ltac1:(simp sat2E).
        rewrite Expression2_Expression_evaluate.
        inversion HH; subst; clear HH.
        {
            apply (f_equal prettify) in H1.
            rewrite (cancel prettify uglify') in H1.
            subst t. inversion pf; subst; clear pf.
            simpl.
            destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression a)) eqn:Heq;
                simpl in *.
            {
                inversion H0; subst; clear H0.
                simpl. reflexivity.
            }
            {
                inversion H0.
            }
        }
        {
            apply (f_equal prettify) in H1.
            rewrite (cancel prettify uglify') in H1.
            subst t. inversion X; subst; clear X.
            simpl.
            destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression a)) eqn:Heq;
                simpl in *.
            {
                inversion H0; subst; clear H0.
                simpl. reflexivity.
            }
            {
                inversion H0.
            }
        }
    }
    {
        destruct t;
            ltac1:(simp sat2E).
        { inversion HH. }
        {
            inversion HH; subst; clear HH.
            revert l0 Hsz pf.
            ltac1:(induction l using rev_ind_T); intros l0 Hsz pf.
            {
                destruct (analyze_list_from_end l0) as [Hempty|Hnempty].
                {
                    subst. inversion pf; subst; clear pf.
                    (repeat split).
                    intros i t' φ' H1i H2i.
                    rewrite lookup_nil in H1i.
                    inversion H1i.
                }
                {
                    destruct Hnempty as [l' [x Hnempty]].
                    subst l0.
                    simpl in *.
                    inversion pf; subst; clear pf.
                    rewrite map_app in H1.
                    rewrite to_PreTerm''_app in H1.
                    simpl in H1.
                    unfold helper in H1.
                    destruct (uglify' x); inversion H1.
                }
            }
            {
                rewrite sum_list_with_app in Hsz. simpl in Hsz.
                destruct (analyze_list_from_end l0) as [Hempty|Hnempty].
                {
                    subst. inversion pf; subst; clear pf.
                    do 2 (rewrite map_app in H2).
                    rewrite to_PreTerm''_app in H2.
                    simpl in H2.
                    unfold helper in H2.
                    destruct (uglify' ((TermOver_map Expression2_to_Expression x))); inversion H2.
                }
                {
                    destruct Hnempty as [l' [x0 Hnempty]].
                    subst l0.
                    unfold satisfies in pf; simpl in pf.
                    do 3 (rewrite map_app in pf).
                    do 2 (rewrite to_PreTerm''_app in pf).
                    simpl in pf.
                    unfold helper'' in pf at 1.
                    destruct (uglify' x0) eqn:Hux0.
                    {
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x0.
                        unfold helper'' in pf at 1.
                        destruct (uglify' (TermOver_map Expression2_to_Expression x)) eqn:Hux.
                        {
                            inversion pf; subst; clear pf.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length).
                            simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            unfold TermOver in *.
                            destruct (decide (i = length l)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                injection H1i as H1i.
                                injection H2i as H2i.
                                subst.
                                apply IHsz.
                                { ltac1:(lia). }
                                {
                                    unfold satisfies; simpl.
                                    rewrite uglify'_prettify'.
                                    rewrite Hux.
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        apply IH3l with (i := i).
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    ltac1:(lia).
                                }
                            }
                        }
                        {
                            inversion pf; subst; clear pf.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length).
                            simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            unfold TermOver in *.
                            destruct (decide (i = length l)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                injection H1i as H1i.
                                injection H2i as H2i.
                                subst.
                                apply IHsz.
                                { ltac1:(lia). }
                                {
                                    unfold satisfies; simpl.
                                    rewrite uglify'_prettify'.
                                    rewrite Hux.
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        apply IH3l with (i := i).
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    ltac1:(lia).
                                }
                            }
                        }
                    }
                    {
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x0.
                        unfold helper'' in pf at 1.
                        destruct (uglify' (TermOver_map Expression2_to_Expression x)) eqn:Hux.
                        {
                            inversion pf; subst; clear pf.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length).
                            simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            unfold TermOver in *.
                            destruct (decide (i = length l)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                injection H1i as H1i.
                                injection H2i as H2i.
                                subst.
                                apply IHsz.
                                { ltac1:(lia). }
                                {
                                    inversion X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        apply IH3l with (i := i).
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    ltac1:(lia).
                                }
                            }
                        }
                        {
                            inversion pf; subst; clear pf.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length).
                            simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            unfold TermOver in *.
                            destruct (decide (i = length l)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                injection H1i as H1i.
                                injection H2i as H2i.
                                subst.
                                apply IHsz.
                                { ltac1:(lia). }
                                {
                                    unfold satisfies; simpl.
                                    rewrite Hux.
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        apply IH3l with (i := i).
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    ltac1:(lia).
                                }
                            }
                        }
                    }
                }
            }
        }
    }
Qed.