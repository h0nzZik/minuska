From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    minusl_compile
    minusl_syntax
    minusl_semantics
.

Require Import Ring.
Require Import ArithRing.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Wf.

From Equations Require Export Equations.


#[global]
Set Equations Transparent.




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


(*
Lemma frto_step_app
    {Σ : StaticModel}
    (Act : Set)
    :
    forall
        Γ
        (t1 t2 t3 : TermOver builtin_value)
        (w : list Act)
        (a : Act)
        r,
    r ∈ Γ ->
    flattened_rewrites_to_over Γ t1 w t2 ->
    flattened_rewrites_to r (uglify' t2) a (uglify' t3) ->
    flattened_rewrites_to_over Γ t1 (w++[a]) t3
.
Proof.
    intros Γ t1 t2 t3 w a r Hr H1 H2.
    induction H1.
    {
        simpl.
        eapply frto_step.
        { exact Hr. }
        { exact H2. }
        { apply frto_base. }
    }
    {
        simpl.
        specialize (IHflattened_rewrites_to_over H2).
        eapply frto_step.
        { exact e. }
        { exact f. }
        { apply IHflattened_rewrites_to_over. }
    }
Qed.
*)
(*
Lemma frto_app
    {Σ : StaticModel}
    (Act : Set)
    :
    forall
        Γ
        (t1 t2 t3 : TermOver builtin_value)
        (w1 w2 : list Act),
    flattened_rewrites_to_over Γ t1 w1 t2 ->
    flattened_rewrites_to_over Γ t2 w2 t3 ->
    flattened_rewrites_to_over Γ t1 (w1++w2) t3
.
Proof.
    intros.
    revert t1 t2 t3 w2 X X0.
    induction w1; intros t1 t2 t3 w2 H0 H1.
    {
        inversion H0; subst; clear H0.
        simpl.
        exact H1.
    }
    {
        simpl.
        inversion H0; subst; clear H0.
        eapply frto_step>[|apply X|].
        { assumption. }
        {
            eapply IHw1.
            { apply X0. }
            { apply H1. }
        }
    }
Qed.
*)



Definition isDownC
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (t : TermOver builtin_value)
    : Prop
:=
    exists ctrl data cont,
    t = downC topSymbol cseqSymbol ctrl data cont
.

Fixpoint hasDepthExactly
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (depth : nat)
    (t : TermOver builtin_value)
:=
    match t with
    | t_term _ [t_term _ [ctlr; cont]; _] =>
        match depth with
        | 0 => False
        | S depth' =>
            isDownC topSymbol cseqSymbol t /\
            hasDepthExactly topSymbol cseqSymbol depth' cont
        end
    | _ => depth = 0
    end
.

Definition projTopCtrl
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    match t with
    | t_term _ [t_term _ [ctrl; _]; _] => Some ctrl
    | _ => None
    end
.

Definition projTopCont
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    match t with
    | t_term _ [t_term _ [_; cont]; _] => Some cont
    | _ => None
    end
.

Definition projTopData
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    match t with
    | t_term _ [_; data] => Some data
    | _ => None
    end
.

#[export]
Instance IsDownC_dec
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (t : TermOver builtin_value)
    : Decision (isDownC topSymbol cseqSymbol t)
.
Proof.
    unfold isDownC.
    remember (projTopCtrl t) as mctrl.
    remember (projTopCont t) as mcont.
    remember (projTopData t) as mdata.
    destruct mctrl.
    {
        destruct mcont.
        {
            destruct mdata.
            {
                unfold downC.
                unfold projTopCtrl, projTopCont,projTopData in *.
                ltac1:(repeat case_match; simplify_eq/=).
                destruct (decide (s = topSymbol)).
                {
                    destruct (decide (s0 = cseqSymbol)).
                    {
                        subst.
                        left.
                        exists t5,t4,t6.
                        reflexivity.
                    }
                    {
                        right.
                        intros HContra.
                        ltac1:(naive_solver).
                    }
                }
                {
                    right.
                    intros HContra.
                    ltac1:(naive_solver).
                }
            }
            {
                right.
                unfold projTopData in Heqmdata.
                ltac1:(repeat case_match; simplify_eq/=; naive_solver).
            }
        }
        {
            right.
            unfold projTopCont in Heqmcont.
            ltac1:(repeat case_match; simplify_eq/=; naive_solver).
        }
    }
    {
        right.
        unfold projTopCtrl in Heqmctrl.
        ltac1:(repeat case_match; simplify_eq/=; naive_solver).
    }
Defined.



Lemma in_compile_inv
    {Σ : StaticModel}
    (Act : Set)
    {_aD : EqDecision Act}
    (D: MinusL_LangDef Act)
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable)
    (r : RewritingRule2 Act)
:
  r
∈ compile invisible_act topSymbol cseqSymbol holeSymbol
  continuationVariable D ->
  (
    (
        { lc : TermOver BuiltinOrVar &
        { ld : TermOver BuiltinOrVar &
        { a : Act &
        { rc : TermOver Expression2 &
        { rd : TermOver Expression2 &
        { cond : SideCondition &
            mld_rewrite Act lc ld a rc rd cond ∈ mlld_decls Act D /\
            r =
            {|
                r_from :=
                t_term topSymbol
                [t_term cseqSymbol
                [lc; t_over (bov_variable continuationVariable)];
                ld];
                r_to :=
                t_term topSymbol
                [t_term cseqSymbol
                [rc; t_over (e_variable continuationVariable)];
                rd];
                r_scs := cond;
                r_act := a
            |}
        }}}}}}
    ) + (
        { c : _ &
        { h : variable &
        { cond : SideCondition &
        mld_context Act c h cond ∈ mlld_decls Act D /\
        (
            r = ctx_heat invisible_act topSymbol cseqSymbol holeSymbol
                (fresh
                (h
                :: vars_of_to_l2r c ++
                elements (vars_of cond) ++
                elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D)))))
                (fresh
                (h
                :: fresh
                (h
                :: vars_of_to_l2r c ++
                elements (vars_of cond) ++
                elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D))))
                :: vars_of_to_l2r c ++
                elements (vars_of cond) ++
                elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D)))))
                (MinusL_isValue Act D)
                (MinusL_isNonValue Act D)
                c h
                cond
            \/
            r =
            ctx_cool invisible_act topSymbol cseqSymbol holeSymbol
            (fresh
            (h
            :: vars_of_to_l2r c ++
            elements (vars_of cond) ++
            elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D)))))
            (fresh
            (h
            :: fresh
            (h
            :: vars_of_to_l2r c ++
            elements (vars_of cond) ++
            elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D))))
            :: vars_of_to_l2r c ++
            elements (vars_of cond) ++
            elements ((vars_of (mlld_isValue_c Act D)) ∪  (vars_of (mlld_isNonValue_c Act D)))))
            (MinusL_isValue Act D)
            (MinusL_isNonValue Act D)
            c
            h
        )
        }}}
    )
  )
.
Proof.
    intros HH.
    unfold compile in HH.
    eapply list_find_elem_of_isSome with (P := (eq r)) in HH.
    {
        unfold is_true,isSome in *.
        ltac1:(case_match).
        {
            clear HH.
            ltac1:(rename H into HH).
            destruct p as [i d].
            apply list_find_Some in HH.
            destruct HH as [HH1 [? HH2]].
            subst d.
            apply flat_map_lookup_Some in HH1.
            destruct HH1 as [j [x [k [HH3 HH4]]]].
            apply map_lookup_Some in HH3.
            destruct HH3 as [y [H1y H2y]].
            subst x.
            unfold compile' in HH4.
            destruct y.
            {
                destruct k.
                {
                    left. do 6 (eexists).
                    rewrite elem_of_list_lookup.
                    split.
                    {
                        eexists. eapply H1y.
                    }
                    {
                        simpl in HH4. inversion HH4; subst; clear HH4.
                        reflexivity.
                    }
                }
                {
                    inversion HH4.
                }
            }
            {
                right.
                do 3 eexists.
                split.
                {
                    rewrite elem_of_list_lookup.
                    eexists. eapply H1y.
                }
                {
                    destruct k; inversion HH4; subst; clear HH4.
                    {
                        left. reflexivity.
                    }

                    destruct k; inversion H0; subst; clear H0.
                    {
                        right. reflexivity.
                    }
                }
            }
        }
        {
            inversion HH.
        }
    }
    {
        reflexivity.
    }
    Unshelve.
    intros ?. apply _.
Qed.

(*
Fixpoint frto_all_nonlast_states_satisfy
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory2 Act)
    (P : TermOver builtin_value -> Prop)
    (x y : TermOver builtin_value)
    (w : list Act)
    (r : rewrites_to_thy Γ x w y)
    :
    Prop
:=
    match r with
    | frto_base _ _ => True
    | frto_step _ t1 t2 t3 _ _ d _ _ r' =>
        P t1 /\
        frto_all_nonlast_states_satisfy Γ P _ _ _ r'
    end
.

Lemma split_frto_by_state_pred
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    (P : TermOver builtin_value -> Prop)
    (_dP : forall t, Decision (P t))
    (x z : TermOver builtin_value)
    (w : list Act)
    (r : flattened_rewrites_to_over Γ x w z)
    :
    (
    { w1 : list Act &
    { w2 : list Act &
    { y : TermOver builtin_value &
    { r1 : flattened_rewrites_to_over Γ x w1 y & 
        (
        (flattened_rewrites_to_over Γ y w2 z) *
        (w1 ++ w2 = w) *
        (frto_all_nonlast_states_satisfy Γ (fun arg => ~ (P arg)) _ _ _ r1) *
        (P y)
        )%type
    }
    } } }
    ) + ( frto_all_nonlast_states_satisfy Γ (fun arg => ~ (P arg)) _ _ _ r )
.
Proof.
Abort.

Lemma compile_correct_2
    {Σ : StaticModel}
    {Act : Set}
    {_AD : EqDecision Act}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable) 
    (D : MinusL_LangDef Act)
    (HcvD: continuationVariable ∉ vars_of D)
    (wfD : MinusL_LangDef_wf Act D)
    :
    ~ (invisible_act ∈ actions_of_ldef Act D) ->
    let Γ := compile invisible_act topSymbol cseqSymbol holeSymbol continuationVariable D in
    forall
        (lc ld rc rd : TermOver builtin_value)
        (w : list Act),
        (
            { w' : list Act & 
            ((w = (filter (fun x => x <> invisible_act) w')) *
            (* w <> [] /\ *)
            forall cont,
            flattened_rewrites_to_over Γ
                (downC topSymbol cseqSymbol lc ld cont)
                w'
                (downC topSymbol cseqSymbol rc rd cont)
            )%type
            }
        ) ->
        MinusL_rewrites Act D lc ld w rc rd
.
Proof.
Abort.

*)
            