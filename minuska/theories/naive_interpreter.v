
From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    flattened
    flatten
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.

(*
#[export]
Instance rr_satisfies_dec
    {Σ : Signature}
    (left_right : LR)
    (ρ : Valuation)
    (r : RewritingRule)
    (e : Element)
    : Decision (rr_satisfies left_right ρ r e)
.
Proof. Admitted.
*)

Section with_decidable_signature.
    Context
        {Σ : Signature}
        (up_dec : forall p e, Decision (builtin_unary_predicate_interp p e))
        (bp_dec : forall p e1 e2, Decision (builtin_binary_predicate_interp p e1 e2))
    .

    #[export]
    Instance val_satisfies_ap_dec
        ρ ap
        : Decision (val_satisfies_ap ρ ap)
    .
    Proof.
        destruct ap; cbn; repeat (ltac1:(case_match));
            try (solve[right; intros []]).
        {
            apply _.
        }
        {
            apply _.
        }
    Defined.

    #[export]
    Instance val_satisfies_c_dec
        ρ c
        : Decision (val_satisfies_c ρ c)
    .
    Proof.
        revert ρ.
        induction c; intros ρ; cbn.
        { left. exact I. }
        { apply _. }
        { apply and_dec; auto with nocore. }
        { apply not_dec. apply IHc. }
    Defined.

    Fixpoint ApppliedOperator'_matches_AppliedOperator'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Operand1 -> Operand2 -> bool)
        (matches_app_1 :
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            bool
        )
        (matches_app_2 :
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            bool
        )
        (x : AppliedOperator' Operator Operand1)
        (y : AppliedOperator' Operator Operand2)
        : bool :=
    match x, y with
    | ao_operator a1, ao_operator a2 =>
        bool_decide (a1 = a2)
    | ao_operator _, ao_app_operand _ _ => false
    | ao_operator _, ao_app_ao _ _ => false
    | ao_app_operand _ _ , ao_operator _ => false
    | ao_app_operand app1 o1, ao_app_operand app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2
        && matches o1 o2
    | ao_app_operand app1 o1, ao_app_ao app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2
        && matches_app_1 o1 o2
    | ao_app_ao app1 o1, ao_operator _ => false
    | ao_app_ao app1 o1, ao_app_operand app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2
        && matches_app_2 o1 o2
    | ao_app_ao app1 o1, ao_app_ao app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2
        &&
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            o1
            o2
    end.

    Definition ApppliedOperatorOr'_matches_AppliedOperatorOr'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Operand1 -> Operand2 -> bool)
        (matches_app_1 :
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            bool
        )
        (matches_app_2 :
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            bool
        )
        (x : AppliedOperatorOr' Operator Operand1)
        (y : AppliedOperatorOr' Operator Operand2)
        : bool :=
    match x, y with
    | aoo_app _ _ app1, aoo_app _ _ app2 =>
        ApppliedOperator'_matches_AppliedOperator'
            Operator
            Operand1 Operand2
            matches matches_app_1 matches_app_2
            app1 app2
    | aoo_app _ _ app1, aoo_operand _ _ o2 =>
        matches_app_2 app1 o2
    | aoo_operand _ _ o1, aoo_app _ _ app2 =>
        matches_app_1 o1 app2
    | aoo_operand _ _ o1, aoo_operand _ _ o2 =>
        matches o1 o2
    end.

    Definition use_left (og1 og2: option GroundTerm): option GroundTerm :=
    match og1, og2 with
    | None, None => None
    | Some g1, None => Some g1
    | None, Some g2 => Some g2
    | Some g1, Some g2 => Some g1
    end.

    Definition merge_valuations (ρ1 ρ2 : Valuation)
        : option Valuation :=
    if decide (ρ1 ## ρ2) then Some (merge use_left ρ1 ρ2) else None.

    Fixpoint ApppliedOperator'_try_match_AppliedOperator'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Operand1 -> Operand2 -> option Valuation)
        (matches_app_1 :
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            option Valuation
        )
        (matches_app_2 :
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            option Valuation
        )
        (x : AppliedOperator' Operator Operand1)
        (y : AppliedOperator' Operator Operand2)
        : option Valuation :=
    match x, y with
    | ao_operator a1, ao_operator a2 =>
        if decide (a1 = a2) then Some ∅ else None
    | ao_operator _, ao_app_operand _ _ => None
    | ao_operator _, ao_app_ao _ _ => None
    | ao_app_operand _ _ , ao_operator _ => None
    | ao_app_operand app1 o1, ao_app_operand app2 o2 =>
        ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2;
        ρ2 ← matches o1 o2;
        merge_valuations ρ1 ρ2

    | ao_app_operand app1 o1, ao_app_ao app2 o2 =>
        ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2 ;
        ρ2 ← matches_app_1 o1 o2;
        merge_valuations ρ1 ρ2

    | ao_app_ao app1 o1, ao_operator _ => None

    | ao_app_ao app1 o1, ao_app_operand app2 o2 =>
        ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2 ;
        ρ2 ← matches_app_2 o1 o2;
        merge_valuations ρ1 ρ2

    | ao_app_ao app1 o1, ao_app_ao app2 o2 =>
        ρ1 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            app1
            app2 ;
        ρ2 ← ApppliedOperator'_try_match_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            o1
            o2 ;
        merge_valuations ρ1 ρ2
    end.

    Definition ApppliedOperatorOr'_try_match_AppliedOperatorOr'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Operand1 -> Operand2 -> option Valuation)
        (matches_app_1 :
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            option Valuation
        )
        (matches_app_2 :
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            option Valuation
        )
        (x : AppliedOperatorOr' Operator Operand1)
        (y : AppliedOperatorOr' Operator Operand2)
        : option Valuation :=
    match x, y with
    | aoo_app _ _ app1, aoo_app _ _ app2 =>
        ApppliedOperator'_try_match_AppliedOperator'
            Operator
            Operand1 Operand2
            matches matches_app_1 matches_app_2
            app1 app2
    | aoo_app _ _ app1, aoo_operand _ _ o2 =>
        matches_app_2 app1 o2
    | aoo_operand _ _ o1, aoo_app _ _ app2 =>
        matches_app_1 o1 app2
    | aoo_operand _ _ o1, aoo_operand _ _ o2 =>
        matches o1 o2
    end.

    Definition builtin_value_matches_BuiltinOrVar
        (ρ : Valuation)
        : builtin_value -> BuiltinOrVar -> bool :=
    fun b bv =>
    match bv with
    | bov_builtin b' => bool_decide (b = b')
    | bov_variable x =>
        match ρ !! x with
        | None => false
        | Some (aoo_app _ _ _) => false
        | Some (aoo_operand _ _ b') => bool_decide (b = b')
        end
    end.

    Definition builtin_value_try_match_BuiltinOrVar:
        builtin_value -> BuiltinOrVar -> option Valuation :=
    fun b bv =>
    match bv with
    | bov_builtin b' => if (decide (b = b')) then Some ∅ else None
    | bov_variable x => Some (<[x := (aoo_operand _ _ b)]>∅)
    end.

    Definition builtin_value_matches_pure_OpenTerm
        (ρ : Valuation)
        : builtin_value -> OpenTerm -> bool :=
    fun b t =>
    match t with
    | aoo_app _ _ _ => false
    | aoo_operand _ _ (bov_variable x) =>
        match ρ !! x with
        | None => false
        | Some (aoo_app _ _ _) => false
        | Some (aoo_operand _ _ b') => bool_decide (b = b')
        end
    | aoo_operand _ _ (bov_builtin b') =>
        bool_decide (b = b')
    end.

    Definition pure_GroundTerm_matches_BuiltinOrVar
        (ρ : Valuation)
        : AppliedOperator' symbol builtin_value -> BuiltinOrVar -> bool
    := fun t bov =>
    match bov with
    | bov_builtin b => false
    | bov_variable x =>
        bool_decide (ρ !! x = Some (aoo_app _ _ t))
    end.

    Definition pure_GroundTerm_try_match_BuiltinOrVar:
        AppliedOperator' symbol builtin_value -> BuiltinOrVar -> option Valuation
    := fun t bov =>
    match bov with
    | bov_builtin b => None
    | bov_variable x =>
        Some (<[x := (aoo_app _ _ t)]>∅)
    end.

    Definition GroundTerm_matches_OpenTerm
        (ρ : Valuation):
        GroundTerm -> OpenTerm -> bool :=
        ApppliedOperatorOr'_matches_AppliedOperatorOr'
            symbol
            builtin_value
            BuiltinOrVar
            (builtin_value_matches_BuiltinOrVar ρ)
            (fun x y => false)
            (pure_GroundTerm_matches_BuiltinOrVar ρ)
    .

    Definition GroundTerm_try_match_OpenTerm:
        GroundTerm -> OpenTerm -> option Valuation :=
        ApppliedOperatorOr'_try_match_AppliedOperatorOr'
            symbol
            builtin_value
            BuiltinOrVar
            (builtin_value_try_match_BuiltinOrVar)
            (fun x y => None)
            (pure_GroundTerm_try_match_BuiltinOrVar)
    .
    
    Definition evaluate_sc
        (ρ : Valuation)
        (sc : SideCondition)
        : bool :=
    match sc with
    | sc_constraint c =>
        bool_decide (val_satisfies_c ρ c)
    | sc_match x φ =>
        match ρ !! x with
        | None => false
        | Some g => GroundTerm_matches_OpenTerm ρ g φ
        end
    end.

    Definition evaluate_rhs_pattern
            (ρ : Valuation)
            (φ : AppliedOperatorOr' symbol Expression)
            : option GroundTerm :=
        let f : Expression -> option GroundTerm
            := (Expression_evaluate ρ) in
        let fφ  : AppliedOperatorOr' symbol (option GroundTerm)
            := f <$> φ in 
        let cfφ : option (AppliedOperatorOr' symbol GroundTerm)
            := AppliedOperatorOr'_collapse_option fφ in
        cfφ' ← cfφ;
        let flat := AppliedOperatorOr'_symbol_A_to_OpenTermB id cfφ' in
        Some flat
    .

    Definition rewrite_with
        (r : FlattenedRewritingRule)
        (g : GroundTerm)
        : option GroundTerm
    :=
        ρ ← GroundTerm_try_match_OpenTerm g (fr_from r);
        if decide (Forall (evaluate_sc ρ) (fr_scs r)) then
            evaluate_rhs_pattern ρ (fr_to r)
        else None
    .

    (*
    Lemma Expression_evaluate_Some_app
        ρ z aoxy:
    Expression_evaluate ρ z = Some (aoo_app symbol builtin_value aoxy) ->
    z = ft_element (aoo_app symbol builtin_value aoxy)
    .
    Proof.
        revert aoxy.
        induction z; intros aoxy H; cbn.
        {
            inversion H. reflexivity.
        }
        {
            cbn in H.
        }

    Qed.
    *)


    Lemma evaluate_rhs_pattern_correct
        (φ : RhsPattern)
        (ρ : Valuation)
        (g : GroundTerm)
        : evaluate_rhs_pattern ρ φ = Some g <->
        GroundTerm_satisfies_RhsPattern ρ g φ
    .
    Proof.
        unfold evaluate_rhs_pattern.
        rewrite bind_Some.
        
        ltac1:(
            under [fun e => _]functional_extensionality => e
        ).
        {
            ltac1:(rewrite inj_iff).
            ltac1:(over).
        }
        unfold GroundTerm_satisfies_RhsPattern.
        destruct φ; cbn.
        {
            cbn.
            ltac1:(
                under [fun e => _]functional_extensionality => e
            ).
            {
                ltac1:(rewrite bind_Some).
                ltac1:(
                    under [fun e' => _]functional_extensionality => e'
                ).
                {
                    ltac1:(rewrite inj_iff).
                    ltac1:(over).
                }
                ltac1:(over).
            }
            destruct g; cbn.
            {
                rewrite <- aoxyo_satisfies_aoxzo_comp_iff.
                cbn.
                rewrite -> aoxy_satisfies_aoxz_comp_iff.

                split; intros H.
                {
                    destruct H as [e H].
                    destruct H as [H1 H2].
                    destruct H1 as [e' [H11 H12]].
                    cbn in *.
                    subst.
                    cbn in *.
                    inversion H2; subst; clear H2.
                    cbn in *.
                    inversion H11; subst; clear H11.
                    revert e' H0.
                    induction ao; intros e' H0.
                    {
                        cbn in *.
                        inversion H0; subst; clear H0.
                        constructor.
                    }
                    {
                        cbn in *.
                        rewrite bind_Some in H0.
                        destruct H0 as [x [H1 H2]].
                        rewrite bind_Some in H2.
                        destruct H2 as [x0 H2].
                        destruct H2 as [H2 H3].
                        inversion H3; subst; clear H3.
                        cbn.
                        destruct x0.
                        {
                            constructor.
                            cbn in *.
                            apply IHao.
                            apply H1.
                            cbn.
                            apply H2.
                        }
                        {
                            constructor.
                            cbn in *.
                            apply IHao.
                            apply H1.
                            cbn.
                            apply H2.
                        }
                    }
                    {
                        cbn in *.
                        rewrite bind_Some in H0.
                        destruct H0 as [x [H1 H2]].
                        rewrite bind_Some in H2.
                        destruct H2 as [x0 H2].
                        destruct H2 as [H2 H3].
                        inversion H3; subst; clear H3.
                        specialize (IHao1 _ H1).
                        specialize (IHao2 _ H2).
                        cbn.
                        constructor; assumption.
                    }
                }
                {
                    remember (fun (v:builtin_value) (e':Expression) =>
                        match Expression_evaluate ρ e' with
                        | Some v' => v'
                        | None => aoo_operand _ _ v
                        end
                    ) as zipper.
                    remember (fun (s1 s2 : symbol) => s1) as symleft.
                    remember (fun (g : AppliedOperator' symbol builtin_value) (e' : Expression) =>
                        (aoo_app symbol _ g)
                    ) as f1.
                    remember (fun (b : builtin_value) (et : AppliedOperator' symbol Expression) =>
                        (aoo_operand symbol _ b)
                    ) as f2.
                    remember (AppliedOperator'_zipWith symleft zipper f1 f2 ao0 ao) as zipped.
                    exists (aoo_app _ _ zipped).
                    cbn.
                    split.
                    {
                        exists zipped.
                        subst.
                        repeat constructor.
                        clear -H.


                        induction H.
                        {
                            cbn.
                            reflexivity.
                        }
                        {
                            cbn in H0.
                            cbn.
                            rewrite bind_Some.
                            cbn.
                            ltac1:(
                                under [fun e => _]functional_extensionality => e
                            ).
                            {
                                ltac1:(rewrite bind_Some).
                                ltac1:(
                                    under [fun e' => _]functional_extensionality => e'
                                ).
                                {
                                    ltac1:(rewrite inj_iff).
                                    ltac1:(over).
                                }
                                ltac1:(over).
                            }
                            cbn in *.
                            eexists.
                            split>[apply IHaoxy_satisfies_aoxz|].
                            eexists.
                            split>[apply H0|].
                            apply f_equal.
                            rewrite H0.
                            reflexivity.
                        }
                        {
                            cbn in H0.
                            cbn.
                            rewrite bind_Some.
                            cbn in *.
                            ltac1:(
                                under [fun e => _]functional_extensionality => e
                            ).
                            {
                                ltac1:(rewrite bind_Some).
                                ltac1:(
                                    under [fun e' => _]functional_extensionality => e'
                                ).
                                {
                                    ltac1:(rewrite inj_iff).
                                    ltac1:(over).
                                }
                                ltac1:(over).
                            }
                            cbn in *.
                            eexists.
                            split>[apply IHaoxy_satisfies_aoxz|].
                            eexists.
                            split>[apply H0|].
                            reflexivity.
                        }
                        {
                            cbn in H0.
                            cbn.
                            rewrite bind_Some.
                            cbn in *.
                            ltac1:(
                                under [fun e => _]functional_extensionality => e
                            ).
                            {
                                ltac1:(rewrite bind_Some).
                                ltac1:(
                                    under [fun e' => _]functional_extensionality => e'
                                ).
                                {
                                    ltac1:(rewrite inj_iff).
                                    ltac1:(over).
                                }
                                ltac1:(over).
                            }
                            cbn in *.
                            eexists.
                            split>[apply IHaoxy_satisfies_aoxz1|].
                            eexists.
                            split>[apply IHaoxy_satisfies_aoxz2|].
                            reflexivity.
                        }
                    }
                    {
                        subst. cbn.
                        apply f_equal.
                        induction H.
                        {
                            cbn. reflexivity.
                        }
                        {
                            cbn in *.
                            rewrite H0.
                            rewrite IHaoxy_satisfies_aoxz.
                            reflexivity.
                        }
                        {
                            cbn in *.
                            rewrite IHaoxy_satisfies_aoxz.
                            reflexivity.
                        }
                        {
                            cbn in *.
                            rewrite IHaoxy_satisfies_aoxz1.
                            rewrite IHaoxy_satisfies_aoxz2.
                            reflexivity.
                        }
                    }
                }
            }
            {
                rewrite <- aoxyo_satisfies_aoxzo_comp_iff.
                cbn.
                split; intros H.
                {
                    destruct H as [e H].
                    destruct H as [H1 H2].
                    destruct H1 as [e' [H11 H12]].
                    subst. cbn in *.
                    inversion H2.
                }
                {
                    inversion H.
                }
            }
        }
        {
            ltac1:(
                under [fun e => _]functional_extensionality => e
            ).
            {
                ltac1:(rewrite bind_Some).
                ltac1:(
                    under [fun e' => _]functional_extensionality => e'
                ).
                {
                    ltac1:(rewrite inj_iff).
                    ltac1:(over).
                }
                ltac1:(over).
            }
            ltac1:(rewrite -aoxyo_satisfies_aoxzo_comp_iff).
            cbn.
            destruct g; cbn.
            {
                split; intros H.
                {
                    destruct H as [e H].
                    destruct H as [[e' [H'1 H'2]] H].
                    subst.
                    cbn in H.
                    subst.
                    assumption.
                }
                {
                    eexists.
                    split.
                    {
                        eexists. split>[|reflexivity].
                        apply H.
                    }
                    {
                        cbn. reflexivity.
                    }
                }
            }
            {
                split; intros H.
                {
                    destruct H as [e H].
                    destruct H as [[e' [H'1 H'2]] H].
                    subst.
                    cbn in H.
                    subst.
                    assumption.
                }
                {
                    eexists.
                    split.
                    {
                        eexists. split>[|reflexivity].
                        apply H.
                    }
                    {
                        cbn. reflexivity.
                    }
                }
            }
        }
    Qed.

    Fixpoint rhs_evaluate_rule
        (ρ : Valuation)
        (r : RewritingRule)
        : option Element :=
    match r with
    | rr_local_rewrite lr =>
        evaluate_rhs_pattern ρ (lr_to lr)
    | rr_builtin b => Some (el_builtin b)
    | rr_sym s => Some (el_appsym (aps_operator s))
    | rr_app r1 r2 =>
        let oe1 := rhs_evaluate_rule ρ r1 in
        let oe2 := rhs_evaluate_rule ρ r2 in
        match oe1,oe2 with
        | Some (el_appsym aps1), Some (el_appsym aps2) =>
            Some (el_appsym (aps_app_aps aps1 aps2))
        | Some (el_appsym aps1), Some (el_builtin b) =>
            Some (el_appsym (aps_app_operand aps1 b))
        | _,_ => None
        end
    | rr_var x => ρ !! x
    | rr_requires r' _ => rhs_evaluate_rule ρ r'
    | rr_requires_match r' _ _ => rhs_evaluate_rule ρ r'
    end
    .


    Lemma rhs_evaluate_rule_correct_1
        (r : RewritingRule)
        (ρ : Valuation)
        (e : Element)
        : 
        rhs_evaluate_rule ρ r = Some e ->
        rr_satisfies LR_Right ρ r e
    .
    Proof.
        {
            revert e. revert ρ.
            induction r; intros ρ e Heval.
            {
                destruct e;
                ltac1:(simp rr_satisfies);
                cbn in Heval;
                destruct lr; cbn in *;
                apply evaluate_rhs_pattern_correct;
                exact Heval.
            }
            all: cbn in Heval; ltac1:(simplify_eq /=); auto with nocore.
            all: ltac1:(simp rr_satisfies); try reflexivity.
            all: (repeat (ltac1:(case_match))); ltac1:(simplify_eq /=).
            all: ltac1:(simp rr_satisfies); try ltac1:(naive_solver).
            {
                unfold rr_satisfies_unfold_clause_8.
                destruct (ρ !! v) eqn:Hv; ltac1:(naive_solver).
            }
        }
    Qed.

    Lemma rhs_evaluate_rule_correct_2
        (r : RewritingRule)
        (ρ : Valuation)
        (e : Element)
        : 
            rr_satisfies LR_Right ρ r e ->
            rhs_evaluate_rule ρ r = Some e
    .
    Proof.
        intros Hsatr.
        ltac1:(funelim (rr_satisfies LR_Right ρ r e));
            cbn.
        {
            apply evaluate_rhs_pattern_correct.
            assumption.
        }
        all: ltac1:(simp rr_satisfies in Hsatr).
        all: ltac1:(simplify_eq /=).
        all: try reflexivity.
        all: try ltac1:(contradiction).
        {
            erewrite H by ltac1:(naive_solver);
            erewrite H0 by ltac1:(naive_solver);
            reflexivity.
        }
        {
            erewrite H by ltac1:(naive_solver);
            erewrite H0 by ltac1:(naive_solver);
            reflexivity.
        }
        {
            ltac1:(simp rr_satisfies in Heqcall).
            apply H.
            apply Hsatr.
        }
        {
            apply H.
            rewrite Heq in Hsatr.
            unfold rr_satisfies_unfold_clause_8 in Hsatr.
            apply Hsatr.
        }{
            apply H.
            rewrite Heq in Hsatr.
            unfold rr_satisfies_unfold_clause_8 in Hsatr.
            apply Hsatr.
        }
    Qed.

    Definition lhs_match_one
        (e : Element)
        (r : RewritingRule)
        : option Valuation
    .
    Admitted.

    Lemma lhs_match_one_Some
        (e : Element)
        (r : RewritingRule)
        (ρ : Valuation)
        :
        lhs_match_one e r = Some ρ <->
        rr_satisfies LR_Left ρ r e
    .
    Proof. Admitted.

    Lemma lhs_match_one_None
        (e : Element)
        (r : RewritingRule)
        :
        lhs_match_one e r = None <-> 
        ~ exists (ρ : Valuation),
            rr_satisfies LR_Left ρ r e
    .
    Proof.
    Admitted.


    Definition thy_lhs_match_one
        (e : Element)
        (Γ : RewritingTheory)
        : option (RewritingRule * Valuation)%type
        := let vs : list (option Valuation) := lhs_match_one e <$> Γ in
        let found : option (nat * option Valuation) := list_find is_Some vs in
        match found with
        | None => None
        | Some (_, None) => None
        | Some (n, Some v) => (
            match Γ !! n with
            | Some r => Some (r, v)
            | None => None
            end)
        end
    .

    Lemma thy_lhs_match_one_None
        (e : Element)
        (Γ : RewritingTheory)
        :
        thy_lhs_match_one e Γ = None ->
        ~ exists (r : RewritingRule) (ρ : Valuation),
            r ∈ Γ /\ rr_satisfies LR_Left ρ r e
    .
    Proof.
        unfold thy_lhs_match_one.
        intros H [r [ρ [Hin HContra]]].
        destruct (list_find is_Some (lhs_match_one e <$> Γ)) eqn:Heqfound.
        {
            destruct p as [n oρ].
            rewrite list_find_Some in Heqfound.
            ltac1:(destruct Heqfound as [Hfound [HSome HFirst]]).
            destruct oρ.
            {
                subst. clear HFirst.
                destruct (Γ !! n) eqn:Heq.
                { inversion H. }
                clear H. clear HSome.
                rewrite list_lookup_fmap in Hfound.
                ltac1:(rewrite Heq in Hfound).
                cbn in Hfound.
                inversion Hfound.
            }
            {
                inversion HSome. inversion H0.
            }
        }
        {
            clear H.
            rewrite list_find_None in Heqfound.
            rewrite Forall_forall in Heqfound.
            specialize (Heqfound (Some ρ)).
            ltac1:(rewrite elem_of_list_fmap in Heqfound).
            ltac1:(feed specialize Heqfound).
            {
                exists r.
                split.
                {
                    symmetry.
                    apply lhs_match_one_Some.
                    exact HContra.
                }
                {
                    exact Hin.
                }
            }
            {
                unfold is_Some.
                exists ρ. reflexivity.
            }
            exact Heqfound.
        }
    Qed.


    Lemma thy_lhs_match_one_Some
        (e : Element)
        (Γ : RewritingTheory)
        (r : RewritingRule)
        (ρ : Valuation)
        :
        thy_lhs_match_one e Γ = Some (r, ρ) ->
        r ∈ Γ /\ rr_satisfies LR_Left ρ r e
    .
    Proof.
        intros H.
        unfold thy_lhs_match_one in H.
        unfold is_Some in H.
        (repeat ltac1:(case_match)); subst.
        {
            inversion H; subst; clear H.
            ltac1:(rewrite list_find_Some in H0).
            ltac1:(rewrite list_lookup_fmap in H0).
            ltac1:(rewrite H3 in H0).
            ltac1:(rewrite fmap_Some in H0).
            ltac1:(destruct_and!).
            destruct_ex!.
            ltac1:(destruct_and!).
            ltac1:(simplify_eq /=).
            symmetry in H0.
            ltac1:(rewrite lhs_match_one_Some in H0).
            split>[()|apply H0].
            apply elem_of_list_lookup_2 in H3.
            exact H3.
        }
        {
            inversion H.
        }
        {
            inversion H.
        }
        {
            inversion H.
        }
    Qed.

    Lemma weakly_well_defined_baked_in ρ r e:
        rr_satisfies LR_Left ρ r e ->
        exists e', rr_satisfies LR_Right ρ r e'
    .
    Proof.
        intros H.
        ltac1:(funelim (rr_satisfies LR_Left ρ r e));
            ltac1:(simp rr_satisfies in H).
        {
            
        }
    Qed.

    Definition naive_interpreter
        (Γ : RewritingTheory)
        (e : Element)
        : option Element
    :=
        let oρ : option (RewritingRule*Valuation) := thy_lhs_match_one e Γ in
        match oρ with
        | None => None
        | Some (r,ρ) => (rhs_evaluate_rule ρ r)
        end
    .

    Lemma naive_interpreter_sound
        (Γ : RewritingTheory)
     : Interpreter_sound Γ (naive_interpreter Γ).
    Proof.
        split.
        {
            unfold naive_interpreter.
            unfold Interpreter_sound.
            unfold stuck,not_stuck.
            intros e Hstuck.
            destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
            {
                destruct p as [r ρ].
                {
                    apply thy_lhs_match_one_Some in Hmatch.
                    destruct Hmatch as [Hin Hsat].
                    ltac1:(rewrite -lhs_match_one_Some in Hsat).
                    unfold rewriting_relation, rewrites_to in Hstuck.
                    destruct (rhs_evaluate_rule ρ r) eqn:Heval; cbn in *.
                    {
                        apply lhs_match_one_Some in Hsat.
                        apply rhs_evaluate_rule_correct_1 in Heval.
                        ltac1:(exfalso).
                        apply Hstuck. clear Hstuck.
                        unfold rewrites_in_valuation_to.
                        exists e0.
                        exists r.
                        split.
                        { exact Hin. }
                        exists ρ.
                        split; assumption.
                    }
                    {
                        reflexivity.
                    }
                }
            }
            {
                reflexivity.
            }
        }
        {
            intros e Hnotstuck.
            unfold naive_interpreter.
            destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
            {
                destruct p as [r ρ]; cbn in *.
                apply thy_lhs_match_one_Some in Hmatch.
                destruct Hmatch as [Hin Hsat].
                destruct (rhs_evaluate_rule ρ r) eqn:Heval.
                {
                    exists e0. reflexivity.
                }
                {
                    ltac1:(exfalso).
                    unfold thy_weakly_well_defined in Hwwd.
                    specialize (Hwwd r Hin).
                    unfold rule_weakly_well_defined in Hwwd.
                    specialize (Hwwd e ρ Hsat).
                    destruct Hwwd as [e' Hsate'].
                    apply evaluate_rhs_rule_correct. in Heval.
                    Search rhs_evaluate_rule.
                }
                Search rhs_evaluate_rule.
            }
        }
    Qed.

End with_decidable_signature.
