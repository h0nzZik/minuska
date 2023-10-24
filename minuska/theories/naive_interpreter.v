
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
        (matches : Valuation -> Operand1 -> Operand2 -> bool)
        (matches_app_1 :
            Valuation ->
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            bool
        )
        (matches_app_2 :
            Valuation ->
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            bool
        )
        (ρ : Valuation)
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
            ρ
            app1
            app2
        && matches ρ o1 o2
    | ao_app_operand app1 o1, ao_app_ao app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            ρ
            app1
            app2
        && matches_app_1 ρ o1 o2
    | ao_app_ao app1 o1, ao_operator _ => false
    | ao_app_ao app1 o1, ao_app_operand app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            ρ
            app1
            app2
        && matches_app_2 ρ o1 o2
    | ao_app_ao app1 o1, ao_app_ao app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            ρ
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
            ρ
            o1
            o2
    end.

    Definition ApppliedOperatorOr'_matches_AppliedOperatorOr'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Valuation -> Operand1 -> Operand2 -> bool)
        (matches_app_1 :
            Valuation ->
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            bool
        )
        (matches_app_2 :
            Valuation ->
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            bool
        )
        (ρ : Valuation)
        (x : AppliedOperatorOr' Operator Operand1)
        (y : AppliedOperatorOr' Operator Operand2)
        : bool :=
    match x, y with
    | aoo_app _ _ app1, aoo_app _ _ app2 =>
        ApppliedOperator'_matches_AppliedOperator'
            Operator
            Operand1 Operand2
            matches matches_app_1 matches_app_2
            ρ
            app1 app2
    | aoo_app _ _ app1, aoo_operand _ _ o2 =>
        matches_app_2 ρ app1 o2
    | aoo_operand _ _ o1, aoo_app _ _ app2 =>
        matches_app_1 ρ o1 app2
    | aoo_operand _ _ o1, aoo_operand _ _ o2 =>
        matches ρ o1 o2
    end.

    Definition use_left (og1 og2: option GroundTerm): option GroundTerm :=
    match og1, og2 with
    | None, None => None
    | Some g1, None => Some g1
    | None, Some g2 => Some g2
    | Some g1, Some g2 => Some g1
    end.

    Definition valuations_compatible (ρ1 ρ2 : Valuation) : Prop
        := Forall (fun k => ρ1 !! k = ρ2 !! k) (elements (dom ρ1 ∩ dom ρ2))
    .

    Instance valautions_compatible_dec:
        forall ρ1 ρ2, Decision (valuations_compatible ρ1 ρ2)
    .
    Proof.
        intros.
        unfold valuations_compatible.
        ltac1:(solve_decision).
    Defined.

    (* TODO fix the case when ρ1 ≡ ρ2 ≡ {[x → 2]} *)
    Definition merge_valuations (ρ1 ρ2 : Valuation)
        : option Valuation :=
    if decide (valuations_compatible ρ1 ρ2)
    then
        Some (merge use_left ρ1 ρ2)
    else
        None
    .

    (* what if we match against `s x x` ?  *)
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
            (builtin_value_matches_BuiltinOrVar)
            (fun ρ' x y => false)
            (pure_GroundTerm_matches_BuiltinOrVar)
            ρ
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

    Definition vars_of_valuation (ρ : Valuation) : gset variable :=
        dom ρ
    .


    Lemma pure_GroundTerm_try_match_BuiltinOrVar_correct a b ρ:
        pure_GroundTerm_try_match_BuiltinOrVar a b = Some ρ ->
        pure_GroundTerm_matches_BuiltinOrVar ρ a b = true
    .
    Proof.
        unfold pure_GroundTerm_matches_BuiltinOrVar.
        unfold pure_GroundTerm_try_match_BuiltinOrVar.
        destruct b; intros H; inversion H.
        subst.
        unfold bool_decide.
        ltac1:(case_match); try reflexivity.
        clear H0 H.
        ltac1:(rewrite lookup_insert in n).
        ltac1:(contradiction n).
        reflexivity.
    Qed.

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

    Lemma builtin_value_try_match_BuiltinOrVar_correct
        b bov ρ:
        builtin_value_try_match_BuiltinOrVar b bov = Some ρ ->
        builtin_value_matches_BuiltinOrVar ρ b bov = true
        /\ ( (bov = bov_builtin b) \/ (∃ x, bov = bov_variable x /\ ρ !! x = Some (aoo_operand _ _ b)))
    .
    Proof.
        destruct bov; cbn;
          unfold is_left; repeat (ltac1:(case_match)); subst;
          unfold bool_decide; repeat (ltac1:(case_match)); subst;
          intros HH; inversion HH; subst; clear HH; try reflexivity;
          try ltac1:(congruence); subst; repeat split;
          try (solve [left; reflexivity]).
        all: try (
            ltac1:(rewrite lookup_insert in H);
            inversion H; subst; clear H;
            ltac1:(congruence)
        ).
        {
            ltac1:(rewrite lookup_insert in H).
            inversion H; subst; clear H.
            right.
            eexists.
            split>[reflexivity|].
            ltac1:(rewrite lookup_insert).
            reflexivity.
        }
    Qed.

    #[export]
    Instance Valuation_lookup : Lookup variable GroundTerm Valuation.
    Proof.
        apply gmap_lookup.
    Defined.
    
    Lemma merge_valuations_correct (ρ1 ρ2 ρ : Valuation):
        merge_valuations ρ1 ρ2 = Some ρ ->
        map_subseteq ρ1 ρ /\
        map_subseteq ρ2 ρ
    .
    Proof.
        unfold merge_valuations.
        unfold is_left.
        destruct (decide (valuations_compatible ρ1 ρ2)) as [Hcompat|Hnocompat]; intros H.
        {
            inversion H; subst; clear H.
            unfold valuations_compatible in Hcompat.
            rewrite Forall_forall in Hcompat; cbn.
            ltac1:(setoid_rewrite <- elem_of_list_In in Hcompat).
            ltac1:(setoid_rewrite elem_of_elements in Hcompat).
            unfold map_subseteq.
            unfold map_included.
            unfold map_relation.
            unfold option_relation.
            fold (@Valuation Σ) in *.
            fold (@Valuation_lookup) in *.
            split; intros i;
                destruct (ρ1 !! i) eqn:Hρ1i;
                destruct (ρ2 !! i) eqn:Hρ2i;
                destruct (merge use_left ρ1 ρ2 !! i) eqn:Hmergei;
                ltac1:(rewrite Hmergei);
                try (exact I);
                ltac1:(rewrite lookup_merge in Hmergei);
                unfold diag_None in Hmergei;
                specialize (Hcompat i);
                ltac1:(rewrite Hρ1i in Hmergei);
                ltac1:(rewrite Hρ2i in Hmergei);
                unfold use_left in Hmergei;
                ltac1:(simplify_eq /=);
                try reflexivity
            .
            ltac1:(ospecialize (Hcompat _)).
            {
                rewrite elem_of_intersection.
                do 2 ltac1:(rewrite elem_of_dom).
                split; eexists.
                {
                    apply Hρ1i.
                }
                {
                    apply Hρ2i.
                }
            }
            ltac1:(congruence).
        }
        {
            inversion H.
        }
    Qed.

    Lemma builtin_value_matches_BuiltinOrVar_monotone
        (ρ ρ' : Valuation)
        b bov:
        map_subseteq ρ ρ' ->
        builtin_value_matches_BuiltinOrVar ρ b bov = true ->
        builtin_value_matches_BuiltinOrVar ρ' b bov = true
    .
    Proof.
        destruct bov; cbn; auto with nocore.
        unfold map_subseteq,map_included,map_relation,option_relation.
        intros H.
        specialize (H x).
        unfold bool_decide.
        unfold Valuation,Valuation_lookup,GroundTerm,GroundTerm' in *.
        unfold Valuation_lookup in *.
        destruct (ρ !! x) eqn:Heq1, (ρ' !! x) eqn:Heq2; subst; auto.
    Qed.

    Lemma pure_GroundTerm_matches_BuiltinOrVar_monotone
        (ρ ρ' : Valuation)
        g bov:
        map_subseteq ρ ρ' ->
        pure_GroundTerm_matches_BuiltinOrVar ρ g bov ->
        pure_GroundTerm_matches_BuiltinOrVar ρ' g bov
    .
    Proof.
        unfold pure_GroundTerm_matches_BuiltinOrVar.
        destruct bov; cbn; auto with nocore.
        unfold map_subseteq,map_included,map_relation,option_relation.
        intros H.
        specialize (H x).
        unfold bool_decide.
        unfold Valuation,Valuation_lookup,GroundTerm,GroundTerm' in *.
        unfold Valuation_lookup in *.
        destruct (ρ !! x) eqn:Heq1, (ρ' !! x) eqn:Heq2; subst; auto.
    Qed.


    Lemma matches_monotone
        (ρ ρ' : Valuation)
        (a : AppliedOperator' symbol builtin_value)
        (b : AppliedOperator' symbol BuiltinOrVar)
        :
        map_subseteq ρ ρ' ->
        @ApppliedOperator'_matches_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_matches_BuiltinOrVar
            (fun _ _ _ => false)
            pure_GroundTerm_matches_BuiltinOrVar
            ρ a b = true ->

        @ApppliedOperator'_matches_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_matches_BuiltinOrVar
            (fun _ _ _ => false)
            pure_GroundTerm_matches_BuiltinOrVar
            ρ' a b = true
    .
    Proof.
        revert a.
        induction b; intros a HH1 HH2; destruct a; simpl in *;
            try assumption.
        {
            apply andb_true_iff in HH2.
            destruct HH2 as [HH21 HH22].
            rewrite IHb.
            cbn.
            eapply builtin_value_matches_BuiltinOrVar_monotone.
            { apply HH1. }
            { apply HH22. }
            { apply HH1. }
            { exact HH21. }
        }
        {
            apply andb_true_iff in HH2.
            destruct HH2 as [HH21 HH22].
            rewrite IHb.
            cbn.
            eapply pure_GroundTerm_matches_BuiltinOrVar_monotone.
            { apply HH1. }
            { apply HH22. }
            { apply HH1. }
            { exact HH21. }
        }
        {
            rewrite andb_comm in HH2.
            cbn in HH2.
            ltac1:(exfalso; congruence).
        }
        {
            apply andb_true_iff in HH2.
            destruct HH2 as [HH21 HH22].
            rewrite IHb1. rewrite IHb2. reflexivity.
            assumption. assumption. assumption. assumption.
        }
    Qed.

    Lemma merge_valuations_empty_r x:
        merge_valuations x ∅ = Some x
    .
    Proof.
        unfold merge_valuations.
        ltac1:(case_match).
        {
            clear H.
            apply f_equal.
            rewrite <- merge_Some.
            intros i.
            unfold use_left.
            ltac1:(case_match).
            {
                ltac1:(rewrite lookup_empty).
                reflexivity.
            }
            {
                ltac1:(rewrite lookup_empty).
                reflexivity.
            }
            reflexivity.
        }
        {
            unfold is_left in H.
            ltac1:(case_match).
            { inversion H. }
            ltac1:(exfalso).
            apply n.
            unfold Valuation.
            unfold valuations_compatible.
            ltac1:(rewrite dom_empty_L).
            rewrite intersection_empty_r_L.
            rewrite elements_empty.
            apply Forall_nil.
        }
    Qed.

    Lemma merge_valuations_empty_l x:
        merge_valuations ∅ x = Some x
    .
    Proof.
        unfold merge_valuations.
        ltac1:(case_match).
        {
            clear H.
            apply f_equal.
            rewrite <- merge_Some.
            intros i.
            unfold use_left.
            repeat ltac1:(case_match);
                try reflexivity.
            {
                ltac1:(rewrite lookup_empty in H).
                inversion H.
            }
            {
                ltac1:(rewrite lookup_empty in H).
                inversion H.
            }
            reflexivity.
        }
        {
            unfold is_left in H.
            ltac1:(case_match).
            { inversion H. }
            ltac1:(exfalso).
            apply n.
            unfold Valuation.
            unfold valuations_compatible.
            ltac1:(rewrite dom_empty_L).
            rewrite intersection_empty_l_L.
            rewrite elements_empty.
            apply Forall_nil.
        }
    Qed.

    Lemma ApppliedOperatorOr'_try_match_AppliedOperatorOr'_correct
        (ρ ρ' : Valuation)
        (a : AppliedOperator' symbol builtin_value)
        (b : AppliedOperator' symbol BuiltinOrVar)
        :
        map_subseteq ρ ρ' ->
        @ApppliedOperator'_try_match_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_try_match_BuiltinOrVar
            (fun _ _ => None)
            pure_GroundTerm_try_match_BuiltinOrVar
            a b = Some ρ ->

        @ApppliedOperator'_matches_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_matches_BuiltinOrVar
            (fun _ _ _ => false)
            pure_GroundTerm_matches_BuiltinOrVar
            ρ' a b = true
    .
    Proof.
        revert b ρ ρ'.
        induction a; intros b' ρ ρ' HH H; destruct b'; cbn in *; intros.
        {
            intros.
            unfold is_left in *.
            unfold bool_decide.
            repeat ltac1:(case_match); subst; simpl;
                try reflexivity; ltac1:(congruence).
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
        {
            rewrite bind_Some in H.
            destruct H as [x [H21 H22]].
            rewrite bind_Some in H22.
            destruct H22 as [x0 [H221 H222]].

            assert (H221' := H221).
            apply builtin_value_try_match_BuiltinOrVar_correct in H221.
            assert (H222' := H222).
            apply merge_valuations_correct in H222'.
            destruct H222' as [Hsub1 Hsub2].
            destruct H221 as [H2211 H2212].
            cbn.
            destruct H2212 as [HH1|HH2].
            {
                subst.
                cbn.
                unfold bool_decide.
                repeat ltac1:(case_match).
                rewrite andb_true_r.
                (*
                eapply matches_monotone.
                { apply HH. }
                *)
                clear e H.
                cbn in *.
                clear H2211.
                destruct (decide (b = b))>[|ltac1:(congruence)].
                cbn in *.
                inversion H221'; subst; clear H221'.
                clear e.
                rewrite merge_valuations_empty_r in H222.
                inversion H222; subst; clear H222.
                clear Hsub2.
                clear Hsub1.
                specialize (IHa b' ρ ρ' HH).
                apply IHa.
                apply H21.
                ltac1:(congruence).
            }
            {
                destruct HH2 as [x1 [HH3 HH4]].
                subst.
                cbn in *.
                inversion H221'; subst; clear H221'.
                ltac1:(rewrite lookup_insert in H2211).
                clear H2211.
                assert (Htmp: ρ' !! x1 = Some (aoo_operand symbol builtin_value b)).
                {
                    clear -Hsub2 HH.
                    unfold map_subseteq in *.
                    unfold map_included in *.
                    unfold map_relation in *.
                    unfold option_relation in *.
                    specialize (HH x1).
                    specialize (Hsub2 x1).
                    repeat ltac1:(case_match); subst;
                        ltac1:(rewrite lookup_insert in H);
                        inversion H; subst; clear H;
                        try assumption;
                        try ltac1:(contradiction).
                }
                unfold Valuation_lookup in *.
                rewrite Htmp.
                unfold bool_decide.
                ltac1:(case_match); try reflexivity; try ltac1:(congruence).
                clear e H.
                clear HH4.
                assert (Htmp2 := IHa b').
                remember (ApppliedOperator'_matches_AppliedOperator' symbol builtin_value
                    BuiltinOrVar builtin_value_matches_BuiltinOrVar
                    (λ (_ : Valuation) (_ : builtin_value) (_ : AppliedOperator'
                    symbol
                    BuiltinOrVar),
                    false)
                    pure_GroundTerm_matches_BuiltinOrVar)
                as f.
                remember (ApppliedOperator'_try_match_AppliedOperator' symbol
                    builtin_value BuiltinOrVar
                    builtin_value_try_match_BuiltinOrVar
                    (λ (_ : builtin_value) (_ : AppliedOperator' symbol
                    BuiltinOrVar),
                    None)
                    pure_GroundTerm_try_match_BuiltinOrVar)
                as g.
                apply Htmp2 with (ρ' := ρ') in H21.
                {
                    rewrite H21. reflexivity.
                }
                {
                    eapply transitivity.
                    { apply Hsub1. }
                    { apply HH. }
                }
            }
        }
        {
            rewrite bind_Some in H.
            destruct H as [x [H21 H22]].
            inversion H22.
        }
        {
            inversion H.
        }
        {
            rewrite bind_Some in H.
            destruct H as [x [H21 H22]].
            rewrite bind_Some in H22.
            destruct H22 as [x0 [H221 H222]].
            (* TODO: need a lemma about correctness of pure_GroundTerm_try_match_BuiltinOrVar *)
            apply pure_GroundTerm_try_match_BuiltinOrVar_correct in H221.
            assert (Hmv := H222).
            apply merge_valuations_correct in Hmv.
            destruct Hmv as [Hsub1 Hsub2].
            assert (Hxrho': map_subseteq x ρ').
            {
                eapply transitivity.
                apply Hsub1.
                apply HH.
            }
            apply pure_GroundTerm_matches_BuiltinOrVar_monotone with (ρ' := ρ') in H221.
            {
                rewrite H221.
                clear H221.
                remember (ApppliedOperator'_try_match_AppliedOperator' symbol
                    builtin_value BuiltinOrVar
                    builtin_value_try_match_BuiltinOrVar
                    (λ (_ : builtin_value) (_ : AppliedOperator' symbol
                    BuiltinOrVar),
                    None)
                    pure_GroundTerm_try_match_BuiltinOrVar)
                as f.
                specialize (IHa1 b' x ρ' Hxrho' H21).
                rewrite IHa1.
                reflexivity.
            }
            {
                eapply transitivity.
                apply Hsub2.
                apply HH.
            }
        }
        {
            rewrite bind_Some in H.
            destruct H as [x [H21 H22]].
            rewrite bind_Some in H22.
            destruct H22 as [x0 [H221 H222]].
            assert (Hsub := H222).
            apply merge_valuations_correct in Hsub.
            destruct Hsub as [Hsub1 Hsub2].
            assert (Hxρ' : map_subseteq x ρ').
            {
                eapply transitivity.
                apply Hsub1.
                apply HH.
            }
            assert (Hx0ρ' : map_subseteq x0 ρ').
            {
                eapply transitivity.
                apply Hsub2.
                apply HH.
            }
            remember (
                ApppliedOperator'_matches_AppliedOperator' symbol builtin_value
                BuiltinOrVar builtin_value_matches_BuiltinOrVar
                (λ (_ : Valuation) (_ : builtin_value) (_ : AppliedOperator'
                symbol
                BuiltinOrVar),
                false)
                pure_GroundTerm_matches_BuiltinOrVar )
            as f.
            remember (ApppliedOperator'_try_match_AppliedOperator' symbol
                builtin_value BuiltinOrVar
                builtin_value_try_match_BuiltinOrVar
                (λ (_ : builtin_value) (_ : AppliedOperator' symbol
                BuiltinOrVar),
                None)
                pure_GroundTerm_try_match_BuiltinOrVar)
            as g.
            apply andb_true_iff.
            ltac1:(naive_solver).
        }
        Unshelve.
        all: apply map_subseteq_po.
    Qed.

    Lemma builtin_value_try_match_BuiltinOrVar_complete a b ρ:
        builtin_value_matches_BuiltinOrVar ρ a b ->
        ∃ ρ',
            vars_of_valuation ρ' = (vars_of_BoV b) /\
            map_subseteq ρ' ρ /\
            builtin_value_try_match_BuiltinOrVar a b = Some ρ'
    .
    Proof.
        unfold builtin_value_matches_BuiltinOrVar.
        unfold builtin_value_try_match_BuiltinOrVar.
        unfold bool_decide.
        destruct b.
        {
            repeat ltac1:(case_match); subst; try ltac1:(congruence);
                intros _.
            {
                exists ∅.
                cbn.
                split>[reflexivity|].
                split>[|reflexivity].
                cbn.
                unfold Valuation.
                apply map_empty_subseteq.
            }
            {
                inversion H0.
            }
        }
        {
            destruct (ρ!!x) eqn:Hρx.
            {
                destruct a0.
                {
                    intros H; inversion H.
                }
                {
                    ltac1:(case_match).
                    {
                        intros _.
                        exists (<[x:=aoo_operand symbol builtin_value a]> ∅).
                        cbn.
                        unfold vars_of_valuation.
                        split.
                        {
                            ltac1:(rewrite insert_empty).
                            cbn.
                            unfold map_to_list.
                            unfold Valuation.
                            rewrite dom_singleton_L.
                            reflexivity.
                        }
                        split>[|reflexivity].
                        unfold map_subseteq.
                        unfold map_included.
                        unfold map_relation.
                        unfold option_relation.
                        intros i.
                        destruct (decide (i = x)).
                        {
                            subst.
                            ltac1:(rewrite lookup_insert).
                            clear H.
                            ltac1:(rewrite Hρx).
                            reflexivity.
                        }
                        {
                            ltac1:(rewrite lookup_insert_ne).
                            {
                                intros HContra; apply n; subst; reflexivity.
                            }
                            {
                                ltac1:(rewrite lookup_empty).
                                ltac1:(case_match); exact I.
                            }
                        }
                    }
                    {
                        intros H'; inversion H'.
                    }
                }
            }
            {
                intros H; inversion H.
            }
        }
    Qed.

    Lemma merge_use_left_subseteq (ρ1 ρ2 : Valuation):
        map_subseteq ρ1 ρ2 ->
        merge use_left ρ1 ρ2 = ρ2
    .
    Proof.
        unfold map_subseteq.
        unfold map_included.
        unfold map_relation.
        unfold option_relation.
        intros H.
        apply map_subseteq_po.
        {
            unfold Valuation.
            unfold Valuation_lookup.
            rewrite map_subseteq_spec.
            intros i x Hix.
            rewrite lookup_merge in Hix.
            unfold diag_None in Hix.
            unfold use_left in Hix.
            ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
            {
                specialize (H i).
                rewrite H0 in H.
                rewrite H1 in H.
                subst.
                reflexivity.
            }
            {
                specialize (H i).
                rewrite H0 in H.
                rewrite H1 in H.
                inversion H.
            }
        }
        {
            unfold Valuation.
            unfold Valuation_lookup.
            rewrite map_subseteq_spec.
            intros i x Hix.
            rewrite lookup_merge.
            unfold diag_None.
            unfold use_left.
            ltac1:(repeat case_match; simplify_eq/=; try reflexivity).
            specialize (H i).
            rewrite H1 in H.
            rewrite H0 in H.
            subst.
            reflexivity.
        }
    Qed.

    Lemma omap_Some (ρ : Valuation):
        omap [eta Some] ρ = ρ
    .
    Proof.
        rewrite <- map_fmap_alt.
        rewrite map_fmap_id.
        reflexivity.
    Qed.

    Lemma ApppliedOperatorOr'_try_match_AppliedOperatorOr'_complete
        (ρ : Valuation)
        (a : AppliedOperator' symbol builtin_value)
        (b : AppliedOperator' symbol BuiltinOrVar)
        :
        @ApppliedOperator'_matches_AppliedOperator'
            symbol _ builtin_value BuiltinOrVar
            builtin_value_matches_BuiltinOrVar
            (fun _ _ _ => false)
            pure_GroundTerm_matches_BuiltinOrVar
            ρ a b = true ->
        ∃ ρ',
            vars_of_valuation ρ' = vars_of_aosb b /\
            map_subseteq ρ' ρ /\
            @ApppliedOperator'_try_match_AppliedOperator'
                symbol _ builtin_value BuiltinOrVar
                builtin_value_try_match_BuiltinOrVar
                (fun _ _ => None)
                pure_GroundTerm_try_match_BuiltinOrVar
                a b = Some ρ'
    .
    Proof.
        remember (ApppliedOperator'_matches_AppliedOperator' symbol builtin_value
            BuiltinOrVar builtin_value_matches_BuiltinOrVar
            (λ (_ : Valuation) (_ : builtin_value) (_ : AppliedOperator'
            symbol
            BuiltinOrVar),
            false)
            pure_GroundTerm_matches_BuiltinOrVar)
        as f.
        remember (ApppliedOperator'_try_match_AppliedOperator' symbol
            builtin_value BuiltinOrVar
            builtin_value_try_match_BuiltinOrVar
            (λ (_ : builtin_value) (_ : AppliedOperator' symbol
            BuiltinOrVar),
            None)
            pure_GroundTerm_try_match_BuiltinOrVar)
        as g.

        revert ρ b.
        induction a; intros ρ b''.
        {
            subst f. cbn. unfold bool_decide.
            repeat ltac1:(case_match); subst;
                intros H; try (ltac1:(congruence)).
            clear H.
            cbn.
            unfold is_left.
            repeat ltac1:(case_match).
            {
                exists ∅.
                unfold vars_of_valuation.
                unfold Valuation.
                rewrite dom_empty_L.
                split>[reflexivity|].
                split>[|reflexivity].
                unfold Valuation.
                apply map_empty_subseteq.
            }
            { ltac1:(exfalso; congruence). }
            { ltac1:(exfalso; congruence). }
            { ltac1:(exfalso; congruence). }
        }
        {
            rewrite Heqf.
            rewrite Heqg.
            cbn.
            destruct b''.
            {
                intros H; inversion H.
            }
            {
                intros H.
                rewrite andb_true_iff in H.
                destruct H as [H1 H2].
                rewrite <- Heqf in H1.
                specialize (IHa ρ b'' H1).
                destruct IHa as [ρ' [IH0 [IH1 IH2]]].
                rewrite <- Heqg.
                apply builtin_value_try_match_BuiltinOrVar_complete in H2.
                destruct H2 as [ρ'' [Hρ''0 [Hρ''1 Hρ''2]]].
                rewrite IH2.
                cbn.
                rewrite Hρ''2.
                cbn.
                destruct b0.
                {
                    cbn in *.
                    unfold is_left in *.
                    destruct (decide (b = b0)).
                    {
                        subst. inversion Hρ''2; subst; clear Hρ''2.
                        cbn.
                        rewrite <- IH0.
                        exists ρ'.
                        split>[reflexivity|].
                        split.
                        { exact IH1. }
                        apply merge_valuations_empty_r.
                    }
                    {
                        inversion Hρ''2.
                    }
                }
                {
                    cbn in *.
                    inversion Hρ''2; subst; clear Hρ''2.
                    destruct (ρ' !! x) eqn:Hρ'x.
                    {
                        exists ρ'.
                        cbn.
                        repeat split.
                        {
                            unfold vars_of_valuation.
                            cbn.
                            unfold Valuation.
                            unfold Valuation_lookup.
                            rewrite <- IH0.
                            unfold vars_of_valuation.
                            clear -Hρ'x.
                            apply leibniz_equiv.
                            ltac1:(cut (x ∈ dom ρ')).
                            {
                                ltac1:(set_solver).
                            }
                            unfold Valuation.
                            unfold Valuation_lookup.
                            rewrite elem_of_dom.
                            exists g.
                            exact Hρ'x.
                        }
                        {
                            exact IH1.
                        }
                        {
                            (*clear -Hρ'x.*)
                            unfold merge_valuations.
                            unfold decide,is_left.
                            repeat ltac1:(case_match).
                            {
                                apply f_equal.
                                clear H0 H.
                                unfold valuations_compatible in *.
                                rewrite Forall_forall in v.
                                specialize (v x).
                                ltac1:(rewrite <- elem_of_list_In in v).
                                rewrite elem_of_elements in v.
                                rewrite elem_of_intersection in v.
                                ltac1:(do 2 rewrite elem_of_dom in v).
                                ltac1:(ospecialize (v _)).
                                split; eexists.
                                {
                                    apply Hρ'x.
                                }
                                {
                                    ltac1:(rewrite lookup_insert).
                                    reflexivity.
                                }
                                ltac1:(rewrite lookup_insert in v).
                                ltac1:(rewrite Hρ'x in v).
                                inversion v; subst; clear v.
                                clear Hρ''0.
                                unfold Valuation.
                                Check @insert_merge_r.
                                ltac1:(
                                    erewrite <- insert_merge_r
                                ).
                                rewrite merge_empty_r.
                                unfold use_left, compose.
                                cbn.
                                rewrite omap_Some.
                                rewrite insert_id.
                                { reflexivity. }
                                { apply Hρ'x. }
                                {
                                    unfold use_left.
                                    ltac1:(rewrite Hρ'x).
                                    reflexivity.
                                }
                            }
                            {
                                inversion H.
                            }
                            {
                                inversion H.
                            }
                            {
                                clear H0 H.
                                unfold valuations_compatible in *.
                                rewrite Forall_forall in n.
                                ltac1:(contradiction n).
                                clear n. intros x0.
                                rewrite <- elem_of_list_In.
                                rewrite elem_of_elements.
                                rewrite elem_of_intersection.
                                intros [HH1 HH2].
                                unfold Valuation.
                                unfold Valuation_lookup.
                                ltac1:(rewrite elem_of_dom in HH1).
                                ltac1:(rewrite elem_of_dom in HH2).
                                destruct HH1 as [g' Hg'].
                                destruct HH2 as [g'' Hg''].
                                destruct (decide (x = x0)).
                                {
                                    subst.
                                    ltac1:(rewrite lookup_insert in Hg'').
                                    inversion Hg''; subst; clear Hg''.
                                    ltac1:(rewrite Hρ'x in Hg').
                                    inversion Hg'; subst; clear Hg'.
                                    rewrite lookup_insert.
                                    clear -IH1 Hρ''1 Hρ'x.
                                    unfold map_subseteq in *.
                                    unfold map_included in *.
                                    unfold map_relation in *.
                                    unfold option_relation in *.
                                    specialize (IH1 x0).
                                    specialize (Hρ''1 x0).
                                    ltac1:(rewrite Hρ'x in IH1).
                                    ltac1:(rewrite lookup_insert in Hρ''1).
                                    unfold Valuation in *.
                                    unfold Valuation_lookup in *.
                                    destruct (ρ !! x0) eqn:Hρx0.
                                    {
                                        subst.
                                        exact Hρ'x.
                                    }
                                    {
                                        inversion IH1.
                                    }
                                }
                                {
                                    unfold Valuation in *.
                                    rewrite lookup_insert_ne in Hg''.
                                    {
                                        rewrite lookup_empty in Hg''.
                                        inversion Hg''.
                                    }
                                    {
                                        assumption.
                                    }
                                }
                            }
                        }
                    }
                    {
                        exists (<[x := aoo_operand _ _ b]>ρ').
                        cbn.
                        repeat split.
                        {
                            unfold vars_of_valuation.
                            cbn.
                            unfold Valuation.
                            unfold Valuation_lookup.
                            ltac1:(rewrite dom_insert_L).
                            ltac1:(set_solver).
                        }
                        {
                            unfold map_subseteq in *.
                            unfold map_included in *.
                            unfold map_relation in *.
                            unfold option_relation in *.
                            intros i.
                            unfold Valuation.
                            unfold Valuation_lookup.
                            destruct (decide (i = x)).
                            {
                                subst.
                                rewrite lookup_insert.
                                specialize (Hρ''1 x).
                                unfold Valuation in *.
                                rewrite lookup_insert in Hρ''1.
                                apply Hρ''1.
                            }
                            {
                                rewrite lookup_insert_ne.
                                {
                                    inversion Hρ''2; subst; clear Hρ''2.
                                    clear Hρ''0.
                                    unfold Valuation in *.
                                    unfold Valuation_lookup in *.
                                    apply IH1.
                                }
                                {
                                    apply nesym.
                                    assumption.
                                }
                            }
                        }
                    }
                    {
                        inversion Hρ''2; subst; clear Hρ''2.
                        clear Hρ''0.
                        unfold merge_valuations.
                        unfold is_left.
                        destruct (decide
                            (valuations_compatible ρ' (<[x:=aoo_operand symbol builtin_value b]> ∅)))
                        as [HCompat|HNotCompat].
                        {
                            apply f_equal.
                            unfold valuations_compatible in *.
                            rewrite Forall_forall in HCompat.
                            rewrite merge_use_left_subseteq.
                            ltac1:(setoid_rewrite <- elem_of_list_In in HCompat).
                            ltac1:(setoid_rewrite elem_of_elements in HCompat).
                            unfold Valuation.
                            apply map_subseteq_po.
                            {
                                apply insert_mono.
                                clear.
                                unfold Valuation in *.
                                unfold subseteq in *.
                                unfold map_subseteq in *.
                                unfold map_included in *.
                                unfold map_relation in *.
                                unfold option_relation in *.
                                intros x0.
                                repeat ltac1:(case_match);
                                    try (exact I).
                                {
                                    rewrite lookup_empty in H.
                                    inversion H.
                                }
                                {
                                    rewrite lookup_empty in H.
                                    inversion H.
                                }
                            }
                            {
                                unfold subseteq in *.
                                unfold map_subseteq in *.
                                unfold map_included in *.
                                unfold map_relation in *.
                                unfold option_relation in *.
                                intros x0.
                                
                                destruct (<[x:=aoo_operand symbol builtin_value b]> ρ' !! x0)
                                    eqn:Hx01.
                                {
                                    unfold Valuation_lookup in *. unfold Valuation in *.
                                    rewrite Hx01.
                                    destruct (<[x:=aoo_operand symbol builtin_value b]> ∅ !! x0)
                                        eqn:Hx02.
                                    {
                                        destruct (decide (x0 = x)).
                                        {
                                            subst.
                                            ltac1:(rewrite lookup_insert in Hx01).
                                            ltac1:(rewrite lookup_insert in Hx02).
                                            inversion Hx01. inversion Hx02. subst. reflexivity.
                                        }
                                        {
                                            rewrite lookup_insert_ne in Hx02.
                                            {
                                                rewrite lookup_empty in Hx02.
                                                inversion Hx02.
                                            }
                                            {
                                                apply nesym. apply n.
                                            }
                                        }
                                    }
                                    {
                                        destruct (decide (x0 = x)).
                                        {
                                            subst.
                                            ltac1:(rewrite lookup_insert in Hx01).
                                            ltac1:(rewrite lookup_insert in Hx02).
                                            inversion Hx02.
                                        }
                                        {
                                            rewrite lookup_insert_ne in Hx01.
                                            {
                                                clear Hx02.
                                                specialize (IH1 x0).
                                                rewrite Hx01 in IH1.
                                                destruct (ρ !! x0) eqn:Hρx0.
                                                {
                                                    subst.
                                                    specialize (Hρ''1 x).
                                                    rewrite lookup_insert in Hρ''1.
                                                    destruct (ρ!!x) eqn:Hρx.
                                                    {
                                                        subst.
                                                        Search ρ.
                                                    }
                                                    {

                                                    }
                                                    specialize (HCompat x).
                                                    ltac1:(ospecialize (HCompat _)).
                                                    {
                                                        rewrite elem_of_intersection.
                                                        do 2 (rewrite elem_of_dom).
                                                        split.
                                                        {
                                                            exists g0.
                                                            exact Hx01.
                                                        }
                                                        {

                                                        }
                                                    }
                                                }
                                                {
                                                    inversion IH1.
                                                }
                                            }
                                            {
                                                apply nesym. apply n.
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        {
                            ltac1:(exfalso).
                            apply HNotCompat.
                        }

                    }
                }
                (*
                assert (Hdisj: (ρ' ##ₘ ρ'')).
                {
                    cbn in *.
                    destruct b0; cbn in *.
                    {
                        ltac1:(case_match); cbn in *.
                        {
                            inversion Hρ''2.
                            subst.
                            clear Hρ''2.
                            unfold Valuation.
                            apply map_disjoint_empty_r.
                        }
                        {
                            inversion Hρ''2.
                        }
                    }
                    {
                        inversion Hρ''2;
                          subst; clear Hρ''2.
                        unfold vars_of_valuation in *.
                        cbn in *.
                        rewrite elements_singleton in Hρ''0.
                        ltac1:(rewrite insert_empty in Hρ''1).
                        ltac1:(rewrite insert_empty in Hρ''0).
                        ltac1:(rewrite map_to_list_singleton in Hρ''0).
                        inversion Hρ''0; subst; clear Hρ''0.
                        unfold map_subseteq in *.
                        unfold map_included in *.
                        unfold map_relation in *.
                        unfold option_relation in *.
                        specialize (Hρ''1 x).
                        rewrite lookup_singleton in Hρ''1.
                        ltac1:(case_match).
                        {
                            unfold Valuation.
                            apply map_disjoint_insert_r_2;
                                subst.
                            {
                                assert (IH1' := IH1 x).
                                repeat ltac1:(case_match); try reflexivity.
                                {
                                    inversion H; subst; clear H.
                                    clear IH1. (* trivial *)

                                }
                            }
                            {
                                apply map_disjoint_empty_r.
                            }
                        }
                        {
                            inversion Hρ''1.
                        }
                    }
                }
                *)
                destruct b0.
                {

                }
                {

                }
                (* I would somehow need [b ## b0]. *)
            }
            {

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
