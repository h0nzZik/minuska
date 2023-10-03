
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
.

(*
    

*)

Module Syntax.


    
    Section vars_of.

        Definition vars_of_AP
            {Σ : Signature}
            (ap : AtomicProposition)
            : gset variable :=
        match ap with
        | ap1 _ x => {[x]}
        | ap2 _ x y => {[x;y]}
        end.

        Fixpoint vars_of_Constraint
            { Σ : Signature }
            (c : Constraint)
            : gset variable :=
        match c with
        | c_True => ∅
        | c_atomic ap => vars_of_AP ap
        | c_and c1 c2 => vars_of_Constraint c1 ∪ vars_of_Constraint c2
        | c_not c' => vars_of_Constraint c'
        end.

        Fixpoint vars_of_aosb
            {Σ : Signature}
            (o : AppliedOperator' symbol BuiltinOrVar)
            : gset variable :=
        match o with
        | ao_operator _ => ∅
        | ao_app_operand o' (bov_builtin _) => vars_of_aosb o'
        | ao_app_operand o' (bov_variable x) => {[x]} ∪ vars_of_aosb o'
        | ao_app_ao o1 o2 => vars_of_aosb o1 ∪ vars_of_aosb o2
        end.

        Fixpoint vars_of_BasicPattern
            {Σ : Signature}
            (φ : BasicPattern)
            : gset variable :=
        match φ with
        | ao_operator s => ∅
        | ao_app_operand φ' (bov_variable x)
            => {[x]} ∪ vars_of_BasicPattern φ'
        | ao_app_operand φ' (bov_builtin _)
            => vars_of_BasicPattern φ'
        | ao_app_ao φ1 φ2
            => vars_of_BasicPattern φ1 ∪ vars_of_BasicPattern φ2
        end.

        Definition vars_of_SideCondition
            {Σ : Signature}
            (c : SideCondition)
            : gset variable :=
        match c with
        | sc_constraint c' => vars_of_Constraint c'
        | sc_match x φ => {[x]} ∪ vars_of_BasicPattern φ
        end.

        Fixpoint vars_of_BasicPatternWSC
            {Σ : Signature}
            (φc : BasicPatternWSC)
            : gset variable :=
        match φc with
        | wsc_base φ => vars_of_BasicPattern φ
        | wsc_sc φ c
            => vars_of_BasicPatternWSC φ ∪ vars_of_SideCondition c
        end.

        Fixpoint vars_of_LhsPattern
            {Σ : Signature}
            (φ : LhsPattern)
            : gset variable :=
        match φ with
        | ao_operator o => ∅
        | ao_app_operand x y
            => vars_of_LhsPattern x ∪ vars_of_BasicPatternWSC y
        | ao_app_ao x y
            => vars_of_LhsPattern x ∪ vars_of_LhsPattern y
        end.

        Fixpoint vars_of_Expression
            {Σ : Signature}
            (t : Expression)
            : gset variable :=
        match t with
        | ft_element _ => ∅
        | ft_variable x => {[x]}
        | ft_unary _ t' => vars_of_Expression t'
        | ft_binary _ t1 t2 => vars_of_Expression t1 ∪ vars_of_Expression t2
        end.

        Fixpoint vars_of_AppliedOperator_sym_fterm
            {Σ : Signature}
            (op : AppliedOperator' symbol Expression)
            : gset variable :=
        match op with
        | ao_operator _ => ∅
        | ao_app_operand aps' o =>
            vars_of_AppliedOperator_sym_fterm aps' ∪ vars_of_Expression o
        | ao_app_ao aps1 aps2 =>
            vars_of_AppliedOperator_sym_fterm aps1 ∪ vars_of_AppliedOperator_sym_fterm aps2
        end.

        Fixpoint vars_of_RhsPattern
            {Σ : Signature}
            (φ : RhsPattern)
            : gset variable :=
        match φ with
        | ao_operator _ => ∅
        | ao_app_operand  φ' t
            => vars_of_RhsPattern φ' ∪ vars_of_Expression t
        | ao_app_ao φ1 φ2
            => vars_of_RhsPattern φ1 ∪ vars_of_RhsPattern φ2
        end.

        Fixpoint var_of_WithASideCondition_variable
            {Σ : Signature}
            (x : WithASideCondition variable)
            : variable :=
        match x with
        | wsc_base x' => x'
        | wsc_sc x' sc => var_of_WithASideCondition_variable x'
        end.

        Definition vars_of_LocalRewrite
            {Σ : Signature}
            (lr : LeftRight)
            (r : LocalRewrite)
            : gset variable :=
        match lr,r with
        | LR_Left,lr_var x _ => {[var_of_WithASideCondition_variable x]}
        | LR_Left, lr_builtin _ _ => ∅
        | LR_Left, lr_pattern φ _ => vars_of_LhsPattern φ
        | LR_Right, lr_var _ e => vars_of_Expression e
        | LR_Right, lr_builtin _ e => vars_of_Expression e
        | LR_Right, lr_pattern _ φ => vars_of_RhsPattern φ
        end.

    End vars_of.

End Syntax.

Module Semantics.
    Import Syntax.

    

    Lemma Expression_evalute_total_iff
        {Σ : Signature}
        (t : Expression)
        (ρ : Valuation)
        :
        (∃ e:Value, Expression_evaluate ρ t = Some e)
        <->
        ( vars_of_Expression t ⊆ dom ρ )
    .
    Proof.
        induction t; cbn.
        {
            split; intros H.
            {
                apply empty_subseteq.
            }
            {
                exists e.
                reflexivity.
            }
        }
        {
            split; intros H.
            {
                rewrite elem_of_subseteq.
                intros x0 Hx0.
                rewrite elem_of_singleton in Hx0.
                subst x0.
                destruct H as [e H].
                ltac1:(rewrite elem_of_dom).
                exists e. exact H.
            }
            {
                rewrite elem_of_subseteq in H.
                specialize (H x).
                rewrite elem_of_singleton in H.
                specialize (H erefl).
                ltac1:(rewrite elem_of_dom in H).
                unfold is_Some in H.
                destruct H as [e H].
                exists e.
                exact H.
            }
        }
        {
            
            ltac1:(rewrite <- IHt).
            split; intros [e H].
            {
                unfold mbind,option_bind in H; cbn.
                ltac1:(case_match).
                {
                    ltac1:(rewrite <- H0).
                    eexists.
                    exact H0.
                }
                {
                    inversion H.
                }
            }
            {
                eexists. rewrite H. reflexivity.
            }
        }
        {
            rewrite union_subseteq.
            ltac1:(rewrite <- IHt1).
            ltac1:(rewrite <- IHt2).
            split; intros H.
            {
                destruct H as [e H].
                unfold mbind,option_bind in H.
                (repeat ltac1:(case_match)); ltac1:(simplify_eq /=);
                    split; eexists; reflexivity.
            }
            {
                destruct H as [[e1 H1] [e2 H2]].
                unfold mbind,option_bind.
                rewrite H1.
                rewrite H2.
                eexists. reflexivity.
            }
        }
    Qed.

    Lemma lhs_sat_impl_good_valuation
        {Σ : Signature} e φ ρ:
        element_satisfies_pattern ρ e φ ->
        vars_of_Pattern φ ⊆ dom ρ
    .
    Proof.
        intros H.
        induction H; cbn; try (ltac1:(set_solver)).
        { 
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            rewrite elem_of_singleton in Hx0.
            subst.
            ltac1:(rewrite elem_of_dom).
            exists e.
            exact H.
        }
        {
            ltac1:(rewrite !union_subseteq).
            repeat split; try assumption.
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            rewrite elem_of_singleton in Hx0.
            subst.
            ltac1:(rewrite elem_of_dom).
            exists e2.
            exact H.
        }
    Qed.


    Lemma good_valuation_impl_rhs_sat_helper
        {Σ : Signature} φ ρ:
        vars_of_AppliedOperator_sym_fterm φ ⊆ dom ρ ->
        exists e, aosb_satisfies_aosf ρ e φ
    .
    Proof.
        induction φ; cbn; intros H.
        {
            eexists. econstructor.
        }
        {
            rewrite union_subseteq in H.
            destruct H as [H1 H2]; cbn.
            specialize (IHφ H1).
            ltac1:(rewrite -Expression_evalute_total_iff in H2).
            destruct IHφ as [e1 IHφ].
            destruct H2 as [e2 He2]; cbn.
            destruct e2; cbn.
            {
                eexists. econstructor.
                apply IHφ.
                exact He2.
            }
            {
                eexists. apply asaosf_app_operand_2.
                { apply IHφ. }
                { apply He2. }
            }
        }
        {
            rewrite union_subseteq in H.
            destruct H as [H1 H2].
            specialize (IHφ1 H1).
            specialize (IHφ2 H2).
            destruct IHφ1 as [e1 IHφ1].
            destruct IHφ2 as [e2 IHφ2].
            eexists. econstructor.
            { apply IHφ1. }
            { apply IHφ2. }
        }
    Qed.

    Lemma good_valuation_impl_rhs_sat
        {Σ : Signature} φ ρ:
        vars_of_RhsPattern φ ⊆ dom ρ ->
        exists e, element_satisfies_rhs_pattern ρ e φ
    .
    Proof.
        destruct φ; cbn.
        {
            intros H.
            ltac1:(rewrite -Expression_evalute_total_iff in H).
            destruct H as [e H].
            exists e.
            constructor.
            exact H.
        }
        {
            intros H.
            apply good_valuation_impl_rhs_sat_helper in H.
            destruct H as [e H].
            eexists. econstructor. 
            apply H.
        }
    Qed.


    Definition lr_satisfies
        {Σ : Signature} (left_right : LR) (e : Value) (lr : LocalRewrite) (ρ : Valuation)
        : Prop :=
    match left_right with
    | LR_Left =>
        element_satisfies_pattern ρ e (lr_from lr)
    | LR_Right =>
        element_satisfies_rhs_pattern ρ e (lr_to lr)
    end
    .

    Print Pattern.

    Equations Derive NoConfusion for RewritingRule.

    Fixpoint RewritingRule_size {Σ : Signature} (r : RewritingRule) : nat :=
    match r with
    | rr_local_rewrite _ => 1
    | rr_builtin _ => 1
    | rr_app r1 r2 => 1 + RewritingRule_size r1 + RewritingRule_size r2
    | rr_var _ => 1
    | rr_sym _ => 1
    | rr_requires r _ => 1 + RewritingRule_size r
    | rr_requires_match r _ _ => 1 + RewritingRule_size r
    end.

    #[export]
    Instance RewritingRule_eqdec {Σ : Signature}
        : EqDecision RewritingRule
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    Section sec.
        Context
            {Σ : Signature}
            (left_right : LR)
            (ρ : Valuation)
        .

        Print Pattern.

        Inductive rr_satisfies :
            RewritingRule -> Value -> Prop :=
            
        | rr_sat_local :
            forall e lr
                (Hvars : vars_of_RhsPattern (lr_to lr) ⊆ vars_of_Pattern (lr_from lr))
                (Hsat : lr_satisfies left_right e lr ρ),
                rr_satisfies (rr_local_rewrite lr) e
        
        | rr_sat_builtin :
            forall b,
                rr_satisfies (rr_builtin b) (val_builtin b)

        | rr_sat_var :
            forall x e
                (Hlookup : ρ !! x = Some e),
                rr_satisfies (rr_var x) e
        
        | rr_sat_sym :
            forall s,
                rr_satisfies (rr_sym s) (val_gterm (ao_operator s))
        
        | rr_sat_app_1 :
            forall φ1 φ2 aps1 aps2
                (Hsat1 : rr_satisfies φ1 (val_gterm aps1))
                (Hsat2 : rr_satisfies φ2 (val_gterm aps2)),
                rr_satisfies (rr_app φ1 φ2) (val_gterm (ao_app_ao aps1 aps2))
        
        | rr_sat_app_2 :
            forall φ1 φ2 aps1 b2
                (Hsat1 : rr_satisfies φ1 (val_gterm aps1))
                (Hsat2 : rr_satisfies φ2 (val_builtin b2)),
                rr_satisfies (rr_app φ1 φ2) (val_gterm (ao_app_operand aps1 b2))
        
        | rr_sat_req :
            forall r c e
                (Hsat1 : rr_satisfies r e)
                (Hsat2 : (val_satisfies_c ρ c  \/ left_right = LR_Right)),
                rr_satisfies (rr_requires r c) e
        
        | rr_sat_req_match :
            forall r x φ' e e2
                (Hsat1 : rr_satisfies r e)
                (Hlookup : ρ !! x = Some e2)
                (Hsat2 : (element_satisfies_pattern ρ e2 φ' \/ left_right = LR_Right)),
                rr_satisfies (rr_requires_match r x φ') e
        .

    End sec.
    (*
    Lemma rr_weakly_well_defined_0 {Σ : Signature} rr ρ aps:
        rr_satisfies LR_Left ρ rr (val_gterm aps) ->
        ∃ aps', rr_satisfies LR_Right ρ rr (val_gterm aps').
    Proof.
        intros H.
        induction H; cbn.
        {
            destruct lr; cbn in *.
            apply lhs_sat_impl_good_valuation in Hsat.
            assert (Hvars2 : vars_of_RhsPattern lr_to0 ⊆ dom ρ).
            { ltac1:(set_solver). }
            apply good_valuation_impl_rhs_sat in Hvars2.
            destruct Hvars2 as [e' He'].
            eexists. econstructor; cbn.
            { ltac1:(set_solver). }
            { apply He'. }
        }
    Qed.
    *)
    Lemma rr_weakly_well_defined {Σ : Signature} rr ρ e:
        rr_satisfies LR_Left ρ rr e ->
        ∃ e', rr_satisfies LR_Right ρ rr e'.
    Proof.
        intros H.
        induction H; cbn.
        {
            destruct lr; cbn in *.
            apply lhs_sat_impl_good_valuation in Hsat.
            assert (Hvars2 : vars_of_RhsPattern lr_to0 ⊆ dom ρ).
            { ltac1:(set_solver). }
            apply good_valuation_impl_rhs_sat in Hvars2.
            destruct Hvars2 as [e' He'].
            eexists. econstructor; cbn.
            { ltac1:(set_solver). }
            { apply He'. }
        }
        {
            eexists. econstructor.
        }
        {
            eexists. econstructor. apply Hlookup.
        }
        {
            eexists. econstructor.
        }
        {
            destruct IHrr_satisfies1 as [e1 He1].
            destruct IHrr_satisfies2 as [e2 He2].
            (* eexists (val_gterm ?[aps']). *)
            destruct e1.
            {
                inversion He1; subst;
                            eexists;
                apply rr_sat_app_2.
                {
                    econstructor.
                    { exact Hvars. }
                    {}
                }
            }
            eexists.
            apply rr_sat_app_1.
            {}
            destruct e1, e2.
            { eexists. apply rr_sat_app_2. }
            eexists.
            apply rr_sat_app_2.
            { apply He1. }
            { apply He2. }
        }
        {

        }

    Qed.

    Definition rewrites_in_valuation_to
        {Σ : Signature} (ρ : Valuation) (r : RewritingRule) (from to : Value)
        : Prop
    := rr_satisfies LR_Left ρ r from
    /\ rr_satisfies LR_Right ρ r to
    .

    Definition rewrites_to
        {Σ : Signature} (r : RewritingRule) (from to : Value)
        : Prop
    := exists ρ, rewrites_in_valuation_to ρ r from to
    .

    Definition RewritingTheory {Σ : Signature}
        := list RewritingRule
    .

    Definition rewriting_relation
        {Σ : Signature}
        (Γ : RewritingTheory)
        : relation Value
        := fun from to =>
            exists r, r ∈ Γ /\ rewrites_to r from to
    .

    Definition not_stuck
        {Σ : Signature}
        (Γ : RewritingTheory)
        (e : Value) : Prop
    := exists e', rewriting_relation Γ e e'.

    Definition stuck
        {Σ : Signature}
        (Γ : RewritingTheory)
        (e : Value) : Prop
    := not (not_stuck Γ e).

End Semantics.

Definition Interpreter
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Type
    := Value -> option Value
.

Definition Interpreter_sound
    {Σ : Signature}
    (Γ : RewritingTheory)
    (interpreter : Interpreter Γ)
    : Prop
    := (forall e,
        stuck Γ e -> interpreter e = None)
    /\ (forall e,
        not_stuck Γ e ->
        exists e', interpreter e = Some e')
.

Definition Explorer
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Type
    := Value -> list Value
.

Definition Explorer_sound
    {Σ : Signature}
    (Γ : RewritingTheory)
    (explorer : Explorer Γ)
    : Prop
    := forall (e e' : Value),
        e' ∈ explorer e <-> rewriting_relation Γ e e'
.




