From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
.

Definition valuation_satisfies_scs
    {Σ : Signature}
    (ρ : Valuation)
    (scs : list SideCondition)
    : Prop
:= Forall (valuation_satisfies_sc ρ) scs
.

Record FlattenedRewritingRule {Σ : Signature} := {
    fr_from : OpenTerm ;
    fr_to : RhsPattern ;
    fr_scs : list SideCondition ;
}.

Definition flattened_rewrites_in_valuation_to
    {Σ : Signature}
    (ρ : Valuation)
    (r : FlattenedRewritingRule)
    (from to : GroundTerm)
    : Prop
:= in_val_GroundTerm_satisfies_OpenTerm
    ρ from (fr_from r)
/\ GroundTerm_satisfies_RhsPattern
    ρ to (fr_to r)
/\ valuation_satisfies_scs ρ (fr_scs r)
.

Definition flattened_rewrites_to
    {Σ : Signature}
    (r : FlattenedRewritingRule)
    (from to : GroundTerm)
    : Prop
:= exists ρ, flattened_rewrites_in_valuation_to ρ r from to
.

Fixpoint separate_scs
    {Σ : Signature}
    {A : Set}
    (wsc : WithASideCondition A):
    A * (list SideCondition)
:=
match wsc with
| wsc_base a => (a, [])
| wsc_sc wsc' sc =>
    match separate_scs wsc' with
    | (a, scs) => (a, sc::scs)
    end
end.

Lemma separate_scs_correct
    {Σ : Signature}
    {A B : Set}
    (A_sat_B : A -> B -> Prop)
    (wscb : WithASideCondition B)
    (a : A)
    (ρ : Valuation)
    :
    match separate_scs wscb with
    | (b, scs) => A_sat_B a b /\ valuation_satisfies_scs ρ scs
    end
    <->
    A_satisfies_B_WithASideCondition A B A_sat_B ρ a wscb
.
Proof.
    unfold valuation_satisfies_scs.
    induction wscb; cbn.
    {
        split.
        {
            intros [H1 H2].
            constructor.
            exact H1.
        }
        {
            intros H.
            inversion H; subst.
            split.
            { assumption. }
            {
                apply Forall_nil.
            }
        }
    }
    {
        repeat (ltac1:(case_match)).
        rewrite Forall_cons_iff.
        
        ltac1:(rewrite [(valuation_satisfies_sc _ _) /\ _]and_comm).
        ltac1:(rewrite and_assoc).
        ltac1:(rewrite IHwscb).
        clear IHwscb.
        (repeat split); intros.
        {
            constructor;
            ltac1:(naive_solver).
        }
        {
            inversion H0; subst.
            assumption.
        }
        {
            inversion H0; subst.
            assumption.
        }
    }
Qed.

Fixpoint AppliedOperator'_size
    {Operator Operand : Set}
    (x : AppliedOperator' Operator Operand)
    : nat :=
match x with
| ao_operator _ => 1
| ao_app_operand x' _ => 1 + AppliedOperator'_size x'
| ao_app_ao x1 x2 => 1 + AppliedOperator'_size x1 + AppliedOperator'_size x2
end.

Definition AppliedOperatorOr'_deep_size
    {Operator Operand : Set}
    (x : AppliedOperatorOr' Operator Operand)
    : nat :=
match x with
| aoo_operand _ _ o => 1
| aoo_app _ _ x' => 1 + AppliedOperator'_size x'
end.

Fixpoint AppliedOperator'_symbol_A_to_pair_OpenTerm_SC
    {Σ : Signature}
    {A : Set}
    (A_to_OpenTerm_SC : A ->
        ((AppliedOperatorOr' symbol BuiltinOrVar) * (list SideCondition))
    )
    (x : AppliedOperator' symbol A)
    : ((AppliedOperator' symbol BuiltinOrVar) * (list SideCondition))
:=
match x with
| ao_operator a => ((ao_operator a), [])
| ao_app_operand x' o =>
    match AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC x' with
    | (t1, scs1) =>
        match A_to_OpenTerm_SC o with
        | (aoo_app _ _ t2, scs2) =>
            ((ao_app_ao t1 t2), scs1 ++ scs2)
        | (aoo_operand _ _ t2, scs2) =>
            ((ao_app_operand t1 t2), scs1 ++ scs2)
        end
    end
| ao_app_ao x1 x2 =>
    match AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC x1 with
    | (t1, scs1) =>
        match AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC x2 with
        | (t2, scs2) => (ao_app_ao t1 t2, scs1 ++ scs2)
        end
    end
end.

(*
Lemma helper
    {Σ : Signature}
    x:
    match AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC x with
        | (y, scs) =>
*)
Lemma correct_AppliedOperator'_symbol_A_to_pair_OpenTerm_SC
    {Σ : Signature}
    {A : Set}
    (A_to_OpenTerm_SC : A ->
        ((AppliedOperatorOr' symbol BuiltinOrVar) * (list SideCondition))
    )
    (builtin_satisfies_A:
        Valuation -> builtin_value -> A -> Prop
    )
    (AppliedOperator'_symbol_builtin_satisfies_A:
        Valuation ->
        AppliedOperator' symbol builtin_value ->
        A ->
        Prop
    )
    (ρ : Valuation)
    (correct_A_to_OpenTerm_SC :
        forall γ (a : A),
            (match A_to_OpenTerm_SC a with
            | (aoo_app _ _ b, scb) => @aoxy_satisfies_aoxz symbol builtin_value BuiltinOrVar
                (builtin_satisfies_BuiltinOrVar ρ)
                (AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ)
                γ b
                /\ valuation_satisfies_scs ρ scb
            | (aoo_operand _ _ b, scb) =>
                AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ γ b
                /\ valuation_satisfies_scs ρ scb
            end
            <->
                AppliedOperator'_symbol_builtin_satisfies_A ρ γ a
            )
    )
    (correct2_A_to_OpenTerm_SC :
        ∀ (a : A) (b : builtin_value) (ρ : Valuation),
        builtin_satisfies_A ρ b a <->
        ∃ (bov : BuiltinOrVar) rest,
            (A_to_OpenTerm_SC a) = (aoo_operand _ _ bov, rest)
            /\ builtin_satisfies_BuiltinOrVar ρ b bov
            /\ valuation_satisfies_scs ρ rest
    )
    (x : AppliedOperator' symbol A)
    (g : AppliedOperator' symbol builtin_value)
    :
    (
        match AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC x with
        | (y, scs) =>
            @aoxy_satisfies_aoxz
                symbol
                builtin_value
                BuiltinOrVar
                (builtin_satisfies_BuiltinOrVar ρ)
                (AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ)
                g
                y
            /\ (valuation_satisfies_scs ρ scs)
        end

    )
    <-> @aoxy_satisfies_aoxz
                symbol
                builtin_value
                A
                (builtin_satisfies_A ρ)
                (AppliedOperator'_symbol_builtin_satisfies_A ρ)
                g
                x
.
Proof.
    split.
    { 
        intros H.
        remember (AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC x) as call.
        destruct call as [y scs].
        destruct H as [H1 H2].
        revert y g scs Heqcall H1 H2.
        induction x; intros y g scs Heqcall H1 H2; cbn in *.
        {
            ltac1:(simplify_eq /=).
            inversion H1; subst; clear H1.
            constructor.
        }
        {
            (repeat ltac1:(case_match));
              ltac1:(simplify_eq /=).
            {
                inversion H1; subst; clear H1.
                constructor.
                {
                    eapply IHx.
                    { reflexivity. }
                    { assumption. }
                    {
                        unfold valuation_satisfies_scs in * |-; cbn.
                        unfold valuation_satisfies_scs.
                        rewrite Forall_app in H2.
                        apply H2.
                    }
                }
                {
                    
                    apply correct_A_to_OpenTerm_SC.
                    repeat ltac1:(case_match);
                    ltac1:(simplify_eq /=).
                    {
                        split.
                        {
                            assumption.
                        }
                        {
                            unfold valuation_satisfies_scs in * |-; cbn.
                            unfold valuation_satisfies_scs.
                            rewrite Forall_app in H2.
                            apply H2.
                        }
                    }
                }
            }
            {
                inversion H1; subst; clear H1; constructor.
                {
                    eapply IHx.
                    { reflexivity. }
                    {
                        assumption.
                    }
                    {
                        unfold valuation_satisfies_scs in * |-; cbn.
                        unfold valuation_satisfies_scs.
                        rewrite Forall_app in H2.
                        apply H2.
                    }
                }
                {
                    rewrite correct2_A_to_OpenTerm_SC.
                    rewrite H0.
                    eexists. eexists. split.
                    { reflexivity. }
                    split.
                    { assumption. }
                    {
                        unfold valuation_satisfies_scs in H2.
                        rewrite Forall_app in H2.
                        apply H2.
                    }
                }
                {
                    eapply IHx.
                    { reflexivity. }
                    {
                        assumption.
                    }
                    {
                        unfold valuation_satisfies_scs in * |-; cbn.
                        unfold valuation_satisfies_scs.
                        rewrite Forall_app in H2.
                        apply H2.
                    }
                }
                {
                    destruct operand.
                    {
                        inversion H7.
                    }
                    {
                        inversion H7; subst; clear H7.
                        rewrite <- correct_A_to_OpenTerm_SC.
                        remember (A_to_OpenTerm_SC b) as rec2.
                        destruct rec2 as [a0 scb].
                        destruct a0.
                        {
                            inversion H0; subst; clear H0.
                        }
                        {
                            inversion H0; subst; clear H0.
                            split.
                            {
                                cbn.
                                exact H3.
                            }
                            {
                                unfold valuation_satisfies_scs in H2.
                                rewrite Forall_app in H2.
                                apply H2.
                            }
                        }
                    }
                }
            }
        }
        {
            (repeat ltac1:(case_match));
              ltac1:(simplify_eq /=).
            inversion H1; subst; clear H1.
            constructor.
            {
                eapply IHx1.
                { reflexivity. }
                { assumption.  }
                {
                    unfold valuation_satisfies_scs in H2.
                    rewrite Forall_app in H2.
                    apply H2.
                }
            }
            {
                eapply IHx2.
                { reflexivity. }
                { assumption.  }
                {
                    unfold valuation_satisfies_scs in H2.
                    rewrite Forall_app in H2.
                    apply H2.
                }
            }
        }
        
    }
    {
        intros H.
        induction H; cbn.
        {
            split.
            { constructor. }
            { apply Forall_nil. }
        }
        {
            remember (AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC aoxz) as rec.
            destruct rec as [y0 scs].
            remember (A_to_OpenTerm_SC z) as occall.
            destruct occall as [a scs2].
            apply correct2_A_to_OpenTerm_SC in H0.
            destruct H0 as [bov [rest [H01 [H02 H03]]]]; cbn in *.
            rewrite H01 in Heqoccall.
            destruct a.
            {
                ltac1:(exfalso).
                inversion Heqoccall; subst; clear Heqoccall.
            }
            {
                split.
                {
                    constructor.
                    { apply IHaoxy_satisfies_aoxz. }
                    {
                        inversion Heqoccall; subst; clear Heqoccall.
                        exact H02.
                    }
                }
                {
                    inversion Heqoccall; subst; clear Heqoccall.
                    unfold valuation_satisfies_scs.
                    destruct IHaoxy_satisfies_aoxz as [IH1 IH2]; cbn in *.
                    rewrite Forall_app.
                    split.
                    { exact IH2. }
                    { exact H03. }
                }
            }
        }
        {
            remember (AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC aoxz) as rec1.
            destruct rec1 as [t1 scs2].
            remember (A_to_OpenTerm_SC z ) as rec2.
            destruct rec2 as [a scs0].
            rewrite <- correct_A_to_OpenTerm_SC in H0.
            rewrite <- Heqrec2 in H0.
            destruct a.
            {
                split.
                {
                    constructor.
                    {
                        apply IHaoxy_satisfies_aoxz.
                    }
                    {
                        apply H0.
                    }
                }
                {
                    unfold valuation_satisfies_scs.
                    rewrite Forall_app.
                    split.
                    {
                        apply IHaoxy_satisfies_aoxz.
                    }
                    {
                        apply H0.
                    }
                }
            }
            {
                split.
                {
                    constructor.
                    {
                        apply IHaoxy_satisfies_aoxz.
                    }
                    {
                        apply H0.
                    }
                }
                {
                    unfold valuation_satisfies_scs.
                    rewrite Forall_app.
                    split.
                    {
                        apply IHaoxy_satisfies_aoxz.
                    }
                    {
                        apply H0.
                    }
                }

            }
        }
        {
            remember (AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC aoxz1) as rec1.
            remember (AppliedOperator'_symbol_A_to_pair_OpenTerm_SC A_to_OpenTerm_SC aoxz2) as rec2.
            destruct rec1 as [t1 scs1].
            destruct rec2 as [t2 scs2].
            split.
            {
                constructor.
                { apply IHaoxy_satisfies_aoxz1. }
                { apply IHaoxy_satisfies_aoxz2. }
            }
            {
                unfold valuation_satisfies_scs.
                rewrite Forall_app.
                split.
                { apply IHaoxy_satisfies_aoxz1. }
                { apply IHaoxy_satisfies_aoxz2. }
            }
        }
    }
Qed.


Print AppliedOperator'.
Print AppliedOperatorOr'.
Print OpenTerm.

Print OpenTerm.
Print OpenTermWSC.
Print LhsPattern.

Definition LhsPattern_to_pair_OpenTerm_SC
    {Σ : Signature}
    (l : LhsPattern)
    : (OpenTerm * (list SideCondition))
:=
match l with
| aoo_app _ _ aop =>
    match AppliedOperator'_symbol_A_to_pair_OpenTerm_SC separate_scs aop with
    | (o, sc) => (aoo_app _ _ o, sc)
    end
| aoo_operand _ _ o =>
    separate_scs o
end.

Lemma A_satisfies_B_WithASideCondition_helper {Σ : Signature}:
    forall ρ bsc γ,
    A_satisfies_B_WithASideCondition
        (AppliedOperatorOr' symbol builtin_value)
        (AppliedOperatorOr' symbol BuiltinOrVar)
        (in_val_GroundTerm_satisfies_OpenTerm ρ)
        ρ
        (aoo_app symbol builtin_value γ) bsc <->
    A_satisfies_B_WithASideCondition
        (AppliedOperator' symbol builtin_value)
        (AppliedOperatorOr' symbol BuiltinOrVar)
        (AppliedOperator'_symbol_builtin_satisfies_OpenTerm ρ)
        ρ γ bsc
.
Proof.
    intros.
    split. intros.
    {
        remember ((aoo_app symbol builtin_value γ)) as r.
        induction H; repeat constructor; try assumption.
        {
            subst.
            inversion H; subst; clear H.
            { simpl.
              exact pf.
            }
            {
                simpl. destruct axz.
                { simpl in H1. exact H1. }
                {
                    simpl in H1. exact H1.
                }
            }
        }
        {
            specialize (IHA_satisfies_B_WithASideCondition Heqr).
            apply IHA_satisfies_B_WithASideCondition.
        }
    }
    {
        intros.
        remember ((aoo_app symbol builtin_value γ)) as r.
        induction H; repeat constructor; try assumption.
        {
            subst.
            destruct b; cbn.
            {
                cbn in H.
                constructor.
                assumption.
            }
            {
                cbn in H.
                cbn; destruct operand; constructor.
                inversion H.
                apply H.
            }
        }
        {
            auto with nocore.
        }
    }
Qed.

Lemma correct_LhsPattern_to_pair_OpenTerm_SC
    {Σ : Signature}
    (l : LhsPattern)
    (ρ : Valuation)
    (g : GroundTerm):
    match LhsPattern_to_pair_OpenTerm_SC l with
    | (o, scs) =>
        in_val_GroundTerm_satisfies_OpenTerm ρ g o
        /\ valuation_satisfies_scs ρ scs
    end
    <-> GroundTerm_satisfies_LhsPattern ρ g l
.
Proof.
    remember (LhsPattern_to_pair_OpenTerm_SC l) as call.
    destruct call as [o scs]; cbn.
    unfold GroundTerm_satisfies_LhsPattern.
    destruct g; cbn.
    {
        split.
        {
            intros [H1 H2].
            destruct l.
            {
                simpl in Heqcall.
                repeat ltac1:(case_match).
                constructor.
                inversion H1; subst; clear H1.
                {
                    inversion Heqcall; subst; clear Heqcall.
                    erewrite <- (correct_AppliedOperator'_symbol_A_to_pair_OpenTerm_SC separate_scs); cbn.
                    {
                        rewrite H.
                        split; assumption.
                    }
                    {
                        intros.
                        repeat ltac1:(case_match); subst.
                        {
                            unfold AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC.
                        rewrite <- separate_scs_correct.
                        remember (separate_scs a0) as rsa.
                        ltac1:(rewrite -Heqrsa).
                        ltac1:(rewrite H0).
                        
                            (repeat split); intros; try constructor.
                        {
                            unfold AppliedOperator'_symbol_builtin_satisfies_OpenTerm.
                            apply H1.
                        }
                        {
                            apply H1.
                        }
                        {
                            apply H1.
                        }
                        {
                            apply H1.
                        }
                        }
                        {

                            (* unfold AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar. *)
                            unfold AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC.
                            rewrite <- separate_scs_correct.

                            remember (separate_scs a0) as rsa.
                            ltac1:(rewrite -Heqrsa).
                            ltac1:(rewrite H0).

                            (repeat split); cbn; try ltac1:(naive_solver).
                        }
                    }
                    {
                        intros.
                    }
                }
                {
                    intros.
                    {repeat (ltac1:(case_match)).
                    ltac1:(simplify_eq /=).
                    epose (H' := @separate_scs_correct Σ (AppliedOperatorOr' symbol builtin_value) (AppliedOperatorOr' symbol BuiltinOrVar) (in_val_GroundTerm_satisfies_OpenTerm ρ) a0).
                    rewrite H0 in H'.
                    specialize (H' (aoo_app _ _ γ) ρ).
                    destruct H' as [H'1 H'2].
                    split; intros HH.
                    {
                        destruct HH as [HH1 HH2].
                        ltac1:(feed specialize H'1).
                        {
                            split.
                            {
                                constructor.
                                exact HH1.
                            }
                            {
                                exact HH2.
                            }
                        }
                        inversion H'1; subst; clear H'1; constructor.
                        {
                            inversion H1; subst; clear H1.
                            { simpl. assumption. }
                            { simpl. cbn in H0. inversion H0. }
                        }
                        {
                            simpl in H1.
                            apply A_satisfies_B_WithASideCondition_helper.
                            assumption.
                        }
                        {
                            assumption.
                        }
                    }
                    {
                        ltac1:(feed specialize H'2).
                        {
                            clear H'1 H'2.
                            apply A_satisfies_B_WithASideCondition_helper.
                            assumption.
                        }
                        clear H'1.
                        destruct H'2 as [H''1 H''2].
                        split; try assumption.
                        inversion H''1; subst; clear H''1.
                        assumption.
                    }
                    {
                        subst.
                        unfold AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC.
                        repeat split; intros.
                        {
                            destruct H1 as [HH1 HH2].
                            rewrite <- separate_scs_correct.
                            repeat (ltac1:(case_match)).
                            ltac1:(rewrite H1 in H0); cbn.
                            ltac1:(simplify_eq /=).
                            repeat (ltac1:(case_match));
                                ltac1:(simplify_eq /=).
                            { inversion HH1. }
                            { split; assumption. }
                        }
                        {
                            destruct a0; cbn in *.
                            {
                                inversion H0; subst; clear H0.
                                inversion H1; subst; clear H1.
                                cbn in H4.
                                unfold AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar.
                                exact H4.
                            }
                            {
                                repeat ltac1:(case_match).
                                ltac1:(simplify_eq /=).
                                inversion H1; subst; clear H1.
                                inversion H6; subst; clear H6.
                                unfold AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar.
                                assert (Htmp := @separate_scs_correct Σ GroundTerm OpenTerm (in_val_GroundTerm_satisfies_OpenTerm ρ)).
                                specialize (Htmp (wsc_base b)).
                                ltac1:(rewrite H3 in Htmp).
                                cbn in Htmp.
                                specialize (Htmp (aoo_app _ _ γ) ρ).
                                destruct Htmp as [Htmp1 Htmp2]; cbn.
                                ltac1:(feed specialize Htmp2).
                                {
                                    constructor.
                                    unfold in_val_GroundTerm_satisfies_OpenTerm.
                                    destruct b; constructor.
                                    {
                                        inversion H0; subst; clear H0.
                                        constructor.
                                    }
                                    {
                                        constructor; assumption.
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    rewrite <- correct_AppliedOperator'_symbol_A_to_pair_OpenTerm_SC.
Qed.

Print LocalRewrite.

Print LocalRewriteOrOpenTermOrBOV.

Print UncondRewritingRule.

Print RewritingRule.