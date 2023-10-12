From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
.

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

Fixpoint getSCS {Σ : Signature} {A : Set} (wsc : WithASideCondition A):
    list SideCondition
:=
match wsc with
| wsc_base _ => []
| wsc_sc wsc' sc => sc::(getSCS wsc')
end.

Fixpoint getBase {Σ : Signature} {A : Set} (wsc : WithASideCondition A):
    A
:=
match wsc with
| wsc_base a => a
| wsc_sc wsc' _ => getBase wsc'
end.


Lemma separate_scs_getSCS_getBase
    {Σ : Signature} {A : Set}
    (wsc : WithASideCondition A)
    : separate_scs wsc = (getBase wsc, getSCS wsc)
.
Proof.
    induction wsc; cbn.
    { reflexivity. }
    {
        ltac1:(case_match).
        ltac1:(simplify_eq/=).
        reflexivity.
    }
Qed.


Fixpoint AppliedOperator'_symbol_A_to_SCS
    {Σ : Signature}
    {A : Set}
    (A_to_SC : A -> list SideCondition )
    (x : AppliedOperator' symbol A)
    : list SideCondition
:=
match x with
| ao_operator a => []
| ao_app_operand x' o =>
    (AppliedOperator'_symbol_A_to_SCS A_to_SC x') ++ A_to_SC o
| ao_app_ao x1 x2 =>
    (AppliedOperator'_symbol_A_to_SCS A_to_SC x1) ++ (AppliedOperator'_symbol_A_to_SCS A_to_SC x2)
end.

Definition AppliedOperatorOr'_symbol_A_to_SCS
    {Σ : Signature}
    {A : Set}
    (A_to_SC : A -> list SideCondition )
    (x : AppliedOperatorOr' symbol A)
    : list SideCondition
:=
match x with
| aoo_app _ _ app => AppliedOperator'_symbol_A_to_SCS A_to_SC app
| aoo_operand _ _ operand => A_to_SC operand
end.

Fixpoint AppliedOperator'_symbol_A_to_OpenTermB
    {Σ : Signature}
    {A B : Set}
    (A_to_OpenTermB : A ->
        ((AppliedOperatorOr' symbol B))
    )
    (x : AppliedOperator' symbol A)
    : ((AppliedOperator' symbol B))
:=
match x with
| ao_operator a => (ao_operator a)
| ao_app_operand x' a =>
    let t1 := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x' in
    match A_to_OpenTermB a with
    | (aoo_app _ _ t2) => (ao_app_ao t1 t2)
    | (aoo_operand _ _ t2) => (ao_app_operand t1 t2)
    end
| ao_app_ao x1 x2 =>
    let t1 := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x1 in
    let t2 := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x2 in
    ao_app_ao t1 t2
end.

Definition AppliedOperatorOr'_symbol_A_to_OpenTermB
    {Σ : Signature}
    {A B : Set}
    (A_to_OpenTermB : A ->
        ((AppliedOperatorOr' symbol B))
    )
    (x : AppliedOperatorOr' symbol A)
    : ((AppliedOperatorOr' symbol B))
:=
match x with
| aoo_app _ _ app => aoo_app _ _ (AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB app)
| aoo_operand _ _ operand => A_to_OpenTermB operand
end.


Fixpoint A_satisfies_B_WithASideCondition_comp
    {Σ : Signature}
    (A B : Set)
    (A_sat_B : A -> B -> Prop)
    (ρ : Valuation)
    (a : A)
    (wscb : WithASideCondition B)
:=
match wscb with
| wsc_base b => A_sat_B a b
| wsc_sc wscb' sc =>
    A_satisfies_B_WithASideCondition_comp A B A_sat_B ρ a wscb'
    /\ valuation_satisfies_sc ρ sc
end
.


Fixpoint aoxy_satisfies_aoxz_comp
    {X Y Z : Set}
    (Y_sat_Z : Y -> Z -> Prop)
    (AOXY_sat_Z : AppliedOperator' X Y -> Z -> Prop)
    (g : AppliedOperator' X Y)
    (φ : AppliedOperator' X Z):
    Prop :=
match g, φ with
| ao_operator x1, ao_operator x2 => x1 = x2
| ao_operator _, _ => False
| ao_app_operand g1 g2, ao_app_operand φ1 φ2 =>
    aoxy_satisfies_aoxz_comp Y_sat_Z AOXY_sat_Z g1 φ1
    /\ Y_sat_Z g2 φ2
| ao_app_operand _ _, _ => False
| ao_app_ao g1 g2, ao_app_ao φ1 φ2 => 
    aoxy_satisfies_aoxz_comp Y_sat_Z AOXY_sat_Z g1 φ1
    /\ aoxy_satisfies_aoxz_comp Y_sat_Z AOXY_sat_Z g2 φ2
| ao_app_ao g1 g2, ao_app_operand φ1 φ2 =>
    aoxy_satisfies_aoxz_comp Y_sat_Z AOXY_sat_Z g1 φ1
    /\ AOXY_sat_Z g2 φ2
| ao_app_ao _ _, _ => False
end.


Definition aoxyo_satisfies_aoxzo_comp
    {X Y Z : Set}
    (Y_sat_Z : Y -> Z -> Prop)
    (AOXY_sat_Z : AppliedOperator' X Y -> Z -> Prop):
    AppliedOperatorOr' X Y ->
    AppliedOperatorOr' X Z ->
    Prop :=
fun g φ =>
match g, φ with
| aoo_app _ _ g0, aoo_app _ _ φ0 => aoxy_satisfies_aoxz_comp Y_sat_Z AOXY_sat_Z g0 φ0
| aoo_operand _ _ g0, aoo_operand _ _ φ0 => Y_sat_Z g0 φ0
| aoo_app _ _ g0, aoo_operand _ _ φ0 => AOXY_sat_Z g0 φ0
| aoo_operand _ _ _, aoo_app _ _ _ => False
end.


Definition LhsPattern_to_pair_OpenTerm_SC
    {Σ : Signature}
    (l : LhsPattern)
    : (OpenTerm * (list SideCondition))
:= 
(
    AppliedOperatorOr'_symbol_A_to_OpenTermB getBase l,
    AppliedOperatorOr'_symbol_A_to_SCS getSCS l
).

Definition lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm
    {Σ : Signature}
    (lox : LocalRewriteOrOpenTermOrBOV)
    : OpenTerm
:=
match lox with
| lp_rewrite r => AppliedOperatorOr'_symbol_A_to_OpenTermB getBase (lr_from r)
| lp_basicpat φ => φ
| lp_bov bov => aoo_operand _ _ bov
end.

Definition lhs_LocalRewriteOrOpenTermOrBOV_to_SCS
    {Σ : Signature}
    (lox : LocalRewriteOrOpenTermOrBOV)
    : list SideCondition
:=
match lox with
| lp_rewrite r => AppliedOperatorOr'_symbol_A_to_SCS getSCS (lr_from r)
| lp_basicpat φ => [] (* we would use `getSCS φ` if it had a side condition *)
| lp_bov bov => []
end.

Definition lhs_UncondRewritingRule_to_OpenTerm
    {Σ : Signature}
    (ur : UncondRewritingRule)
    : OpenTerm
:=
    AppliedOperatorOr'_symbol_A_to_OpenTermB lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm ur
.

Definition lhs_UncondRewritingRule_to_SCS
    {Σ : Signature}
    (ur : UncondRewritingRule)
    : list SideCondition
:=
    AppliedOperatorOr'_symbol_A_to_SCS lhs_LocalRewriteOrOpenTermOrBOV_to_SCS ur
.

Definition lhs_RewritingRule_to_OpenTerm
    {Σ : Signature}
    (r : RewritingRule)
    : OpenTerm
:=
    lhs_UncondRewritingRule_to_OpenTerm (getBase r)
.

Definition lhs_RewritingRule_to_SCS
    {Σ : Signature}
    (r : RewritingRule)
    : list SideCondition
:=
    lhs_UncondRewritingRule_to_SCS (getBase r)
    ++ getSCS r
.

Definition BOV_to_Expression
    {Σ : Signature}
    (bov : BuiltinOrVar)
    : Expression
:=
match bov with
| bov_builtin b => ft_element (aoo_operand _ _ b)
| bov_variable x => ft_variable x
end.

Fixpoint AppliedOperator'_fmap
    {A B C : Set}
    (f : B -> C)
    (ao : AppliedOperator' A B)
    : AppliedOperator' A C
:=
match ao with
| ao_operator o => ao_operator o
| ao_app_operand ao' x => ao_app_operand (AppliedOperator'_fmap f ao') (f x)
| ao_app_ao ao1 ao2 => ao_app_ao (AppliedOperator'_fmap f ao1) (AppliedOperator'_fmap f ao2)
end.

Definition AppliedOperatorOr'_fmap
    {A B C : Set}
    (f : B -> C)
    (aoo : AppliedOperatorOr' A B)
    : AppliedOperatorOr' A C
:=
match aoo with
| aoo_app _ _ ao => aoo_app _ _ (AppliedOperator'_fmap f ao)
| aoo_operand _ _ o => aoo_operand _ _ (f o)
end.


Definition rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern
    {Σ : Signature}
    (lox : LocalRewriteOrOpenTermOrBOV)
    : RhsPattern
:=
match lox with
| lp_rewrite r => (lr_to r)
| lp_basicpat φ =>
    AppliedOperatorOr'_fmap BOV_to_Expression φ
| lp_bov bov => aoo_operand _ _ (BOV_to_Expression bov)
end.

Definition rhs_UncondRewritingRule_to_RhsPattern
    {Σ : Signature}
    (ur : UncondRewritingRule)
    : RhsPattern
:=
    AppliedOperatorOr'_symbol_A_to_OpenTermB rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern ur
.

Definition rhs_RewritingRule_to_RhsPattern
    {Σ : Signature}
    (r : RewritingRule)
    : RhsPattern
:=
    rhs_UncondRewritingRule_to_RhsPattern (getBase r)
.

Definition RewritingRule_to_FlattenedRewritingRule
    {Σ : Signature}
    (r : RewritingRule)
    : FlattenedRewritingRule
:=
{|
    fr_from := lhs_RewritingRule_to_OpenTerm r ;
    fr_to := rhs_RewritingRule_to_RhsPattern r ;
    fr_scs := lhs_RewritingRule_to_SCS r ;
|}.

Print RewritingRule.


Lemma A_satisfies_B_WithASideCondition_comp_iff
    {Σ : Signature}
    (A B : Set)
    (A_sat_B : A -> B -> Prop)
    (ρ : Valuation)
    (a : A)
    (wscb : WithASideCondition B)
    :
    A_satisfies_B_WithASideCondition A B A_sat_B ρ a wscb
    <->
    A_satisfies_B_WithASideCondition_comp A B A_sat_B ρ a wscb
.
Proof.
    induction wscb; cbn.
    {
        split; intros H.
        {
            inversion H; subst; clear H.
            assumption.
        }
        {
            constructor. assumption.
        }
    }
    {
        split; intros H.
        {
            inversion H; subst; clear H.
            ltac1:(naive_solver).
        }
        {
            constructor; ltac1:(naive_solver).
        }
    }
Qed.


Lemma getSCS_getBase_correct
    {Σ : Signature}
    {A B : Set}
    (A_sat_B : A -> B -> Prop)
    (wscb : WithASideCondition B)
    (a : A)
    (ρ : Valuation)
    : 
    (A_sat_B a (getBase wscb) /\ valuation_satisfies_scs ρ (getSCS wscb))
    <->
    A_satisfies_B_WithASideCondition A B A_sat_B ρ a wscb
.
Proof.
    unfold valuation_satisfies_scs.
    revert a;
    induction wscb; intros a; cbn.
    {
        split.
        {
            intros [H1 H2].
            constructor.
            assumption.
        }
        {
            intros H.
            inversion H; subst; clear H.
            split.
            { assumption. }
            { apply Forall_nil. }
        }
    }
    {
        ltac1:(rewrite Forall_cons_iff).
        rewrite A_satisfies_B_WithASideCondition_comp_iff.
        specialize (IHwscb a).
        rewrite A_satisfies_B_WithASideCondition_comp_iff in IHwscb.
        cbn.
        ltac1:(naive_solver).
    }
Qed.


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


Lemma aoxy_satisfies_aoxz_comp_iff
    {X Y Z : Set}
    (Y_sat_Z : Y -> Z -> Prop)
    (AOXY_sat_Z : AppliedOperator' X Y -> Z -> Prop)
    (g : AppliedOperator' X Y)
    (φ : AppliedOperator' X Z)
    :
    aoxy_satisfies_aoxz_comp Y_sat_Z AOXY_sat_Z g φ
    <->
    @aoxy_satisfies_aoxz _ _ _ Y_sat_Z AOXY_sat_Z g φ
.
Proof.
    revert g.
    induction φ; intros gg; destruct gg; cbn; split; intros HH;
        inversion HH; subst; try constructor;
        try ltac1:(naive_solver).
Qed.


Lemma aoxyo_satisfies_aoxzo_comp_iff
    {X Y Z : Set}
    (Y_sat_Z : Y -> Z -> Prop)
    (AOXY_sat_Z : AppliedOperator' X Y -> Z -> Prop)
    (g : AppliedOperatorOr' X Y)
    (φ : AppliedOperatorOr' X Z)
    :
    aoxyo_satisfies_aoxzo_comp Y_sat_Z AOXY_sat_Z g φ
    <->
    @aoxyo_satisfies_aoxzo _ _ _ Y_sat_Z AOXY_sat_Z g φ
.
Proof.
    destruct g,φ.
    {
        cbn.
        rewrite aoxy_satisfies_aoxz_comp_iff.
        split; intros H; try constructor; try assumption.
        inversion H; subst. assumption.
    }
    all: split; cbn; intros HH; try (inversion HH); try constructor; cbn; try assumption.
Qed.

Lemma correct_AppliedOperator'_symbol_A_to_OpenTerm
    {Σ : Signature}
    {A B : Set}
    (A_to_OpenTermB : A -> AppliedOperatorOr' symbol B)
    (A_to_SC : A -> list SideCondition )
    (GroundTerm_satisfies_A:
        Valuation ->
        GroundTerm ->
        A ->
        Prop
    )
    (AppliedOperator'_symbol_builtin_satisfies_B:
            Valuation ->
            AppliedOperator' symbol builtin_value ->
            B ->
            Prop
    )
    (builtin_satisfies_B:
        Valuation ->
        builtin_value ->
        B ->
        Prop
    )
    (ρ : Valuation)
    (correct_underlying:
        ∀ γ a,
            (
                @aoxyo_satisfies_aoxzo
        symbol
        builtin_value
        B
        (builtin_satisfies_B ρ)
        (AppliedOperator'_symbol_builtin_satisfies_B ρ)
                γ
                (A_to_OpenTermB a)
            /\
                valuation_satisfies_scs ρ (A_to_SC a)
            )
            <->
            GroundTerm_satisfies_A ρ γ a
    )
    (x : AppliedOperatorOr' symbol A)
    (g : GroundTerm)
    :
    (
        @aoxyo_satisfies_aoxzo
            symbol
            builtin_value
            B
            (builtin_satisfies_B ρ)
            (AppliedOperator'_symbol_builtin_satisfies_B ρ)
            g
            (AppliedOperatorOr'_symbol_A_to_OpenTermB A_to_OpenTermB x)
        /\ (valuation_satisfies_scs
             ρ
             (AppliedOperatorOr'_symbol_A_to_SCS A_to_SC x)
            )

    )
    <->
    @aoxyo_satisfies_aoxzo
        symbol
        builtin_value
        A
        (fun b => GroundTerm_satisfies_A ρ (aoo_operand _ _ b))
        (fun t => GroundTerm_satisfies_A ρ (aoo_app _ _ t))
        g x
.
Proof.
    unfold in_val_GroundTerm_satisfies_OpenTerm in *.
    unfold in_val_GroundTerm_satisfies_OpenTerm in *.
    unfold aoosb_satisfies_aoosbf in *.
    destruct x, g; cbn.
    {
        repeat (rewrite <- aoxyo_satisfies_aoxzo_comp_iff).
        unfold valuation_satisfies_scs.


        revert ao0; induction ao; cbn in *; intros ao0.
        {
            destruct ao0; cbn; try ltac1:(naive_solver).
        }
        {
            repeat ltac1:(case_match); cbn in *;
            destruct ao0; cbn.
            1,4: ltac1:(naive_solver).
            {
                split; intros HH.
                {
                    destruct HH as [HH1 HH2].
                    inversion HH1.
                }
                {
                    ltac1:(exfalso).
                    destruct HH as [HH1 HH2].
                    rewrite <- correct_underlying in HH2; cbn.
                    destruct HH2 as [HH21 HH22].
                    inversion HH21; subst.
                    rewrite H in H2; cbn.
                    inversion H2.
                }
            }
            {
                rewrite <- IHao.
                ltac1:(rewrite Forall_app).
                ltac1:(rewrite -correct_underlying).
                ltac1:(rewrite -aoxyo_satisfies_aoxzo_comp_iff).
                cbn.
                rewrite H.
                unfold valuation_satisfies_scs.
                clear.
                ltac1:(naive_solver).
            }
            {
                ltac1:(rewrite -IHao).
                ltac1:(rewrite -correct_underlying).
                ltac1:(rewrite -aoxyo_satisfies_aoxzo_comp_iff).
                cbn.
                rewrite H.
                rewrite Forall_app.
                unfold valuation_satisfies_scs.
                clear.
                ltac1:(naive_solver).
            }
            {
                ltac1:(rewrite -IHao).
                ltac1:(rewrite -correct_underlying).
                ltac1:(rewrite -aoxyo_satisfies_aoxzo_comp_iff).
                cbn.
                rewrite H.
                unfold valuation_satisfies_scs.
                rewrite Forall_app; cbn.
                clear.
                ltac1:(naive_solver).
            }
        }
        {
            destruct ao0; cbn.
            {
                clear. ltac1:(naive_solver).
            }
            {
                clear. ltac1:(naive_solver).
            }
            {
                ltac1:(rewrite -IHao1);
                ltac1:(rewrite -IHao2).
                rewrite Forall_app.
                clear.
                ltac1:(naive_solver).
            }
        }
    }
    {
        repeat (rewrite <- aoxyo_satisfies_aoxzo_comp_iff).
        cbn.
        ltac1:(naive_solver).
    }
    {
        repeat (rewrite <- aoxyo_satisfies_aoxzo_comp_iff).
        cbn.
        ltac1:(rewrite -correct_underlying).
        repeat (rewrite <- aoxyo_satisfies_aoxzo_comp_iff).
        cbn.
        reflexivity.
    }
    {
        specialize (correct_underlying (aoo_operand _ _ operand0) operand).
        repeat (rewrite <- aoxyo_satisfies_aoxzo_comp_iff).
        cbn.
        rewrite <- aoxyo_satisfies_aoxzo_comp_iff in correct_underlying.
        cbn in correct_underlying.
        apply correct_underlying.
    }
Qed.



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
