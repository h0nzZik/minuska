Require Import Logic.PropExtensionality.
From Coq Require Import Setoid.

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

Definition builtin_satisfies_BuiltinOrVar_comp
    {Σ : Signature}
    (ρ : Valuation)
    (b : builtin_value)
    (bov : BuiltinOrVar)
    : Prop
:=
match bov with
| bov_builtin b' => b = b'
| bov_variable x => ρ !! x = Some (aoo_operand _ _ b)
end.

Lemma builtin_satisfies_BuiltinOrVar_comp_iff
    {Σ : Signature}
    (ρ : Valuation)
    (b : builtin_value)
    (bov : BuiltinOrVar):
    builtin_satisfies_BuiltinOrVar ρ b bov
    <-> builtin_satisfies_BuiltinOrVar_comp ρ b bov
.
Proof.
    destruct bov; cbn; split; intros H; subst; try (inversion H; subst); try constructor; try assumption.
Qed.

Lemma correct_rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern
    {Σ : Signature} lro
    (ρ : Valuation)
    (g : GroundTerm):
    GroundTerm_satisfies_RhsPattern
        ρ
        g
        (rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern lro)
    <->
    GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
        ρ
        LR_Right
        g
        lro
.
Proof.
    unfold GroundTerm_satisfies_RhsPattern.
    unfold GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV.
    unfold rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern.
    destruct lro; cbn.
    {
        unfold GroundTerm_satisfies_right_LocalRewrite.
        unfold GroundTerm_satisfies_RhsPattern.
        ltac1:(naive_solver).
    }
    {
        unfold in_val_GroundTerm_satisfies_OpenTerm.
        unfold BOV_to_Expression.
        unfold aoosb_satisfies_aoosbf.
        do 2 (rewrite <- aoxyo_satisfies_aoxzo_comp_iff).
        cbn.
        destruct φ,g; cbn.
        {
            revert ao.
            induction ao0; cbn; intros ao.
            {
                repeat (ltac1:(case_match)); subst; inversion H; subst;
                    ltac1:(naive_solver).
            }
            {
                (repeat (ltac1:(case_match))); subst; inversion H; subst; clear H;
                    simpl in *; try ltac1:(naive_solver).
                do 1 (rewrite <- IHao0). clear IHao0.
                destruct b1; simpl in *;
                rewrite builtin_satisfies_BuiltinOrVar_comp_iff;
                cbn;
                split; intros H;
                ltac1:(naive_solver).
            }
            {
                unfold AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar in *.
                (repeat (ltac1:(case_match))); subst; inversion H; subst; clear H;
                    simpl in *; try ltac1:(naive_solver).
            }
        }
        {
            ltac1:(naive_solver).
        }
        {
            unfold AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar.
            destruct operand; simpl in *.
            split; intros H; inversion H.
            ltac1:(naive_solver).
        }
        {
            unfold AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar.
            destruct operand; simpl in *.
            split; intros H; inversion H; subst; constructor.
            ltac1:(rewrite builtin_satisfies_BuiltinOrVar_comp_iff).
            simpl.
            ltac1:(naive_solver).
        }
    }
    {

        ltac1:(rewrite -aoxyo_satisfies_aoxzo_comp_iff).
        destruct bx,g; cbn.
        {
            split; intros H; inversion H.
        }
        {
            split; intros H; inversion H;
            subst; reflexivity.
        }
        {
            reflexivity.
        }
        {
            reflexivity.
        }
    }
Qed.

Lemma correct_AppliedOperator'_symbol_A_to_OpenTerm
    {Σ : Signature}
    {A B : Set}
    (A_to_OpenTermB : A -> AppliedOperatorOr' symbol B)
    (A_to_SC : A -> list SideCondition )
    (GroundTerm_satisfies_A:
        GroundTerm ->
        A ->
        Prop
    )
    (AppliedOperator'_symbol_builtin_satisfies_B:
            AppliedOperator' symbol builtin_value ->
            B ->
            Prop
    )
    (builtin_satisfies_B:
        builtin_value ->
        B ->
        Prop
    )
    (ρ : Valuation)
    (x : AppliedOperatorOr' symbol A)
    (g : GroundTerm)
    :
    (
        ∀ γ a,
            (
                @aoxyo_satisfies_aoxzo
        symbol
        builtin_value
        B
        (builtin_satisfies_B)
        (AppliedOperator'_symbol_builtin_satisfies_B)
                γ
                (A_to_OpenTermB a)
            /\
                valuation_satisfies_scs ρ (A_to_SC a)
            )
            <->
            GroundTerm_satisfies_A γ a
    )
    ->
    ((
        @aoxyo_satisfies_aoxzo
            symbol
            builtin_value
            B
            (builtin_satisfies_B)
            (AppliedOperator'_symbol_builtin_satisfies_B)
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
        ((GroundTerm_satisfies_A) ∘ (aoo_operand _ _))
        ((GroundTerm_satisfies_A) ∘ (aoo_app _ _))
        g x
    )
.
Proof.
    intros correct_underlying.
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

Lemma builtin_satisfies_LocalRewriteOrOpenTermOrBOV_iff_GroundTerm
    {Σ : Signature}
    (ρ : Valuation)
    (lr : LeftRight)
    :
    (builtin_satisfies_LocalRewriteOrOpenTermOrBOV ρ lr)
    =
    (GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV ρ lr) ∘ (aoo_operand _ _)
.
Proof.
    apply functional_extensionality.
    intros b.
    apply functional_extensionality.
    intros rb.
    apply propositional_extensionality.
    unfold compose.
    destruct rb.
    { ltac1:(naive_solver). }
    {
        destruct φ.
        split; intros H; inversion H.
        split; intros H; inversion H; subst; clear H.
        {
            constructor.
            constructor.
        }
        {
            constructor. constructor. assumption.
        }
        {
            assumption.
        }
    }
    {

        destruct bx; split; cbn; intros H.
        {
            inversion H. reflexivity.
        }
        {
            subst. constructor.
        }
        {
            inversion H. assumption.
        }
        {
            constructor. assumption.
        }
    }
Qed.

Theorem correct_RewritingRule_to_FlattenedRewritingRule
    {Σ : Signature}
    (r : RewritingRule)
    (ρ : Valuation)
    (from to : GroundTerm)
    :
    flattened_rewrites_in_valuation_to
        ρ
        (RewritingRule_to_FlattenedRewritingRule r)
        from to
    <->
    rewrites_in_valuation_to ρ r from to
.
Proof.
    unfold flattened_rewrites_in_valuation_to.
    unfold rewrites_in_valuation_to.
    unfold in_val_GroundTerm_satisfies_OpenTerm.
    unfold GroundTerm_satisfies_RhsPattern.
    unfold GroundTerm_satisfies_RewritingRule.
    unfold GroundTerm.
    unfold GroundTerm'.
    unfold UncondRewritingRule.
    unfold GroundTerm_satisfies_UncondRewritingRule.
    unfold aoosb_satisfies_aoosbf.

    cbn.
    do 2 (rewrite <- getSCS_getBase_correct).
    do 2 (rewrite builtin_satisfies_LocalRewriteOrOpenTermOrBOV_iff_GroundTerm).

    Set Printing Implicit.
    set (P1 := aoxyo_satisfies_aoxzo from (lhs_RewritingRule_to_OpenTerm r)).
    set (P2 := aoxyo_satisfies_aoxzo to (rhs_RewritingRule_to_RhsPattern r)).
    set (P3 := valuation_satisfies_scs ρ (lhs_RewritingRule_to_SCS r)).
    set (P4 := (@aoxyo_satisfies_aoxzo (@symbol Σ) (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ))
  (@LocalRewriteOrOpenTermOrBOV Σ)
  (@GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV Σ ρ LR_Left
∘ aoo_operand (@symbol Σ) (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)))
  (@GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV Σ ρ LR_Left
∘ aoo_app (@symbol Σ) (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)))
  from
  (@getBase Σ (AppliedOperatorOr' (@symbol Σ) (@LocalRewriteOrOpenTermOrBOV Σ)) r))).

    set ( P5 := @valuation_satisfies_scs Σ ρ
  (@getSCS Σ (AppliedOperatorOr' (@symbol Σ) (@LocalRewriteOrOpenTermOrBOV Σ)) r)).
    set (P6 := @aoxyo_satisfies_aoxzo (@symbol Σ) (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ))
  (@LocalRewriteOrOpenTermOrBOV Σ)
  (@GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV Σ ρ LR_Right
∘ aoo_operand (@symbol Σ) (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)))
  (@GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV Σ ρ LR_Right
∘ aoo_app (@symbol Σ) (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)))
  to
  (@getBase Σ (AppliedOperatorOr' (@symbol Σ) (@LocalRewriteOrOpenTermOrBOV Σ)) r))
    .
    Unset Printing Implicit.

    ltac1:(cut (((P1 /\ P2 /\ P3) <-> (P4 /\ P5 /\ P6)))).
    {
        ltac1:(naive_solver).
    }
    unfold lhs_RewritingRule_to_OpenTerm in P1; cbn.
    unfold rhs_RewritingRule_to_RhsPattern in P2; cbn.
    unfold lhs_RewritingRule_to_SCS in P3; cbn.
    unfold valuation_satisfies_scs in *.
    set (P31 := Forall (valuation_satisfies_sc ρ) (lhs_UncondRewritingRule_to_SCS (getBase r))).
    set (P32 := Forall (valuation_satisfies_sc ρ) (getSCS r)).
    assert (H : P3 <-> P31 /\ P32).
    {
        ltac1:(unfold P3,P31,P32).
        apply Forall_app.
    }

    ltac1:(cut (P1 ∧ P2 ∧ P31 ∧ P32 ↔ P4 ∧ P5 ∧ P6)).
    {
        ltac1:(naive_solver).
    }
    clear H. clear P3.

    unfold lhs_UncondRewritingRule_to_OpenTerm in *.    
    assert (L1 := @correct_AppliedOperator'_symbol_A_to_OpenTerm Σ _ BuiltinOrVar
        (lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm) (lhs_LocalRewriteOrOpenTermOrBOV_to_SCS)
        (GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV ρ LR_Left)
        (AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ)
        (builtin_satisfies_BuiltinOrVar ρ)
        ρ (getBase r) from).
    ltac1:(feed specialize L1).
    {
        clear L1.
        intros.
        unfold GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV.
        destruct a.
        {
            unfold GroundTerm_satisfies_LocalRewrite.
            unfold GroundTerm_satisfies_left_LocalRewrite.
            unfold GroundTerm_satisfies_LhsPattern.
            destruct r0; simpl in *.
            
            ltac1:(replace ((@builtin_value_satisfies_OpenTermWSC Σ ρ))
            with ((in_val_GroundTerm_satisfies_OpenTermWSC ρ) ∘ (aoo_operand _ _))).
            2: {
                apply functional_extensionality.
            }
            Set Printing Implicit.
            rewrite correct_AppliedOperator'_symbol_A_to_OpenTerm.
            unfold AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC.
            (* Set Debug "tactic-unification". *)
            (*unfold builtin_satisfies_BuiltinOrVar.*)
            (*About correct_AppliedOperator'_symbol_A_to_OpenTerm.*)
            (* ltac1:(simple apply correct_AppliedOperator'_symbol_A_to_OpenTerm). *)
        }
    }
    rewrite L1.




    unfold GroundTerm,GroundTerm' in from.
    About correct_AppliedOperator'_symbol_A_to_OpenTerm.
    Check lhs_RewritingRule_to_OpenTerm.

    rewrite <- (@correct_AppliedOperator'_symbol_A_to_OpenTerm Σ _ BuiltinOrVar
        (lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm) (lhs_LocalRewriteOrOpenTermOrBOV_to_SCS)
        (GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV ρ LR_Left)
        (AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ)
        (builtin_satisfies_BuiltinOrVar ρ)
        ρ 
        ) in P4.
    
    {
        rewrite <- (@correct_AppliedOperator'_symbol_A_to_OpenTerm Σ _ Expression
        (rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern) (lhs_LocalRewriteOrOpenTermOrBOV_to_SCS)
        (GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV ρ LR_Right)
        (fun ao e => Expression_evaluate ρ e = Some (aoo_app _ _ ao))
        ((fun b e => Expression_evaluate ρ e = Some (aoo_operand _ _ b)))
        ρ).
        {

            Check @correct_AppliedOperator'_symbol_A_to_OpenTerm.
            Set Printing Implicit.
            unfold lhs_RewritingRule_to_OpenTerm.
            unfold rhs_RewritingRule_to_RhsPattern.
            unfold lhs_RewritingRule_to_SCS.
            unfold valuation_satisfies_scs.
            rewrite Forall_app.
            unfold UncondRewritingRule; cbn in *.
            remember (Forall (valuation_satisfies_sc ρ) (getSCS r)) as P1.
            
            unfold UncondRewritingRule in HeqP1; cbn in *.
            ltac1:(rewrite -correct_rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern).
            Check correct_rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern.
            *)
            
            (*
            unfold lhs_UncondRewritingRule_to_OpenTerm.
            unfold rhs_UncondRewritingRule_to_RhsPattern.
            unfold lhs_UncondRewritingRule_to_SCS.

            unfold UncondRewritingRule.
            remember (Forall (valuation_satisfies_sc ρ)) as FA1.
            remember ((@aoxyo_satisfies_aoxzo (@symbol Σ)
  (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ))
  (@BuiltinOrVar Σ) (@builtin_satisfies_BuiltinOrVar Σ ρ)
  (@AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar Σ ρ) from
  (@AppliedOperatorOr'_symbol_A_to_OpenTermB Σ
  (@LocalRewriteOrOpenTermOrBOV Σ) (@BuiltinOrVar Σ)
  (@lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm Σ)
  (@getBase Σ
  (AppliedOperatorOr' (@symbol Σ) (@LocalRewriteOrOpenTermOrBOV Σ))
  r)))) as P2'.

  
            remember (@aoxyo_satisfies_aoxzo (@symbol Σ)
  (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)) (@Expression Σ)
  (λ (b : @builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)) (e : @Expression
  Σ),
  @Expression_evaluate Σ ρ e =
@Some
  (AppliedOperatorOr' (@symbol Σ)
  (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)))
  (aoo_operand (@symbol Σ)
  (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)) b))
  (λ (ao : AppliedOperator' (@symbol Σ)
  (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ))) (e : @Expression
  Σ),
  @Expression_evaluate Σ ρ e =
@Some
  (AppliedOperatorOr' (@symbol Σ)
  (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)))
  (aoo_app (@symbol Σ)
  (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)) ao))
  to
  (@AppliedOperatorOr'_symbol_A_to_OpenTermB Σ
  (@LocalRewriteOrOpenTermOrBOV Σ) (@Expression Σ)
  (@rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern Σ)
  (@getBase Σ
  (AppliedOperatorOr' (@symbol Σ) (@LocalRewriteOrOpenTermOrBOV Σ))
  r))) as P3.

            cbn.

            Set Printing Implicit.


            ltac1:(naive_solver).
            
            split; intros H; apply H.
            *)
        }
    }
    (*
    rewrite <- (@correct_AppliedOperator'_symbol_A_to_OpenTerm Σ _ BuiltinOrVar).
    {
        rewrite <- (@correct_AppliedOperator'_symbol_A_to_OpenTerm Σ _ BuiltinOrVar).
    }
    {
        in
    }
    unfold AppliedOperatorOr'_symbol_A_to_OpenTermB.

    
    unfold lhs_RewritingRule_to_OpenTerm.
    unfold rhs_RewritingRule_to_RhsPattern.
    unfold lhs_UncondRewritingRule_to_OpenTerm.
    unfold rhs_UncondRewritingRule_to_RhsPattern.
    unfold lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm.
    unfold rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern.
    unfold lhs_RewritingRule_to_SCS.
    unfold lhs_UncondRewritingRule_to_SCS.
    cbn.
    Set Printing Implicit.
    rewrite correct_AppliedOperator'_symbol_A_to_OpenTerm; cbn.

    Check correct_AppliedOperator'_symbol_A_to_OpenTerm.
    Search 
    aoxyo_satisfies_aoxzo .
    unfold A_satisfies_B_WithASideCondition.

    Check correct_AppliedOperator'_symbol_A_to_OpenTerm.

    (*
    (*ltac1:(rewrite -A_satisfies_B_WithASideCondition_iff).*)
    rewrite <- (@A_satisfies_B_WithASideCondition_iff Σ (@LocalRewriteOrOpenTermOrBOV Σ)).
    *)
    *)
Qed.