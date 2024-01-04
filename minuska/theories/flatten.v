Require Import Logic.PropExtensionality.
From Coq Require Import Setoid.

From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    flattened
    basic_matching
.

Fixpoint AppliedOperator'_size
    {Operator Operand : Type}
    (x : AppliedOperator' Operator Operand)
    : nat :=
match x with
| ao_operator _ => 1
| ao_app_operand x' _ => 1 + AppliedOperator'_size x'
| ao_app_ao x1 x2 => 1 + AppliedOperator'_size x1 + AppliedOperator'_size x2
end.

Definition AppliedOperatorOr'_deep_size
    {Operator Operand : Type}
    (x : AppliedOperatorOr' Operator Operand)
    : nat :=
match x with
| aoo_operand _ _ o => 1
| aoo_app _ _ x' => 1 + AppliedOperator'_size x'
end.

Print AppliedOperatorOr'.

Fixpoint AppliedOperator'_operands
    (Operator Operand : Type)
    (a : AppliedOperator' Operator Operand)
    : list Operand
:=
match a with
| ao_operator _ => []
| ao_app_operand a' o => o::(AppliedOperator'_operands Operator Operand a')
| ao_app_ao a1 a2 => (AppliedOperator'_operands Operator Operand a1) ++ (AppliedOperator'_operands Operator Operand a2)
end.

Definition AppliedOperatorOr'_operands
    (Operator Operand : Type)
    (a : AppliedOperatorOr' Operator Operand)
    : list Operand
:=
match a with
| aoo_app _ _ a' => AppliedOperator'_operands Operator Operand a'
| aoo_operand _ _ o => [o]
end.



Fixpoint separate_scs
    {Σ : Signature}
    {A : Type}
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

Fixpoint getSCS {Σ : Signature} {A : Type} (wsc : WithASideCondition A):
    list SideCondition
:=
match wsc with
| wsc_base _ => []
| wsc_sc wsc' sc => sc::(getSCS wsc')
end.

Fixpoint getBase {Σ : Signature} {A : Type} (wsc : WithASideCondition A):
    A
:=
match wsc with
| wsc_base a => a
| wsc_sc wsc' _ => getBase wsc'
end.


Lemma separate_scs_getSCS_getBase
    {Σ : Signature} {A : Type}
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
    {A : Type}
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
    {A : Type}
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
    {A B : Type}
    (A_to_OpenTermB : A ->
        ((AppliedOperatorOr' symbol B))
    )
    (x : AppliedOperator' symbol A)
    : ((AppliedOperator' symbol B))
:=
match x with
| ao_operator a => (ao_operator a)
| ao_app_operand x' a =>
    let t1 : (AppliedOperator' symbol B)
        := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x' in
    match A_to_OpenTermB a with
    | (aoo_app _ _ t2) => (ao_app_ao t1 t2)
    | (aoo_operand _ _ t2) => (ao_app_operand t1 t2)
    end
| ao_app_ao x1 x2 =>
    let t1 : (AppliedOperator' symbol B)
        := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x1 in
    let t2 : (AppliedOperator' symbol B)
        := AppliedOperator'_symbol_A_to_OpenTermB A_to_OpenTermB x2 in
    ao_app_ao t1 t2
end.

Definition AppliedOperatorOr'_symbol_A_to_OpenTermB
    {Σ : Signature}
    {A B : Type}
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

(*
Fixpoint A_satisfies_B_WithASideCondition_comp
    {Σ : Signature}
    (A B : Type)
    `{Satisfies (Valuation*A) B}
    (ρa : Valuation*A)
    (wscb : WithASideCondition B)
:=
let ρ := ρa.1 in
match wscb with
| wsc_base b => satisfies ρa b
| wsc_sc wscb' sc =>
    A_satisfies_B_WithASideCondition_comp A B ρa wscb'
    /\ satisfies ρ sc
end
.

Fixpoint aoxy_satisfies_aoxz_comp
    {V X Y Z : Type}
    `{Satisfies (V*Y) Z}
    `{Satisfies (V*(AppliedOperator' X Y)) Z}
    (ρ : V)
    (g : AppliedOperator' X Y)
    (φ : AppliedOperator' X Z):
    Prop :=
match g, φ with
| ao_operator x1, ao_operator x2
    => x1 = x2

| ao_operator _, _
    => False

| ao_app_operand g1 g2, ao_app_operand φ1 φ2
    => aoxy_satisfies_aoxz_comp ρ g1 φ1
    /\ satisfies (ρ,g2) φ2

| ao_app_operand _ _, _
    => False

| ao_app_ao g1 g2, ao_app_ao φ1 φ2
    => aoxy_satisfies_aoxz_comp ρ g1 φ1
    /\ aoxy_satisfies_aoxz_comp ρ g2 φ2

| ao_app_ao g1 g2, ao_app_operand φ1 φ2
    => aoxy_satisfies_aoxz_comp ρ g1 φ1
    /\ satisfies (ρ,g) φ2

| ao_app_ao _ _, _ => False
end.



*)

Definition aoxyo_satisfies_aoxzo_bool
    `{CΣ : ComputableSignature}
    {Y Z : Type}
    `{Matches (Valuation*Y) Z }
    `{Matches (Valuation*(AppliedOperator' symbol Y)) Z}
    `{Matches (Valuation * AppliedOperator' symbol Y) (AppliedOperator' symbol Z)}
    :
    (Valuation*(AppliedOperatorOr' symbol Y)) ->
    AppliedOperatorOr' symbol Z ->
    bool :=
fun ρg φ =>
let ρ := ρg.1 in
let g := ρg.2 in
match g, φ with
| aoo_app _ _ g0, aoo_app _ _ φ0
    => matchesb (ρ, g0) φ0

| aoo_operand _ _ g0, aoo_operand _ _ φ0
    => matchesb (ρ,g0) φ0

| aoo_app _ _ g0, aoo_operand _ _ φ0
    => matchesb (ρ,g0) φ0

| aoo_operand _ _ _, aoo_app _ _ _
    => false
end.

#[export]
Program Instance Matches__aoxyo_satisfies_aoxzo_bool
    `{CΣ : ComputableSignature}
    {Y Z : Type}
    `{Matches (Valuation*Y) Z }
    `{Matches (Valuation*(AppliedOperator' symbol Y)) Z}
    `{Matches (Valuation * AppliedOperator' symbol Y) (AppliedOperator' symbol Z)}
    :
    Matches ((Valuation*(AppliedOperatorOr' symbol Y))) (AppliedOperatorOr' symbol Z)
:= {|
    matchesb := aoxyo_satisfies_aoxzo_bool ;
|}.
Next Obligation.
    destruct a,b; simpl.
    {
        unfold satisfies.
        unfold aoxyo_satisfies_aoxzo_bool.
        simpl.
        apply iff_reflect.
        split; intros HH.
        {
            inversion HH; subst; clear HH.
            eapply introT.
            { apply matchesb_satisfies. }
            assumption.
        }
        {
            constructor.
            eapply elimT.
            { apply matchesb_satisfies. }
            assumption.
        }
    }
    {
        unfold satisfies.
        unfold aoxyo_satisfies_aoxzo_bool.
        simpl.
        apply iff_reflect.
        split; intros HH.
        {
            inversion HH; subst; clear HH.
            eapply introT.
            { apply matchesb_satisfies. }
            assumption.
        }
        {
            constructor.
            eapply elimT.
            { apply matchesb_satisfies. }
            assumption.
        }
    }
    {
        unfold satisfies.
        unfold aoxyo_satisfies_aoxzo_bool.
        simpl.
        apply iff_reflect.
        split; intros HH.
        {
            inversion HH.
        }
        {
            inversion HH.
        }
    }
    {
        unfold satisfies.
        unfold aoxyo_satisfies_aoxzo_bool.
        simpl.
        apply iff_reflect.
        split; intros HH.
        {
            inversion HH; subst; clear HH.
            eapply introT.
            { apply matchesb_satisfies. }
            assumption.
        }
        {
            constructor.
            eapply elimT.
            { apply matchesb_satisfies. }
            assumption.
        }
    }
Qed.
Fail Next Obligation.

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



Definition rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern
    {Σ : Signature}
    (lox : LocalRewriteOrOpenTermOrBOV)
    : RhsPattern
:=
match lox with
| lp_rewrite r => (lr_to r)
| lp_basicpat φ =>
    BOV_to_Expression <$> φ
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

Definition enables_match
    {Σ : Signature}
    (vars : gset variable)
    (m : Match)
: Prop :=
    (m_variable m) ∈ vars
.

#[export]
Instance enables_match_dec
    {Σ : Signature}
    (vars : gset variable)
    (m : Match)
    : Decision (enables_match vars m)
.
Proof.
    unfold enables_match.
    ltac1:(solve_decision).
Defined.

Definition choose_first_enabled_match
    {Σ : Signature}
    (initial_vars : gset variable)
    (matches : list Match)
: option (nat*Match * list Match)%type
:=
    found ← list_find (enables_match initial_vars) matches;
    match found with
    | (i, m) => Some (i, m, delete i matches)
    end
.

Lemma choose_first_enabled_match_shortens_list
    {Σ : Signature}
    (initial_vars : gset variable)
    (matches : list Match)
    (i : nat)
    (m : Match)
    (resulting_matches : list Match)
: 
    choose_first_enabled_match initial_vars matches = Some (i, m, resulting_matches) ->
    length matches = S (length resulting_matches)
.
Proof.
    intros H.
    unfold choose_first_enabled_match in H.
    rewrite bind_Some in H.
    destruct H as [[i' m'] [H1 H2]].
    inversion H2; subst; clear H2.
    destruct matches.
    {
        cbn in H1. inversion H1.
    }
    cbn.
    rewrite length_delete; cbn.
    { 
        rewrite Nat.sub_0_r.
        reflexivity.
    }
    {
        rewrite list_find_Some in H1.
        destruct H1 as [H1 H2].
        rewrite H1.
        unfold is_Some.
        exists m.
        reflexivity.
    }
Qed.


Equations? order_enabled_first
    {Σ : Signature}
    (initial_vars : gset variable)
    (matches : list Match)
    : (list Match * list Match)%type
    by wf (length matches) lt
:=
    order_enabled_first vs ms
        with (inspect (choose_first_enabled_match vs ms)) => {
            | exist _ None _ := ([], ms)
            | exist _ (Some (i, m', rest)) H :=
                match (order_enabled_first
                    (vs ∪ vars_of_OpenTerm (m_term m'))
                    rest) with
                | (good, bad) => (m'::good, bad)
                end
        };
.
Proof.
    apply choose_first_enabled_match_shortens_list in H.
    cbn in H.
    inversion H; subst; clear H.
    ltac1:(lia).
Qed.

Opaque order_enabled_first.

Lemma choose_first_enabled_match_perm
    {Σ : Signature}
    (initial_vars : gset variable)
    (matches : list Match)
    (i : nat)
    (m : Match)
    (matches' : list Match)
    : choose_first_enabled_match initial_vars matches = Some (i,m,matches') ->
      (m::matches') ≡ₚ matches /\ matches' = delete i matches
.
Proof.
    unfold choose_first_enabled_match.
    rewrite bind_Some.
    intros [[i' m'] [H1i'm' H2i'm']].
    inversion H2i'm'; subst; clear H2i'm'.
    rewrite list_find_Some in H1i'm'.
    destruct H1i'm' as [H1 [H2 H3]].
    split.
    {
        symmetry.
        apply delete_Permutation.
        exact H1.
    }
    {
        reflexivity.
    }
Qed.


Lemma order_enabled_first_perm
    {Σ : Signature}
    (initial_vars : gset variable)
    (matches : list Match)
    : let gb := order_enabled_first initial_vars matches in
      (gb.1 ++ gb.2) ≡ₚ matches
.
Proof.
    ltac1:(funelim (order_enabled_first initial_vars matches)).
    {
        assert (H' := H).
        apply choose_first_enabled_match_perm in H'.
        rewrite <- Heqcall. clear Heqcall.
        repeat (ltac1:(case_match)).
        simpl in *.
        eapply transitivity>[|apply H'].
        constructor.
        exact H0.
    }
    {
        rewrite <- Heqcall.
        simpl.
        apply reflexivity.
    }
Qed.

(*
Lemma A_satisfies_B_WithASideCondition_comp_iff
    {Σ : Signature}
    {A B : Type}
    `{Satisfies (Valuation*A) B}
    :
    @satisfies (Valuation*A) (WithASideCondition B) _
    =
    A_satisfies_B_WithASideCondition_comp A B
.
Proof.
    apply functional_extensionality.
    intros ρa.
    apply functional_extensionality.
    intros wscb.
    apply propositional_extensionality.
    induction wscb; cbn.
    {
        split; intros H'.
        {
            inversion H'; subst; clear H'.
            assumption.
        }
        {
            apply asbwsc_base.
            assumption.
        }
    }
    {
        split; intros H'.
        {
            inversion H'; subst; clear H'.
            ltac1:(naive_solver).
        }
        {
            constructor; ltac1:(naive_solver).
        }
    }
Qed.

*)

Lemma getSCS_getBase_correct
    `{CΣ : ComputableSignature}
    {A B : Type}
    `{Matches (Valuation*A) B}
    (wscb : WithASideCondition B)
    (a : A)
    (ρ : Valuation)
    : 
    (satisfies (ρ,a) (getBase wscb) /\
    satisfies ρ (getSCS wscb))
    <->
    satisfies (ρ,a) wscb
.
Proof.
    revert a.
    induction wscb; intros a; cbn.
    {
        split.
        {
            intros [H1 H2].
            constructor.
            assumption.
        }
        {
            intros H'.
            inversion H'; subst; clear H'.
            split.
            { assumption. }
            { apply Forall_nil. }
        }
    }
    {
        specialize (IHwscb a).
        unfold satisfies at 2.
        simpl.
        unfold valuation_satisfies_scs.
        ltac1:(rewrite Forall_cons_iff).
        
        rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ ρ (getSCS wscb))) in IHwscb.
        split; intros HH.
        {
            unfold satisfies. simpl. constructor.
            apply IHwscb.
            destruct HH as [HH1 [HH2 HH3]].
            split>[assumption|].
            unfold matchesb. simpl.
            rewrite forallb_forall.
            rewrite Forall_forall in HH3.
            intros x HHH. specialize (HH3 x HHH).
            eapply introT.
            { apply matchesb_satisfies. }
            { assumption. }
            simpl. apply HH.
        }
        {
            inversion HH; subst; clear HH.
            simpl in *.
            unfold satisfies at 2 in IHwscb. simpl in IHwscb.
            rewrite <- IHwscb in H3. clear IHwscb.
            destruct H3 as [H31 H32].
            split>[assumption|].
            split>[assumption|].
            rewrite Forall_forall.
            intros x HHH.
            unfold matchesb in H32. simpl in H32.
            rewrite forallb_forall in H32.
            specialize (H32 x HHH).
            eapply elimT.
            { apply matchesb_satisfies. }
            { assumption. }
        }
    }
Qed.


Lemma separate_scs_correct
    {Σ : Signature}
    {A B : Type}
    `{Satisfies (Valuation*A) B}
    (wscb : WithASideCondition B)
    (a : A)
    (ρ : Valuation)
    :
    match separate_scs wscb with
    | (b, scs) => satisfies (ρ,a) b /\ valuation_satisfies_scs ρ scs
    end
    <->
    A_satisfies_B_WithASideCondition Valuation A B (ρ, a) wscb
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
            intros H'.
            inversion H'; subst.
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
            inversion H1; subst.
            assumption.
        }
        {
            inversion H1; subst.
            assumption.
        }
    }
Qed.
(*
Lemma aoxy_satisfies_aoxz_comp_iff
    {Σ : Signature}
    {Y Z : Type}
    `{Satisfies (Valuation * Y) Z}
    `{Satisfies (Valuation * AppliedOperator' symbol Y) Z}
    (ρ : Valuation)
    (g : (AppliedOperator' symbol Y))
    :
    aoxy_satisfies_aoxz_comp ρ g
    =
    @satisfies _ (AppliedOperator' symbol Z) _ (ρ,g)
.
Proof.
    apply functional_extensionality.
    intros φ.
    apply propositional_extensionality.
    revert g.
    induction φ; intros gg; destruct gg; cbn; split; intros HH;
        inversion HH; subst; try constructor;
        try ltac1:(naive_solver).
    {
        destruct HH as [HH1 HH2].
        eapply elimT.
        { apply matchesb_satisfies. }
        unfold satisfies.
        apply HH.
        unfold satisfies in H2.
        simpl in H2.
        inversion H2.
    }
    {
        apply HH.
    }
Qed.


Lemma aoxyo_satisfies_aoxzo_comp_iff
    {X Y Z : Type}
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
*)

#[export]
Program Instance Matchse__builtin__Expression
    `{CΣ : ComputableSignature}
    :
    Matches (Valuation * builtin_value) Expression
:= {|
    matchesb := fun ρb e =>
        let ρ := ρb.1 in
        let b := ρb.2 in
        bool_decide (Expression_evaluate ρ e = Some (aoo_operand _ _ b))
      ;
|}.
Next Obligation.
    unfold satisfies. simpl.
    apply bool_decide_reflect.
Qed.
Fail Next Obligation.

#[export]
Program Instance Matches_aopb_Expr
    `{CΣ : ComputableSignature}
    :
    Matches
        (Valuation * AppliedOperator' symbol builtin_value)
    Expression
:= {|
    matchesb := fun ρx e =>
        let ρ := ρx.1 in
        let x := ρx.2 in
        bool_decide (Expression_evaluate ρ e = Some (aoo_app _ _ x))
     ;
    matchesb_satisfies := _ ;
|}.
Next Obligation.
    unfold satisfies. simpl.
    apply bool_decide_reflect.
Qed.
Fail Next Obligation.

#[export]
Program Instance Matches_bv_pureterm
    {Σ : Signature}:
    Matches
        (Valuation * builtin_value)
        (AppliedOperator' symbol Expression)
:= {|
    matchesb := fun _ _ => false;
|}.
Next Obligation.
    unfold satisfies. simpl.
    apply ReflectF. intros HContra. inversion HContra.
Qed.
Fail Next Obligation.

#[export]
Instance Matches__GroundTerm__RhsPattern
    `{CΣ : ComputableSignature}
    :
    Matches (Valuation * GroundTerm) RhsPattern
.
Proof.
    apply Matches__aoxyo_satisfies_aoxzo_bool.
Defined.

Lemma correct_rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern
    `{CΣ : ComputableSignature} lro
    (ρ : Valuation)
    (g : GroundTerm):
    satisfies
        (ρ,g)
        (rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern lro)
    <->
    satisfies ((ρ,LR_Right),g) lro
.
Proof.
    rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ,g) (rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern lro))).
    unfold rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern.
    destruct lro; simpl.
    {
        unfold satisfies; simpl.
        unfold satisfies; simpl.
        unfold GroundTerm_satisfies_LocalRewrite; simpl.
        symmetry. apply reflect_iff.
        apply matchesb_satisfies.
    }
    {
        unfold satisfies; simpl.
        rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ,g) (φ))).
        
        cbn.
        destruct φ,g; cbn.
        {
            revert ao.
            induction ao0; cbn; intros ao.
            {
                unfold matchesb; simpl.
                unfold aoxyo_satisfies_aoxzo_bool; simpl.
                unfold ApppliedOperatorOr'_matches_AppliedOperatorOr'; simpl.
                unfold matchesb; simpl.
                destruct ao; reflexivity.
            }
            {
                simpl.

                destruct ao; simpl.
                { reflexivity. }
                { 
                    specialize (IHao0 ao).
                    cbn in *.
                    unfold fmap in *.
                    unfold matchesb in *; simpl in *.
                    unfold aoxyo_satisfies_aoxzo_bool in *; simpl in *.
                    unfold matchesb in *; simpl in *.
                    rewrite -> andb_true_iff.
                    rewrite -> IHao0.
                    unfold ApppliedOperatorOr'_matches_AppliedOperatorOr'; simpl.
                    unfold matchesb at 3; simpl.
                    rewrite -> andb_true_iff.
                    unfold matchesb; simpl.
                    destruct b0; simpl.
                    {
                        unfold bool_decide; simpl.
                        ltac1:((repeat case_match); simplify_eq/=).
                        { reflexivity. }
                        {
                            clear H.
                            inversion e; subst.
                            ltac1:(contradiction).
                        }
                        {
                            reflexivity.
                        }
                    }
                    {
                        unfold bool_decide; simpl.
                        ltac1:((repeat case_match); simplify_eq/=);
                            clear H; ltac1:(simplify_eq/=); try reflexivity.
                        {
                            ltac1:(exfalso).
                            ltac1:(rewrite e in H0).
                            inversion H0.
                        }
                        {
                            inversion H0; subst; clear H0.
                            ltac1:(rewrite e in H1).
                            inversion H1; subst; clear H1.
                            ltac1:(contradiction).
                        }
                        {
                            ltac1:(rewrite e in H0).
                            inversion H0; subst; clear H0.
                        }
                    }
                }
                {
                    assert(IH1 := IHao0 ao1).
                    assert(IH2 := IHao0 ao2).
                    unfold matchesb in *; simpl in *.
                    unfold aoxyo_satisfies_aoxzo_bool in *; simpl in *.
                    unfold matchesb in *; simpl in *.
                    unfold ApppliedOperatorOr'_matches_AppliedOperatorOr' in *; simpl in *.
                    unfold matchesb in *; simpl in *.
                    rewrite -> andb_false_r.
                    rewrite -> andb_true_iff.
                    unfold matchesb; simpl.
                    split.
                    { intros HH. inversion HH. }
                    { intros [HH1 HH2]. inversion HH2. }
                }
            }
            {
                unfold matchesb; simpl.
                unfold aoxyo_satisfies_aoxzo_bool; simpl.
                unfold matchesb; simpl.
                unfold ApppliedOperatorOr'_matches_AppliedOperatorOr'; simpl.
                unfold matchesb; simpl.
                
                destruct ao; simpl in *.
                {
                    ltac1:(tauto).
                }
                {
                    do 2 (rewrite -> andb_true_iff).
                    specialize (IHao0_1 ao).
                    specialize (IHao0_2 ao).
                    unfold matchesb in *|-; simpl in *|-.
                    unfold aoxyo_satisfies_aoxzo_bool in *|-; simpl in *|-.
                    rewrite IHao0_1.
                    destruct b; simpl in *; unfold matchesb; simpl.
                    { ltac1:(tauto). }
                    { ltac1:(tauto). }
                }
                {
                    do 2 (rewrite -> andb_true_iff).
                    specialize (IHao0_1 ao1).
                    specialize (IHao0_2 ao2).
                    unfold matchesb in *|-; simpl in *|-.
                    unfold aoxyo_satisfies_aoxzo_bool in *|-; simpl in *|-.
                    rewrite IHao0_1.
                    rewrite IHao0_2.
                    reflexivity.
                }
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
            unfold matchesb; simpl.
            unfold aoxyo_satisfies_aoxzo_bool; simpl.
            unfold ApppliedOperatorOr'_matches_AppliedOperatorOr'; simpl.
            destruct operand; simpl in *; unfold matchesb; simpl;
                unfold bool_decide; simpl; ltac1:(repeat case_match);
                try (ltac1:(tauto)); ltac1:(try solve[clear H H0; simplify_eq/=]).
            {
                subst.
                ltac1:(rewrite e in H0).
                inversion H0.
            }
            {
                subst.
                ltac1:(rewrite e in H0).
                inversion H0; subst; clear H0.
                ltac1:(contradiction).
            }
            {
                ltac1:(rewrite e in H0).
                inversion H0.
            }
            {
                subst.
                clear H H2.
                ltac1:(rewrite H0 in n).
                ltac1:(contradiction n).
                reflexivity.
            }
        }
    }
    {
        unfold matchesb; simpl.
        unfold aoxyo_satisfies_aoxzo_bool; simpl.
        unfold satisfies; simpl.
        unfold satisfies; simpl.
        unfold GroundTerm_satisfies_BuiltinOrVar; simpl.
        unfold matchesb; simpl.
        unfold bool_decide; simpl.
        ltac1:(repeat case_match); subst; try (ltac1:(naive_solver)).
        {
            clear H0. inversion e. ltac1:(naive_solver).
        }
    }
Qed.

Lemma correct_AppliedOperator'_symbol_A_to_OpenTerm
    `{CΣ : ComputableSignature}
    {A B : Type}
    (A_to_OpenTermB : A -> AppliedOperatorOr' symbol B)
    (A_to_SC : A -> list SideCondition )
    `{Matches (Valuation*builtin_value) A}
    `{Matches (Valuation * AppliedOperator' symbol builtin_value) A}
    `{Matches (Valuation*GroundTerm) A}
    `{Matches (Valuation*(AppliedOperator' symbol builtin_value)) B}
    `{Matches (Valuation*builtin_value) B}
    `{Matches (Valuation*builtin_value) (AppliedOperator' symbol B)}
    `{Matches (Valuation*builtin_value) (AppliedOperator' symbol A)}
    (*
    `{Matches (Valuation * GroundTerm) (AppliedOperatorOr' symbol A)}
    `{Matches (Valuation * GroundTerm) (AppliedOperatorOr' symbol B)}
    *)
    (ρ : Valuation)
    (x : AppliedOperatorOr' symbol A)
    (g : GroundTerm)
    :
    (
        ∀ (γ : AppliedOperatorOr' symbol builtin_value)
          (a : A),
        a ∈ AppliedOperatorOr'_operands _ _ x ->
            (
                satisfies (ρ,γ) (A_to_OpenTermB a)
            /\
                satisfies ρ (A_to_SC a)
            )
            <->
            satisfies (ρ,γ) a
    )
    ->
    ((
        satisfies (ρ,g)
            (AppliedOperatorOr'_symbol_A_to_OpenTermB A_to_OpenTermB x)
        /\ (satisfies
             ρ
             (AppliedOperatorOr'_symbol_A_to_SCS A_to_SC x)
            )

    )
    <->
    satisfies (ρ,g) x
    )
.
Proof.
    intros correct_underlying.
    rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ ρ (AppliedOperatorOr'_symbol_A_to_SCS A_to_SC x))).
    rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ,g) (AppliedOperatorOr'_symbol_A_to_OpenTermB A_to_OpenTermB x))).
    rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ,g) (x))).
    (*
    unfold in_val_GroundTerm_satisfies_OpenTerm in *.
    unfold in_val_GroundTerm_satisfies_OpenTerm in *.
    unfold aoosb_satisfies_aoosbf in *.
    *)
    destruct x, g; simpl.
    {
        unfold matchesb; simpl.
        unfold aoxyo_satisfies_aoxzo_bool; simpl.

        revert ao0; induction ao; simpl in *; intros ao0.
        {
            ltac1:(tauto).
        }
        {
            (*unfold matchesb.*)
            unfold matchesb; simpl.
            assert (Hcu := correct_underlying (aoo_app _ _ ao0) b).
            ltac1:(ospecialize (Hcu _)).
            {
                left.
            }
            rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ, aoo_app symbol builtin_value ao0) (A_to_OpenTermB b))) in Hcu.
            unfold matchesb at 1 in Hcu; simpl in Hcu.


            destruct (A_to_OpenTermB b) eqn:Hb, (ao0) eqn:Hao0.
            {
                unfold ApppliedOperator'_matches_AppliedOperator'; simpl.
                rewrite <- andb_true_iff.
                simpl.
                ltac1:(tauto).
            }
            {
                
                ltac1:(ospecialize (IHao _)).
                {
                    intros γ a0 HH.
                    specialize (correct_underlying γ a0).
                    ltac1:(ospecialize (correct_underlying _)).
                    {
                        right. exact HH.
                    }
                    exact correct_underlying.
                }

                unfold ApppliedOperator'_matches_AppliedOperator' at 1; simpl.
                unfold ApppliedOperator'_matches_AppliedOperator' in Hcu; simpl in Hcu.
                unfold aoxyo_satisfies_aoxzo_bool in Hcu; simpl in Hcu.
                unfold matchesb in Hcu; simpl in Hcu.
                rewrite <- Hao0 in Hcu.
                specialize (IHao a).
                subst ao0.
                (* rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ, aoo_app symbol builtin_value ao0) (A_to_OpenTermB b))) in Hcu. *)

                destruct ao1; simpl.
                {
                    subst.
                    
                    unfold matchesb at 3 in IHao; simpl in IHao.
                    rewrite -> andb_true_iff.
                    
                    destruct a; simpl in *.
                    {
                        destruct ao; simpl in *.
                        {
                            clear IHao.
                        }
                        {

                        }
                        rewrite <- IHao.
                        rewrite <- (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ,b0) (b))).
                        ltac1:(rewrite <- (correct_underlying a b)).    
                    }
                    {

                    }

                    rewrite <- IHao.
                    rewrite <- (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ,b0) (b))).
                    ltac1:(rewrite <- (correct_underlying a b)).
                }
                {

                }
                unfold ApppliedOperator'_matches_AppliedOperator'; simpl.
                rewrite -> andb_true_iff.

            }
        }
        (*
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
                    { clear; ltac1:(set_solver). }
                }
            }
            {
                rewrite <- IHao.
                ltac1:(rewrite Forall_app).
                ltac1:(rewrite -correct_underlying).
                { ltac1:(clear; set_solver). }
                {
                    ltac1:(rewrite -aoxyo_satisfies_aoxzo_comp_iff).
                    cbn.
                    rewrite H.
                    unfold valuation_satisfies_scs.
                    clear.
                    ltac1:(naive_solver).
                }
                {
                    intros.
                    apply correct_underlying.
                    { clear -H0; ltac1:(set_solver). }
                }
            }
            {
                ltac1:(rewrite -IHao).
                {
                    intros.
                    apply correct_underlying.
                    clear -H0; ltac1:(set_solver).
                }
                ltac1:(rewrite -correct_underlying).
                {
                    clear; ltac1:(set_solver).
                }
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
                {
                    intros.
                    apply correct_underlying.
                    clear -H0; ltac1:(set_solver).
                }
                ltac1:(rewrite -correct_underlying).
                {
                    clear; ltac1:(set_solver).
                }
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
                ltac1:(rewrite -IHao1).
                {
                    intros.
                    apply correct_underlying.
                    clear -H; ltac1:(set_solver).
                }
                ltac1:(rewrite -IHao2).
                {
                    intros.
                    apply correct_underlying.
                    clear -H; ltac1:(set_solver).
                }
                rewrite Forall_app.
                clear.
                ltac1:(naive_solver).
            }
        }
        *)
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
        {
            clear; ltac1:(set_solver).
        }
        repeat (rewrite <- aoxyo_satisfies_aoxzo_comp_iff).
        reflexivity.
    }
    {
        specialize (correct_underlying (aoo_operand _ _ operand0) operand).
        repeat (rewrite <- aoxyo_satisfies_aoxzo_comp_iff).
        cbn.
        rewrite <- aoxyo_satisfies_aoxzo_comp_iff in correct_underlying.
        cbn in correct_underlying.
        apply correct_underlying.
        clear; ltac1:(set_solver).
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

Lemma builtin_value_satisfies_OpenTermWSC_iff
    {Σ : Signature} ρ x:
    in_val_GroundTerm_satisfies_OpenTermWSC ρ (aoo_operand symbol builtin_value x)
    = builtin_value_satisfies_OpenTermWSC ρ x
.
Proof.
    apply functional_extensionality.
    intros t.
    apply propositional_extensionality.
    unfold OpenTermWSC in *.
    unfold in_val_GroundTerm_satisfies_OpenTermWSC.
    rewrite A_satisfies_B_WithASideCondition_comp_iff.
    cbn.
    revert x.
    induction t; intros x; cbn.
    {
        split; intros H; inversion H; subst; clear H.
        {
            constructor.
            simpl. assumption.
        }
        {
            destruct φ; cbn in *.
            { inversion H2. }
            { constructor. assumption. }
        }
    }
    {
        rewrite IHt.
        split; intros H; constructor.
        { 
            inversion H; subst; clear H.
            assumption.
        }
        {
            apply H.
        }
        {
            inversion H; subst; clear H.
            assumption.
        }
        {
            inversion H; subst; clear H.
            assumption.
        }
    }
Qed.

Lemma AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC_iff
    {Σ : Signature} ρ x:
    in_val_GroundTerm_satisfies_OpenTermWSC ρ (aoo_app symbol builtin_value x)
    = AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC ρ x
.
Proof.
    apply functional_extensionality.
    intros t.
    apply propositional_extensionality.
    unfold OpenTermWSC in *.
    unfold in_val_GroundTerm_satisfies_OpenTermWSC.
    rewrite A_satisfies_B_WithASideCondition_comp_iff.
    cbn.
    revert x.
    induction t; intros x; cbn.
    {
        split; intros H; inversion H; subst; clear H.
        {
            constructor. constructor.
            assumption.
        }
        {
            constructor. constructor. assumption.
        }
        {
            destruct φ; cbn in *.
            {
                constructor.
                inversion H2; subst; clear H2.
                assumption.
            }
            {
                constructor.
                inversion H2; subst; clear H2.
                assumption.
            }
        }
    }
    {
        rewrite IHt.
        split; intros H; constructor.
        { 
            inversion H; subst; clear H.
            assumption.
        }
        {
            apply H.
        }
        {
            inversion H; subst; clear H.
            assumption.
        }
        {
            inversion H; subst; clear H.
            assumption.
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
    unfold satisfies. simpl.
    unfold GroundTerm_satisfies_RewritingRule.
    unfold GroundTerm.
    unfold GroundTerm'.
    unfold UncondRewritingRule.
    unfold GroundTerm_satisfies_UncondRewritingRule.
    unfold aoosb_satisfies_aoosbf.

    cbn.
    do 2 (rewrite <- getSCS_getBase_correct).
    do 2 (rewrite builtin_satisfies_LocalRewriteOrOpenTermOrBOV_iff_GroundTerm).

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

    ltac1:(cut (P32 -> (P1 ∧ P2 ∧ P31 ↔ P4 ∧ P6))).
    {
        ltac1:(naive_solver).
    }
    intros HP32.

    unfold lhs_UncondRewritingRule_to_OpenTerm in *.    

    assert (Htmp1: (
        ∀ (γ : AppliedOperatorOr' (@symbol Σ)
        (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ))) (a : @LocalRewriteOrOpenTermOrBOV
        Σ),
        a
        ∈ AppliedOperatorOr'_operands symbol LocalRewriteOrOpenTermOrBOV (getBase r) ->
        @aoxyo_satisfies_aoxzo (@symbol Σ)
        (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)) (@BuiltinOrVar Σ)
        (@builtin_satisfies_BuiltinOrVar Σ ρ)
        (@AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar Σ ρ) γ
        (@lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm Σ a)
        ∧ @valuation_satisfies_scs Σ ρ (@lhs_LocalRewriteOrOpenTermOrBOV_to_SCS Σ a)
        ↔ @GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV Σ ρ LR_Left γ a))
    .
    {
        intros γ a H0a.
        unfold GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV.
        destruct a.
        {
            destruct r0. (*; simpl in *.*)
            simpl in *|-.
            simpl satisfies. simpl.
            unfold GroundTerm_satisfies_left_LocalRewrite.
            simpl.
            unfold GroundTerm_satisfies_LhsPattern.
            assert (HMyLemma1 := @getSCS_getBase_correct Σ).
            ltac1:(epose proof (HMyLemma2 := @correct_AppliedOperator'_symbol_A_to_OpenTerm Σ ?[MyA] (@BuiltinOrVar Σ))).
            specialize (HMyLemma2 getBase).
            specialize (HMyLemma2 getSCS).
            specialize (HMyLemma2 (@in_val_GroundTerm_satisfies_OpenTermWSC Σ ρ)).
            specialize (HMyLemma2 (@AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar Σ ρ)).
            specialize (HMyLemma2 (@builtin_satisfies_BuiltinOrVar Σ ρ)).
            specialize (HMyLemma2 ρ).
            ltac1:(specialize (HMyLemma2 lr_from)).
            ltac1:(specialize (HMyLemma2 γ)).
            specialize(HMyLemma1 GroundTerm OpenTerm (in_val_GroundTerm_satisfies_OpenTerm ρ)).
            ltac1:(specialize (HMyLemma2 (fun x' y' UnusedHyp => HMyLemma1 y' x' ρ))).
            unfold compose in HMyLemma2. cbn in HMyLemma2.
            rewrite HMyLemma2.
            clear.
            unfold OpenTermWSC,OpenTerm.
            cbn.
            (*
            unfold builtin_value_satisfies_OpenTermWSC.
            unfold in_val_GroundTerm_satisfies_OpenTermWSC.*)
            simpl.
            assert (M2 := AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC_iff ρ).
            assert (M3 := builtin_value_satisfies_OpenTermWSC_iff).
            ltac1:(under [fun (e : AppliedOperator' _ _) => _]functional_extensionality => e).
            {
                ltac1:(rewrite -> M2 at 1).
                ltac1:(over).
            }
            ltac1:(under [fun e => _]functional_extensionality => e).
            {
                ltac1:(rewrite M3).
                ltac1:(over).
            }
            Set Printing Implicit.
            reflexivity.
        }
        {
            {
                unfold in_val_GroundTerm_satisfies_OpenTerm.
                unfold aoosb_satisfies_aoosbf.
                cbn.
                unfold valuation_satisfies_scs.
                split; intros H.
                {
                    apply H.
                }
                {
                    split.
                    { apply H. }
                    apply Forall_nil.
                }
            }
        }
        {
        cbn.
        unfold GroundTerm_satisfies_BuiltinOrVar.
        unfold valuation_satisfies_scs.
        destruct bx,γ; cbn.
        {
            split; intros H.
            {
                destruct H as [H1 H2].
                inversion H1; subst; clear H1.
                inversion H3.
            }
            {
                inversion H.
            }
        }
        {
            split; intros H.
            {
                destruct H as [H1 H2].
                inversion H1; subst; clear H1.
                inversion pf.
                subst. reflexivity.
            }
            {
                subst.
                split; constructor.
                constructor.
            }
        }
        {
            split; intros H.
            destruct H as [H1 H2].
            inversion H1; subst; clear H1.
            inversion H3. assumption.
            split; constructor. simpl.
            assumption.
        }
        {
            split; intros H.
            destruct H as [H1 H2].
            inversion H1; subst; clear H1.
            inversion pf. assumption.
            split; constructor.
            constructor.
            assumption.
        }
        }
    }
    
    assert (L1 := @correct_AppliedOperator'_symbol_A_to_OpenTerm Σ _ BuiltinOrVar
        (lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm) (lhs_LocalRewriteOrOpenTermOrBOV_to_SCS)
        (GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV ρ LR_Left)
        (AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ)
        (builtin_satisfies_BuiltinOrVar ρ)
        ρ (getBase r) from Htmp1).

    clear Htmp1.
    fold P1 in L1.
    unfold valuation_satisfies_scs in L1.
    unfold UncondRewritingRule in L1.
    fold P4 in L1.
    unfold rhs_UncondRewritingRule_to_RhsPattern in P2.
    set (P7 := (@Forall (@SideCondition Σ) (@valuation_satisfies_sc Σ ρ)
        (@AppliedOperatorOr'_symbol_A_to_SCS Σ (@LocalRewriteOrOpenTermOrBOV Σ)
        (@lhs_LocalRewriteOrOpenTermOrBOV_to_SCS Σ)
        (@getBase Σ
        (AppliedOperatorOr' (@symbol Σ) (@LocalRewriteOrOpenTermOrBOV Σ)) r)))).
    unfold lhs_UncondRewritingRule_to_SCS in P31.
    fold P7 in L1.
    ltac1:(cut (P7 -> ((P2 /\ P7) ↔ P6))).
    {
        ltac1:(naive_solver).
    }
    intros HP7.
    clear L1.
    clear P4.
    clear P5.
    clear P1.    
    clear P31.
    ltac1:(unfold P2).
    ltac1:(unfold P6).
    ltac1:(unfold P7).
    
    erewrite <- correct_AppliedOperator'_symbol_A_to_OpenTerm.
    { 
        unfold valuation_satisfies_scs.
        reflexivity.
    }
    intros γ a Ha.
    unfold valuation_satisfies_scs.

    assert (Htmp2: forall b,
        Forall (valuation_satisfies_sc ρ)
            (AppliedOperatorOr'_symbol_A_to_SCS lhs_LocalRewriteOrOpenTermOrBOV_to_SCS
            b) -> 
        a ∈ AppliedOperatorOr'_operands symbol LocalRewriteOrOpenTermOrBOV b ->
        Forall (valuation_satisfies_sc ρ) (lhs_LocalRewriteOrOpenTermOrBOV_to_SCS a)
    ).
    {
        clear. intros b Hb1 Hb2.
        destruct b; cbn in *.
        {
            rewrite Forall_forall.
            intros x Hx.
            rewrite Forall_forall in Hb1.
            specialize (Hb1 x).
            rewrite <- elem_of_list_In in Hx.
            rewrite <- elem_of_list_In in Hb1.
            ltac1:(ospecialize (Hb1 _)).
            {
                clear -Hx Hb2.
                induction ao; cbn in *.
                {
                    rewrite elem_of_nil in Hb2.
                    inversion Hb2.
                }
                {
                    rewrite elem_of_cons in Hb2.
                    rewrite elem_of_app.
                    destruct Hb2 as [Hb2|Hb2].
                    {
                        subst.
                        right.
                        assumption.
                    }
                    {
                        left.
                        auto with nocore.
                    }
                }
                {
                    rewrite elem_of_app in Hb2.
                    rewrite elem_of_app.
                    ltac1:(naive_solver).
                }
            }
            exact Hb1.
        }
        {
            rewrite elem_of_cons in Hb2.
            destruct Hb2 as [Hb2|Hb2].
            {
                subst.
                assumption.
            }
            {
                rewrite elem_of_nil in Hb2. inversion Hb2.
            }
        }
    }
    
    specialize (Htmp2 _ HP7 Ha).

    ltac1:(cut (@aoxyo_satisfies_aoxzo (@symbol Σ)
        (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)) (@Expression Σ)
        (λ (b : @builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)) (e : @Expression Σ),
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
        (aoo_app (@symbol Σ) (@builtin_value (@symbol Σ) (@symbols Σ) (@builtin Σ)) ao))
        γ
        (@rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern Σ a)
        ↔ @GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV Σ ρ LR_Right γ a))
    .
    {
        ltac1:(set_solver).
    }

    rewrite <- correct_rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern.
    unfold GroundTerm_satisfies_RhsPattern.
    reflexivity.
Qed.
