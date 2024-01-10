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
    {Σ : StaticModel}
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

Fixpoint getSCS {Σ : StaticModel} {A : Type} (wsc : WithASideCondition A):
    list SideCondition
:=
match wsc with
| wsc_base _ => []
| wsc_sc wsc' sc => sc::(getSCS wsc')
end.

Fixpoint getBase {Σ : StaticModel} {A : Type} (wsc : WithASideCondition A):
    A
:=
match wsc with
| wsc_base a => a
| wsc_sc wsc' _ => getBase wsc'
end.


Lemma separate_scs_getSCS_getBase
    {Σ : StaticModel} {A : Type}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    {A : Type}
    (A_to_SC : A -> list SideCondition )
    (x : AppliedOperatorOr' symbol A)
    : list SideCondition
:=
match x with
| aoo_app _ _ app => AppliedOperator'_symbol_A_to_SCS A_to_SC app
| aoo_operand _ _ operand => A_to_SC operand
end.


(*
Fixpoint A_satisfies_B_WithASideCondition_comp
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    {CΣ : ComputableStaticModel}
    {Y Z : Type}
    {_S1 : Satisfies Valuation (Y) Z variable}
    {_S2 : Satisfies Valuation (AppliedOperator' symbol Y) Z variable}
    {_S3 : Satisfies Valuation (AppliedOperator' symbol Y) (AppliedOperator' symbol Z) variable}
    {_M1 : Matches Valuation (Y) Z variable}
    {_M2 : Matches Valuation (AppliedOperator' symbol Y) Z variable}
    {_M3 : Matches Valuation (AppliedOperator' symbol Y) (AppliedOperator' symbol Z) variable}
    :
    Valuation -> (AppliedOperatorOr' symbol Y) ->
    AppliedOperatorOr' symbol Z ->
    bool :=
fun ρ g φ =>
match g, φ with
| aoo_app _ _ g0, aoo_app _ _ φ0
    => matchesb ρ g0 φ0

| aoo_operand _ _ g0, aoo_operand _ _ φ0
    => matchesb ρ g0 φ0

| aoo_app _ _ g0, aoo_operand _ _ φ0
    => matchesb ρ g0 φ0

| aoo_operand _ _ _, aoo_app _ _ _
    => false
end.

#[export]
Program Instance Matches__aoxyo_satisfies_aoxzo_bool
    `{CΣ : ComputableStaticModel}
    {Y Z : Type}
    {_S1 : Satisfies Valuation Y Z }
    {_S2 : Satisfies Valuation (AppliedOperator' symbol Y) Z}
    {_S3 : Satisfies Valuation (AppliedOperator' symbol Y) (AppliedOperator' symbol Z)}
    {_M1 : Matches Valuation Y Z }
    {_M2 : Matches Valuation (AppliedOperator' symbol Y) Z}
    {_M3 : Matches Valuation (AppliedOperator' symbol Y) (AppliedOperator' symbol Z)}
    :
    Matches Valuation (((AppliedOperatorOr' symbol Y))) (AppliedOperatorOr' symbol Z)
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
    {Σ : StaticModel}
    (l : LhsPattern)
    : (OpenTerm * (list SideCondition))
:= 
(
    AppliedOperatorOr'_symbol_A_to_OpenTermB getBase l,
    AppliedOperatorOr'_symbol_A_to_SCS getSCS l
).

Definition lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm
    {Σ : StaticModel}
    (lox : LocalRewriteOrOpenTermOrBOV)
    : OpenTerm
:=
match lox with
| lp_rewrite r => AppliedOperatorOr'_symbol_A_to_OpenTermB getBase (lr_from r)
| lp_basicpat φ => φ
| lp_bov bov => aoo_operand _ _ bov
end.

Definition lhs_LocalRewriteOrOpenTermOrBOV_to_SCS
    {Σ : StaticModel}
    (lox : LocalRewriteOrOpenTermOrBOV)
    : list SideCondition
:=
match lox with
| lp_rewrite r => AppliedOperatorOr'_symbol_A_to_SCS getSCS (lr_from r)
| lp_basicpat φ => [] (* we would use `getSCS φ` if it had a side condition *)
| lp_bov bov => []
end.

Definition lhs_UncondRewritingRule_to_OpenTerm
    {Σ : StaticModel}
    (ur : UncondRewritingRule)
    : OpenTerm
:=
    AppliedOperatorOr'_symbol_A_to_OpenTermB lhs_LocalRewriteOrOpenTermOrBOV_to_OpenTerm ur
.

Definition lhs_UncondRewritingRule_to_SCS
    {Σ : StaticModel}
    (ur : UncondRewritingRule)
    : list SideCondition
:=
    AppliedOperatorOr'_symbol_A_to_SCS lhs_LocalRewriteOrOpenTermOrBOV_to_SCS ur
.

Definition lhs_RewritingRule_to_OpenTerm
    {Σ : StaticModel}
    (r : RewritingRule)
    : OpenTerm
:=
    lhs_UncondRewritingRule_to_OpenTerm (getBase r)
.

Definition lhs_RewritingRule_to_SCS
    {Σ : StaticModel}
    (r : RewritingRule)
    : list SideCondition
:=
    lhs_UncondRewritingRule_to_SCS (getBase r)
    ++ getSCS r
.

Definition BOV_to_Expression
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : Expression
:=
match bov with
| bov_builtin b => ft_element (aoo_operand _ _ b)
| bov_variable x => ft_variable x
end.



Definition rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    (ur : UncondRewritingRule)
    : RhsPattern
:=
    AppliedOperatorOr'_symbol_A_to_OpenTermB rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern ur
.

Definition rhs_RewritingRule_to_RhsPattern
    {Σ : StaticModel}
    (r : RewritingRule)
    : RhsPattern
:=
    rhs_UncondRewritingRule_to_RhsPattern (getBase r)
.

Definition RewritingRule_to_FlattenedRewritingRule
    {Σ : StaticModel}
    (r : RewritingRule)
    : FlattenedRewritingRule
:=
{|
    fr_from := lhs_RewritingRule_to_OpenTerm r ;
    fr_to := rhs_RewritingRule_to_RhsPattern r ;
    fr_scs := lhs_RewritingRule_to_SCS r ;
|}.

Definition enables_match
    {Σ : StaticModel}
    (vars : gset variable)
    (m : Match)
: Prop :=
    (m_variable m) ∈ vars
.

#[export]
Instance enables_match_dec
    {Σ : StaticModel}
    (vars : gset variable)
    (m : Match)
    : Decision (enables_match vars m)
.
Proof.
    unfold enables_match.
    ltac1:(solve_decision).
Defined.

Definition choose_first_enabled_match
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    {CΣ : ComputableStaticModel}
    {A B : Type}
    {_S1 : Satisfies Valuation A B}
    {_M1 : Matches Valuation A B}
    (wscb : WithASideCondition B)
    (a : A)
    (ρ : Valuation)
    : 
    (satisfies ρ a (getBase wscb) /\
    satisfies ρ () (getSCS wscb))
    <->
    satisfies ρ a wscb
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
        ltac1:(rewrite Forall_cons_iff).
        
        rewrite (reflect_iff _ _ (matchesb_satisfies ρ () (getSCS wscb))) in IHwscb.
        split; intros HH.
        {
            destruct HH as [HH1 [HH2 HH3]].
            unfold satisfies. simpl. constructor.
            {
                apply IHwscb.
                split>[assumption|].
                unfold matchesb. simpl.
                rewrite forallb_forall.
                rewrite Forall_forall in HH3.
                intros x Hx.
                specialize (HH3 x Hx).
                apply satisfies_implies_matchesb.
                assumption.
            }
            {
                assumption.
            }
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
            {
                assumption.
            }
        }
    }
Qed.


Lemma separate_scs_correct
    {Σ : StaticModel}
    {A B : Type}
    {_S1 : Satisfies Valuation (A) B}
    (wscb : WithASideCondition B)
    (a : A)
    (ρ : Valuation)
    :
    match separate_scs wscb with
    | (b, scs) => satisfies ρ a b /\ satisfies ρ () scs
    end
    <->
    satisfies ρ a wscb
.
Proof.
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
        unfold satisfies at 2. simpl.
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
(*
Lemma aoxy_satisfies_aoxz_comp_iff
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    `{CΣ : ComputableStaticModel}
    :
    Matches Valuation builtin_value Expression
:= {|
    matchesb := fun ρ b e =>
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
    `{CΣ : ComputableStaticModel}
    :
    Matches
        Valuation
        (AppliedOperator' symbol builtin_value)
    Expression
:= {|
    matchesb := fun ρ x e =>
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
    {Σ : StaticModel}:
    Matches
        Valuation
        builtin_value
        (AppliedOperator' symbol Expression)
:= {|
    matchesb := fun _ _ _ => false;
|}.
Next Obligation.
    unfold satisfies. simpl.
    apply ReflectF. intros HContra. inversion HContra.
Qed.
Fail Next Obligation.

#[export]
Instance Matches__GroundTerm__RhsPattern
    `{CΣ : ComputableStaticModel}
    :
    Matches Valuation (GroundTerm) RhsPattern
.
Proof.
    apply Matches__aoxyo_satisfies_aoxzo_bool.
Defined.

Lemma correct_rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern
    `{CΣ : ComputableStaticModel} lro
    (ρ : Valuation)
    (g : GroundTerm):
    satisfies
        ρ g
        (rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern lro)
    <->
    satisfies (ρ,LR_Right) g lro
.
Proof.
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ g (rhs_LocalRewriteOrOpenTermOrBOV_to_RhsPattern lro))).
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
        rewrite (reflect_iff _ _ (matchesb_satisfies ρ g (φ))).
        
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
                    unfold matchesb at 2; simpl.
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
(*
Lemma correct_AppliedOperator'_symbol_A_to_OpenTerm
    `{CΣ : ComputableStaticModel}
    {A B : Type}
    (A_to_OpenTermB : A -> AppliedOperatorOr' symbol B)
    (A_to_SC : A -> list SideCondition )
    `{Matches (Valuation*builtin_value) A}
    `{Matches (Valuation * AppliedOperator' symbol builtin_value) A}
    `{Matches (Valuation*GroundTerm) A}
    `{Matches (Valuation*(AppliedOperator' symbol builtin_value)) B}
    `{Matches (Valuation*builtin_value) B}
    (*`{Matches (Valuation*builtin_value) (AppliedOperator' symbol B)}
    `{Matches (Valuation*builtin_value) (AppliedOperator' symbol A)} *)
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
                rewrite -> andb_true_iff.
                rewrite forallb_app.
                rewrite -> andb_true_iff.
                
                cbn.
                rewrite -> andb_true_iff.
                ltac1:(rewrite [matchesb (ρ, b0) ao1]/matchesb). simpl.


                ltac1:(specialize (correct_underlying (aoo_app _ _ a) b)).
                rewrite Hb in correct_underlying.
                ltac1:(ospecialize (correct_underlying _)).
                { left. }

                ltac1:(rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ, aoo_app symbol builtin_value a) (aoo_app symbol B ao1))) in correct_underlying).
                unfold matchesb in correct_underlying; simpl in correct_underlying.
                unfold aoxyo_satisfies_aoxzo_bool in correct_underlying; simpl in correct_underlying.

                ltac1:(rewrite [matchesb (ρ, b0) b]/matchesb). simpl.
                specialize (IHao a).
                split; intros HH.
                {
                    destruct HH as [[HH1 HH2] [HH3 HH4]].
                    inversion HH2.
                    (*
                    destruct IHao as [IH1 IH2].
                    subst ao0.
                    ltac1:(ospecialize (IH1 _)).
                    {
                        split.
                        { apply HH1. }
                        {
                            apply HH3.
                        }
                    }
                    split.
                    { apply IH1. }
                    {
                        unfold matchesb in HH2; simpl in HH2.
                        inversion HH2.
                    }*)
                }
                {
                    ltac1:(exfalso).
                    destruct IHao as [IH1 IH2].
                    subst ao0.
                    destruct HH as [HH1 HH2].
                    
                    ltac1:(ospecialize (IH1 _)).
                    {

                    }
                }
                (*
                assert (Hcu := correct_underlying (aoo_app _ _ ao0) b).
                ltac1:(ospecialize (Hcu _)).
                {
                    left.
                }
                rewrite (reflect_iff _ _ (@matchesb_satisfies _ _ _ _ (ρ, aoo_app symbol builtin_value ao0) (A_to_OpenTermB b))) in Hcu.
                unfold matchesb at 1 in Hcu; simpl in Hcu.


                specialize (IHao a).
                *)

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
    {Σ : StaticModel}
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
    {Σ : StaticModel} ρ x:
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
    {Σ : StaticModel} ρ x:
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
    {Σ : StaticModel}
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
*)


Lemma order_enabled_first_nil
    {Σ : StaticModel}
    {CΣ : ComputableStaticModel}
    initial_vars:
    order_enabled_first initial_vars [] = ([],[])
.
Proof.
    ltac1:(simp order_enabled_first).
    unfold order_enabled_first_unfold_clause_1.
    simpl.
    reflexivity.
Qed.


Definition vars_of_lm
    {Σ : StaticModel}
    (lm : list Match)
    : gset variable
:=
    union_list (vars_of_OpenTerm <$> (m_term <$> lm))
.

Inductive nicely_ordered {Σ : StaticModel}
    : gset variable -> list Match -> Prop
:=
| no_empty: forall initial, nicely_ordered initial []
| no_cons: forall initial x xs,
    (m_variable x) ∈ initial ->
    nicely_ordered (initial ∪ (vars_of_OpenTerm (m_term x))) xs ->
    nicely_ordered
        initial
        (x::xs)
.

Lemma nicely_ordered_mono
    {Σ : StaticModel}
    i1 i2 l:
    i1 ⊆ i2 ->
    nicely_ordered i1 l ->
    nicely_ordered i2 l
.
Proof.
    intros H1 H2.
    revert i1 i2 H1 H2.
    induction l; intros i1 i2 H1 H2.
    {
        constructor.
    }
    {
        inversion H2; subst; clear H2.
        constructor.
        { ltac1:(set_solver). }
        eapply IHl>[|apply H5].
        ltac1:(set_solver).
    }
Qed.

Lemma nicely_ordered_cons {Σ : StaticModel} initial x l:
    nicely_ordered initial (x::l)
    <-> (
        (m_variable x) ∈ initial /\
        nicely_ordered (initial ∪ (vars_of_OpenTerm (m_term x))) l
    )
.
Proof.
    split; intros H.
    {
        inversion H; subst; clear H.
        split.
        {
            clear -H3. ltac1:(set_solver).
        }
        {
            eapply nicely_ordered_mono>[|apply H4].
            clear. ltac1:(set_solver).
        }
    }
    {
        destruct H as [H1 H2].
        apply no_cons; assumption.
    }
Qed.


Lemma nicely_ordered_app {Σ : StaticModel} initial l1 l2:
    nicely_ordered initial (l1 ++ l2)
    <->
    (nicely_ordered initial l1 /\
        nicely_ordered (initial ∪ (vars_of_lm l1)) l2)
.
Proof.
    revert l2 initial.
    induction l1; intros l2 initial.
    {
        unfold vars_of_lm.
        do 2 (rewrite fmap_nil).
        rewrite union_list_nil.
        rewrite union_empty_r_L.
        simpl.
        split.
        {
            intros H.
            split.
            { apply no_empty. }
            exact H.
        }
        {
            intros [_ H].
            exact H.
        }
    }
    {
        unfold vars_of_lm.
        do 2 (rewrite fmap_cons).
        simpl.
        do 2 (rewrite nicely_ordered_cons).
        rewrite IHl1.
        clear IHl1 up_dec bp_dec.
        unfold vars_of_lm.
        unfold union_list.
        rewrite foldr_fmap.
        simpl.
        rewrite union_assoc_L.
        ltac1:(naive_solver).
    }
Qed.

Lemma enables_match_mono {Σ : StaticModel} vs1 vs2 m:
    vs1 ⊆ vs2 ->
    enables_match vs1 m ->
    enables_match vs2 m
.
Proof.
    unfold enables_match.
    ltac1:(set_solver).
Qed.

Lemma nicely_ordered_all_enable_match {Σ : StaticModel} vs l m:
    nicely_ordered vs l ->
    m ∈ l ->
    ∃ vs', vs ⊆ vs' /\
        enables_match vs' m
.
Proof.
    intros Hord Hin.
    apply elem_of_list_split in Hin.
    destruct Hin as [l1 [l2 Hl1l2]].
    subst l.
    rewrite nicely_ordered_app in Hord.
    destruct Hord as [_ Hml2].
    rewrite nicely_ordered_cons in Hml2.
    destruct Hml2 as [Hmin Hl2].
    unfold enables_match.
    eexists.
    split>[|apply Hmin].
    ltac1:(clear; set_solver).
Qed.

Lemma nicely_ordered_all_enable_match' {Σ : StaticModel} vs l i m:
    nicely_ordered vs l ->
    l !! i = Some m ->
    enables_match (vs ∪ vars_of_lm (take i l)) m
.
Proof.
    intros Hord Hin.
    assert (Hlt := Hin).
    apply lookup_lt_Some in Hlt.   
    rewrite <- (take_drop (i)) in Hord.
    rewrite <- (take_drop (S i) l) in Hin.
    rewrite nicely_ordered_app in Hord.
    destruct Hord as [_ Hord].
    rewrite lookup_app in Hin.
    rewrite lookup_take in Hin>[|ltac1:(lia)].
    remember (l !! i) as om.
    destruct om.
    {
        inversion Hin; subst; clear Hin.
        symmetry in Heqom.
        apply elem_of_list_split_length in Heqom.
        destruct Heqom as [l1 [l2 [H1 H2]]].
        subst.
        clear Hlt.
        rewrite drop_app_length in Hord.
        rewrite nicely_ordered_cons in Hord.
        destruct Hord as [H1 H2].
        unfold enables_match.
        apply H1.
    }
    {
        ltac1:(exfalso).
        clear -Heqom Hlt.
        symmetry in Heqom.
        apply lookup_ge_None_1 in Heqom.
        ltac1:(lia).
    }
Qed.

Lemma nicely_ordered_exists_enables_match {Σ : StaticModel} vs ms l':
    l' ≡ₚ ms ->
    ms <> [] ->
    nicely_ordered vs l' ->
    (∃ i g vs',
        ms !! i = Some g
        /\ enables_match vs' g
        /\ vs ⊆ vs'
    )
.
Proof.
    intros Hperm Hnotnil Hno.
    destruct ms.
    {
        ltac1:(contradiction Hnotnil).
        reflexivity.
    }
    clear Hnotnil.
    apply Permutation_vs_cons_inv in Hperm.
    destruct Hperm as [l1 [l2 Hl1l2]].
    subst l'.
    apply nicely_ordered_all_enable_match with (m := m) in Hno.
    {
        destruct Hno as [vs' [Hsub Hen]].
        exists 0.
        exists m.
        exists vs'.
        cbn.
        split>[reflexivity|].
        split>[exact Hen|].
        apply Hsub.
    }
    {
        clear. ltac1:(set_solver).
    }
Qed.

Lemma can_be_ordered_implies_choose_Some
    {Σ : StaticModel}
    vs ms ms':
    ms <> [] ->
    ms' ≡ₚ ms ->
    nicely_ordered vs ms' ->
    ∃ mlm,
    choose_first_enabled_match vs ms = Some mlm
.
Proof.
    intros Hnotnil Hperm Hordered.
    assert (Hnotnil': ms' <> []).
    {
        clear -Hnotnil Hperm.
        intros HContra.
        apply Hnotnil.
        subst ms'.
        apply Permutation_nil.
        exact Hperm.
    }
    destruct ms'.
    {
        ltac1:(contradiction Hnotnil').
        reflexivity.
    }
    clear Hnotnil' Hnotnil.
    symmetry in Hperm.
    apply Permutation_vs_cons_inv in Hperm.
    destruct Hperm as [l' [l'' Hms]].
    subst ms.
    inversion Hordered; subst; clear Hordered.
    remember (choose_first_enabled_match vs l') as o.
    destruct o as [[[idx m'] lm' ]|].
    {
        exists (idx,m', lm'++m::l'').
        unfold choose_first_enabled_match in Heqo.
        unfold choose_first_enabled_match.
        symmetry in Heqo.
        rewrite bind_Some in Heqo.
        destruct Heqo as [[idx' Midx] [HH1 HH2]].
        inversion HH2; subst; clear HH2.
        rewrite bind_Some.
        exists (idx, m').
        split.
        {
            apply list_find_app_l.
            exact HH1.
        }
        apply f_equal.
        rewrite list_find_Some in HH1.
        destruct HH1 as [Hl'idx HH1].
        rewrite delete_take_drop.
        rewrite delete_take_drop.
        rewrite <- app_assoc.
        rewrite firstn_app.
        apply lookup_lt_Some in Hl'idx as HH2.
        destruct l'.
        { simpl in HH2. ltac1:(lia). }
        simpl.
        ltac1:(f_equal).
        rewrite <- app_assoc.
        apply f_equal.
        simpl in HH2.
        assert (Hexp0: idx - (S (length l')) = 0).
        {
            ltac1:(lia).
        }
        rewrite Hexp0.
        clear Hexp0.
        simpl.
        rewrite drop_app_le.
        {
            reflexivity.
        }
        {
            ltac1:(lia).
        }
    }
    exists (length l', m, l' ++ l'').
    unfold choose_first_enabled_match.
    rewrite bind_Some.
    exists ((length l'), m).
    unfold choose_first_enabled_match in Heqo.
    symmetry in Heqo.
    rewrite bind_None in Heqo.
    destruct Heqo as [Heqo|Heqo].
    {
        rewrite list_find_None in Heqo.
        split.
        {
            rewrite list_find_Some.
            split.
            {
                rewrite lookup_app_r.
                {
                    rewrite Nat.sub_diag.
                    simpl.
                    reflexivity.
                }
                {
                    ltac1:(lia).
                }
            }
            {
                rewrite Forall_forall in Heqo.
                split.
                {
                    apply H2.
                }
                intros i y HH1 HH2.
                apply Heqo.
                rewrite <- elem_of_list_In.
                rewrite lookup_app_l in HH1>[|apply HH2].
                rewrite elem_of_list_lookup.
                exists i.
                exact HH1.
            }
        }
        {
            rewrite delete_middle.
            reflexivity.
        }
    }
    {
        destruct Heqo as [[i' m'] [HH1 HH2]].
        inversion HH2.
    }
Qed.

Lemma order_enabled_first_1_nicely_ordered
    {Σ : StaticModel}
    initial l :
    nicely_ordered initial (order_enabled_first initial l).1
.
Proof.
    ltac1:(funelim (order_enabled_first initial l)).
    {
        rewrite <- Heqcall.
        clear Heqcall H1.
        repeat ltac1:(case_match).
        simpl. simpl in H0.
        constructor.
        {
            clear -H.
            unfold choose_first_enabled_match in H.
            rewrite bind_Some in H.
            destruct H as [[x m] [H1 H2]].
            inversion H2; subst; clear H2.
            rewrite list_find_Some in H1.
            destruct H1 as [H1 [H2 H3]].
            unfold enables_match in H2.
            apply H2.
        }
        {
            apply H0.
        }
    }
    {
        rewrite <- Heqcall.
        simpl.
        constructor.
    }
Qed.

Lemma choose_first_enabled_match_lookup
    {Σ : StaticModel}
    vs l i m rest:
    choose_first_enabled_match vs l = Some (i, m, rest) ->
    l !! i = Some m
.
Proof.
    intros H.
    unfold choose_first_enabled_match in H.
    rewrite bind_Some in H.
    destruct H as [[i' m'] [H1 H2]].
    inversion H2; subst; clear H2.
    rewrite list_find_Some in H1.
    apply H1.
Qed.

Lemma choose_first_enabled_match_elem_of
    {Σ : StaticModel} vs l i m rest:
    choose_first_enabled_match vs l = Some (i, m, rest) ->
    m_variable m ∈ vs
.
Proof.
    intros H.
    unfold choose_first_enabled_match in H.
    rewrite bind_Some in H.
    destruct H as [[i' m'] [H1 H2]].
    inversion H2; subst; clear H2.
    rewrite list_find_Some in H1.
    apply H1.
Qed.

Lemma choose_first_really_first
    {Σ : StaticModel} vs l i m rest:
    choose_first_enabled_match vs l = Some (i, m, rest) ->
    Forall (λ x : Match, ¬ enables_match vs x) (take i l)
.
Proof.
    intros H.
    unfold choose_first_enabled_match in H.
    rewrite bind_Some in H.
    destruct H as [[i' m'] [H1 H2]].
    inversion H2; subst; clear H2.
    rewrite list_find_Some in H1.
    destruct H1 as [H1 [H2 H3]].
    rewrite Forall_forall.
    intros x Hx.
    rewrite <- elem_of_list_In in Hx.
    
    assert (Htmp: (i <= length l)).
    {
        apply lookup_lt_Some in H1.
        ltac1:(lia).
    }
    rewrite elem_of_list_lookup in Hx.
    destruct Hx as [i0 Hx].
    apply lookup_lt_Some in Hx as Htmp2.
    rewrite take_length in Htmp2.
    eapply H3 with (j := i0).
    {
        rewrite lookup_take in Hx.
        {
            apply Hx.
        }
        {
            ltac1:(lia).    
        }
    }
    {
        ltac1:(lia).
    }
Qed.

Lemma delete_preserves_orderability
    {Σ : StaticModel}
    vs l l' i m:
    l ≡ₚ l' ->
    nicely_ordered vs l' ->
    m_variable m ∈ vs ->
    l !! i = Some m ->
    exists l'',
        delete i l ≡ₚ l'' /\
        nicely_ordered vs (m::l'')
.
Proof.
    intros Hperm Hno Hmvs Hli.
    apply elem_of_list_split_length in Hli.
    destruct Hli as [l1 [l2 [H1 Hlen]]].
    subst l i.
    rewrite delete_middle.
    symmetry in Hperm.
    apply Permutation_vs_elt_inv in Hperm as Hperm'.
    destruct Hperm' as [l'1 [l'2 H]].
    subst l'.
    rewrite nicely_ordered_app in Hno.
    rewrite nicely_ordered_cons in Hno.
    apply Permutation_app_inv in Hperm.
    ltac1:(setoid_rewrite nicely_ordered_cons).
    exists (l'1 ++ l'2).
    split.
    { symmetry. assumption. }
    split>[assumption|].
    rewrite nicely_ordered_app.
    destruct Hno as [H1 [H2 H3]].
    split.
    {
        eapply nicely_ordered_mono>[|apply H1].
        ltac1:(set_solver).
    }
    {
        eapply nicely_ordered_mono>[|apply H3].
        ltac1:(set_solver).
    }
Qed.

Lemma order_enabled_first_2_empty_if_can_be_ordered
    {Σ : StaticModel}
    initial l :
    (∃ l', l' ≡ₚ l /\ nicely_ordered initial l') ->
    (order_enabled_first initial l).2 = []
.
Proof.
    intros [l' [Hl'1 Hl'2]].
    ltac1:(funelim (order_enabled_first initial l)).
    {
        rewrite <- Heqcall.
        clear Heqcall.
        repeat ltac1:(case_match).
        simpl. simpl in *.
        clear H1.

        assert(Hperm := choose_first_enabled_match_perm vs ms i m' rest H).
        destruct Hperm as [Hperm Hperm'].
        subst rest.
        assert (Hno := delete_preserves_orderability vs ms l' i m').
        symmetry in Hl'1.
        specialize (Hno Hl'1 Hl'2).
        apply choose_first_enabled_match_elem_of in H as H'.
        apply choose_first_enabled_match_lookup in H as H''.
        specialize (Hno H' H'').
        destruct Hno as [l'' [Hl'' Hnol'']].
        symmetry in Hl''.
        specialize (H0 l'' Hl'').
        inversion Hnol''; subst; clear Hnol''.
        specialize (H0 H6).
        apply H0.
    }
    {
        rewrite <- Heqcall.
        clear Heqcall.
        simpl.
        clear H.
        ltac1:(rename e into Hnone).
        unfold choose_first_enabled_match in Hnone.
        rewrite bind_None in Hnone.
        destruct Hnone as [Hnone|Hnone].
        {
            rewrite list_find_None in Hnone.
            destruct l'.
            {
                apply Permutation_nil in Hl'1.
                exact Hl'1.
            }
            {
                ltac1:(exfalso).
                inversion Hl'2; subst; clear Hl'2.
                rewrite Forall_forall in Hnone.
                unfold enables_match in Hnone.
                eapply Hnone>[|apply H2].
                rewrite <- elem_of_list_In.
                apply elem_of_Permutation.
                exists l'.
                symmetry. exact Hl'1.
            }
        }
        {
            destruct Hnone as [[n m] [HH1 HH2]].
            inversion HH2.
        }
    }
Qed.

Lemma order_enabled_first_nicely_ordered
    {Σ : StaticModel}
    initial l
    :
    (∃ l', l' ≡ₚ l /\ nicely_ordered initial l' ) ->
    nicely_ordered initial ((order_enabled_first initial l).1 ++ (order_enabled_first initial l).2)
.
Proof.
    intros [l' Hl'].
    rewrite order_enabled_first_2_empty_if_can_be_ordered.
    {
        rewrite app_nil_r.
        apply order_enabled_first_1_nicely_ordered.
    }
    {
        exists l'.
        apply Hl'.
    }
Qed.



Definition valuation_satisfies_all_matches
    {Σ : StaticModel}
    {CΣ : ComputableStaticModel}
    (ρ : Valuation)
    (l : list Match)
    : Prop
:=
    ∀ x ot, (mkMatch _ x ot) ∈ l ->
    ∃ t, ρ !! x = Some t /\
    matchesb ρ t ot
.

Lemma valuation_satisfies_all_matches_perm
    {Σ : StaticModel}
    {CΣ : ComputableStaticModel}
    (l1 l2 : list Match) (ρ : Valuation)
: l1 ≡ₚ l2 ->
    valuation_satisfies_all_matches ρ l1
    -> valuation_satisfies_all_matches ρ l2
.
Proof.
    intros Hp.
    unfold valuation_satisfies_all_matches.
    intros H1 x ot Hin.
    specialize (H1 x ot).
    apply H1.
    rewrite Hp.
    exact Hin.
Qed.
