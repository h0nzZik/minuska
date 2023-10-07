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

Print AppliedOperator'.
Print AppliedOperatorOr'.
Print OpenTerm.

Fixpoint AppliedOperator'_symbol_A_to_pair_OpenTerm_SC
    {Σ : Signature}
    {A : Set}
    (A_to_OpenTerm_SC : A ->
        ((AppliedOperator' symbol BuiltinOrVar) * (list SideCondition))
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
        | (t2, scs2) =>
            ((ao_app_ao t1 t2), scs1 ++ scs2)
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

Lemma correct_AppliedOperator'_symbol_A_to_pair_OpenTerm_SC
    {Σ : Signature}
    {A : Set}
    (A_to_OpenTerm_SC : A ->
        ((AppliedOperator' symbol BuiltinOrVar) * (list SideCondition))
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
    (x : AppliedOperator' symbol A)
    (g : AppliedOperator' symbol builtin_value)
    (ρ : Valuation)
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
    induction x; cbn.
    {
        unfold valuation_satisfies_scs.
        rewrite list.Forall_nil.
        ltac1:(naive_solver).
    }
Qed.

Print LhsPattern.

Fixpoint LhsPattern_to_pair_OpenTerm_SC
    {Σ : Signature}
    (l : LhsPattern)
    : (OpenTerm * (list SideCondition))
:=
match l with
| aoo_app _ _ 
end.

Print LocalRewrite.

Print LocalRewriteOrOpenTermOrBOV.

Print UncondRewritingRule.

Print RewritingRule.