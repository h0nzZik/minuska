
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    flattened
.


Declare Scope RuleLhsScope.
Declare Scope RuleRhsScope.

Delimit Scope RuleLhsScope with rule_lhs.
Delimit Scope RuleRhsScope with rule_rhs.

Structure MyApplyLhs {Σ : StaticModel} := {
    mal_T2 : Type ;
    my_apply_lhs :
        AppliedOperator' symbol BuiltinOrVar ->
        mal_T2 ->
        AppliedOperator' symbol BuiltinOrVar ;
}.

Arguments my_apply_lhs {_} {m} _ _.
Arguments my_apply_lhs : simpl never.

Definition MyApplyLhs_operand {Σ : StaticModel} : MyApplyLhs := {|
    my_apply_lhs := fun x y => ao_app_operand x y ;
|}.
Canonical MyApplyLhs_operand.

Definition MyApplyLhs_ao {Σ : StaticModel} : MyApplyLhs := {|
    my_apply_lhs := fun x y => @ao_app_ao symbol BuiltinOrVar x y ;
|}.
Canonical MyApplyLhs_ao.


Structure MyApplyRhs {Σ : StaticModel} := {
    mar_T2 : Type ;
    my_apply_rhs :
        AppliedOperator' symbol Expression ->
        mar_T2 ->
        AppliedOperator' symbol Expression ;
}.

Arguments my_apply_rhs {_} {m} _ _.
Arguments my_apply_rhs : simpl never.

Definition MyApplyRhs_operand {Σ : StaticModel} : MyApplyRhs := {|
    my_apply_rhs := fun x y => ao_app_operand x y ;
|}.
Canonical MyApplyRhs_operand.

Definition MyApplyRhs_ao {Σ : StaticModel} : MyApplyRhs := {|
    my_apply_rhs := fun x y => @ao_app_ao symbol Expression x y ;
|}.
Canonical MyApplyRhs_ao.

Notation "f [<>]" := (ao_operator f)
    (at level 90)
.

Notation "f [< y , .. , z >]"
    := (my_apply_lhs .. (my_apply_lhs (ao_operator f) y) .. z)
    (at level 90)
    : RuleLhsScope
.

Notation "f [< y , .. , z >]"
    := (my_apply_rhs .. (my_apply_rhs (ao_operator f) y) .. z)
    (at level 90)
    : RuleRhsScope
.

Notation "'$' x" := (bov_variable x)
    (at level 200)
    : RuleLhsScope
.

Notation "'$' x" := (ft_variable x)
    (at level 200)
    : RuleRhsScope
.


Notation "'llrule' l => r 'requires' s"
    := (@mkFlattenedRewritingRule
        _
        (l)%rule_lhs
        (r)%rule_rhs
        (s)
    )
    (at level 200)
.

Notation "'rule' l => r 'requires' s"
    := (llrule
        (aoo_app _ _ l)
        =>
        (aoo_app _ _ r) 
        requires
        s
    )
    (at level 200)
.
