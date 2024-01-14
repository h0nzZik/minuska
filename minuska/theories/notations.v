
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    flattened
.


Declare Scope RuleLhsScope.
Declare Scope RuleRhsScope.
Declare Scope RuleScsScope.
Declare Scope ConcreteScope.

Delimit Scope RuleLhsScope with rule_lhs.
Delimit Scope RuleRhsScope with rule_rhs.
Delimit Scope RuleScsScope with rule_scs.
Delimit Scope ConcreteScope with concrete.

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


Structure MyApplyConcrete {Σ : StaticModel} := {
    mac_T2 : Type ;
    my_apply_c :
        AppliedOperator' symbol builtin_value ->
        mac_T2 ->
        AppliedOperator' symbol builtin_value ;
}.

Arguments my_apply_c {_} {m} _ _.
Arguments my_apply_c : simpl never.

Definition MyApplyConcrete_operand {Σ : StaticModel} : MyApplyConcrete := {|
    my_apply_c := fun x y => ao_app_operand x y ;
|}.
Canonical MyApplyConcrete_operand.

Definition MyApplyConcrete_ao {Σ : StaticModel} : MyApplyConcrete := {|
    my_apply_c := fun x y => @ao_app_ao symbol builtin_value x y ;
|}.
Canonical MyApplyConcrete_ao.

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

Notation "f [< y , .. , z >]"
    := (my_apply_c .. (my_apply_c (ao_operator f) y) .. z)
    (at level 90)
    : ConcreteScope
.

Notation "'$' x" := (bov_variable x)
    (at level 200)
    : RuleLhsScope
.

Notation "'$' x" := (ft_variable x)
    (at level 200)
    : RuleRhsScope
.


Notation "'$' x" := (ft_variable x)
    (at level 200)
    : RuleScsScope
.

Notation "'llrule' l => r 'requires' s"
    := (@mkFlattenedRewritingRule
        _
        (l)%rule_lhs
        (r)%rule_rhs
        (s)%rule_scs
    )
    (at level 200)
.

Notation "'rule' l => r 'requires' s"
    := (llrule
        (aoo_app l)
        =>
        (aoo_app r) 
        requires
        s
    )
    (at level 200)
.
