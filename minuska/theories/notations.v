
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    flattened
.

Declare Scope SymbolicScope.
Declare Scope ConcreteScope.
(*Declare Scope RuleScsScope.*)

Delimit Scope SymbolicScope with symbolic.
Delimit Scope ConcreteScope with concrete.
(*Delimit Scope RuleScsScope with rule_scs.*)


Record ExprAndBoV {Σ : StaticModel} : Type := mkExprAndBoV {
    eab_expr : Expression ;
    eab_bov : BuiltinOrVar ;
}.

Arguments mkExprAndBoV {Σ} eab_expr eab_bov.

Class TagLHS := mkTagLHS {}.
Class TagRHS := mkTagRHS {}.

Class Resolver {Σ : StaticModel} := {
    operand_type : Type ;
    (*operand_of_eab : ExprAndBoV -> operand_type ; *)
    inject_variable : variable -> operand_type ;
}.

#[export]
Instance Resolver_1 {Σ : StaticModel} {_T1 : TagLHS} : Resolver := {
    operand_type := BuiltinOrVar ;
    (*operand_of_eab := eab_bov ;*)
    inject_variable := bov_variable;
}.

#[export]
Instance Resolver_2 {Σ : StaticModel} {_T2 : TagRHS} : Resolver := {
    operand_type := Expression ;
    (*operand_of_eab := eab_expr ;*)
    inject_variable := ft_variable;
}.
(*
Class Coercer {Σ : StaticModel} (T : Type) := {
    mycoerc : T -> Expression ;
}.

#[export]
Instance Coercer_eab {Σ : StaticModel} {_T : TagRHS} : Coercer ExprAndBoV := {|
    mycoerc := eab_expr ;
|}.

#[export]
Instance Coercer_expr {Σ : StaticModel} {_T : TagRHS} : Coercer Expression := {|
    mycoerc := fun x => x ;
|}.
*)
(*
Notation "'$' x" :=
    (mkExprAndBoV (ft_variable x) (bov_variable x))
    (at level 40)
.
*)

Notation "'$' x" :=
    (inl (inject_variable x))
    (at level 40)
.

Class MyApply
    {Σ : StaticModel}
    {_R : Resolver}
    (T2 : Type)
:= {
    my_apply : 
        AppliedOperator' symbol operand_type ->
        T2 ->
        AppliedOperator' symbol operand_type ;
}.

#[export]
Instance MyApply_direct_operand
    {Σ : StaticModel}
    {_R : Resolver}
    : MyApply operand_type
:= {|
    my_apply := fun x y => ao_app_operand x y ;
|}.

(*
#[export]
Instance MyApply_eab_operand
    {Σ : StaticModel}
    {_R : Resolver}
    : MyApply ExprAndBoV
:= {|
    my_apply := fun x y => ao_app_operand x (operand_of_eab y) ;
|}.
*)
#[export]
Instance MyApply_ao
    {Σ : StaticModel}
    {_R : Resolver}
    : MyApply (AppliedOperator' symbol operand_type)
:= {|
    my_apply := fun x y => @ao_app_ao symbol _ x y ;
|}.


(*

Structure MyApply {Σ : StaticModel} {_R : Resolver} := {
    #[canonical=yes] mal_T2 : Type ;
    #[canonical=no] my_apply :
        AppliedOperator' symbol operand_type ->
        mal_T2 ->
        AppliedOperator' symbol operand_type ;
}.

Arguments my_apply {_} {_} {m} _ _.
Arguments my_apply : simpl never.

Definition MyApply_operand
    {Σ : StaticModel}
    {_R : Resolver}
    : MyApply
:= {|
    my_apply := fun x y => ao_app_operand x y ;
|}.
Canonical MyApply_operand.

Definition MyApply_ao
    {Σ : StaticModel}
    {_R : Resolver}
    : MyApply
:= {|
    my_apply := fun x y => @ao_app_ao symbol _ x y ;
|}.
Canonical MyApply_ao.
Print Canonical Projections.
*)
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

(*
Definition AOBV {Σ : StaticModel} : Type
:=
    AppliedOperator' symbol BuiltinOrVar
.

Definition ArgTypeL {Σ : StaticModel} : Type
:=
    ((BuiltinOrVar)+(AOBV))
.

Definition AOBE {Σ : StaticModel} : Type
:=
    AppliedOperator' symbol Expression
.


Definition ArgTypeR {Σ : StaticModel} : Type
:=
    ((Expression)+(AOBE))
.


Definition inject_bov_l
    {Σ : StaticModel}
    (x : BuiltinOrVar)
    : ArgTypeL
:=
    inl x
.

Definition inject_bov_r
    {Σ : StaticModel}
    (x : AOBV)
    : ArgTypeL
:=
    inr x
.


Definition inject_expr_l
    {Σ : StaticModel}
    (x : Expression)
    : ArgTypeR
:=
    inl x
.

Definition inject_expr_r
    {Σ : StaticModel}
    (x : AOBE)
    : ArgTypeR
:=
    inr x
.

Coercion inject_bov_l : BuiltinOrVar >-> ArgTypeL.
Coercion inject_bov_r : AOBV >-> ArgTypeL.
Coercion inject_expr_l : Expression >-> ArgTypeR.
Coercion inject_expr_r : AOBE >-> ArgTypeR.
*)

Definition to_AppliedOperator'
    {Σ : StaticModel}
    {T : Type}
    (s : symbol)
    (l : list ((T)+(AppliedOperator' symbol T)))
    : AppliedOperator' symbol T
:=
    fold_left
        (fun a b =>
            match b with
            | inl b' => ao_app_operand a b'
            | inr b' => ao_app_ao a b'
            end
        )
        l
        (ao_operator s)
.

Definition to_AppliedOperatorOr'
    {Σ : StaticModel}
    {T : Type}
    (x : ((T)+(AppliedOperator' symbol T)))
    : AppliedOperatorOr' symbol T
:=
match x with
| inl x' => aoo_operand x'
| inr x' => aoo_app x'
end
.

Notation "f [<>]" := (inr (ao_operator f))
    (at level 90)
.


Notation "f [< y , .. , z >]"
:=
    (inr (to_AppliedOperator' f (@cons ((operand_type)+(AppliedOperator' symbol operand_type)) y .. (@cons ((operand_type)+(AppliedOperator' symbol operand_type)) z (@nil ((operand_type)+(AppliedOperator' symbol operand_type)))) ..)))
    (at level 90)
.
(*
    Definition my_type_of {T : Type} (x : T) : Type := T.
Notation "f [< y , .. , z >]"
    := (@my_apply _ _ (my_type_of z) _ .. (@my_apply _ _ (my_type_of y) _ (ao_operator f) y) .. z)
    (at level 90)
.
*)
Notation "f [< y , .. , z >]"
    := (my_apply_c .. (my_apply_c (ao_operator f) y) .. z)
    (at level 90)
    : ConcreteScope
.

About mkFlattenedRewritingRule.

Notation "'llrule' l => r 'requires' s"
    := (@mkFlattenedRewritingRule
        _
        ((fun (_:TagLHS) => l) mkTagLHS) (* why not %symbolic ?*)
        ((fun (_:TagRHS) => r) mkTagRHS)%symbolic
        (s)%symbolic
    )
    (at level 200)
.

Notation "'rule' l => r 'requires' s"
    := (llrule
        (to_AppliedOperatorOr' l)
        =>
        (to_AppliedOperatorOr' r) 
        requires
        s
    )
    (at level 200)
.
