
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    flattened
.


Declare Scope ExprScope.
Declare Scope RuleLhsScope.
(*Declare Scope RuleRhsScope.*)
Declare Scope RuleScsScope.
Declare Scope ConcreteScope.

Delimit Scope ExprScope with expr.
Delimit Scope RuleLhsScope with rule_lhs.
(*Delimit Scope RuleRhsScope with rule_rhs.*)
Delimit Scope RuleScsScope with rule_scs.
Delimit Scope ConcreteScope with concrete.

(*
Section wm.
    Context
        {Σ : StaticModel}
    .

    Check AppliedOperator' symbol (Type -> Type).

End wm.

*)

Class MyContext (Operand : Type) := {
    mc_result : Type;
    mc_result_from_operand : Operand -> mc_result ;
}.

Definition MCAO {Σ : StaticModel} (Operand : Type) : Type
:=
    AppliedOperator'
        symbol
        (forall (MC : MyContext Operand), mc_result)
.

Definition mc_operator
    {Σ : StaticModel}
    {Operand : Type}
    (sym : symbol)
    : MCAO Operand
:=
    ao_operator sym
.

Definition mc_app_operand
    {Σ : StaticModel}
    {Operand : Type}
    (app : MCAO Operand)
    (operand : Operand)
    : MCAO Operand
:=
    fun MC => ao_app_operand (app MC) operand
.

Definition mc_app_ao
    {Σ : StaticModel}
    {Operand : Type}
    (app1 app2 : MCAO Operand)
    : MCAO Operand
:=
    fun MC => ao_app_ao (app1 MC) (app2 MC)
.

Definition MC_resolve
    {Σ : StaticModel}
    {Operand : Type}
    (x : MCAO Operand)
    (MC : MyContext Operand)
    : AppliedOperator' symbol mc_result
:= x MC.
    match x with
    |
    end
.


Inductive BoV_or_Expr := BE_BoV | BE_Expr .

Structure InterpretBE {Σ : StaticModel} := {
    ibe_BE : BoV_or_Expr ;
    ibe_type : Type ;
}.

Definition InterpretBE_BoV {Σ : StaticModel} : InterpretBE := {|
    ibe_BE := BE_BoV ;
    ibe_type := BuiltinOrVar ;
|}.
Canonical InterpretBE_BoV.

Definition InterpretBE_Expr {Σ : StaticModel} : InterpretBE := {|
    ibe_BE := BE_Expr ;
    ibe_type := Expression ;
|}.
Canonical InterpretBE_Expr.

(*
Inductive Operand_or_AO := OA_Operand | OA_AO.

Structure InterpretOA {Σ : StaticModel} := {
    ioa_OA : Operand_or_AO ;
    ioa_type : Type ;
}.
*)

Structure MyApply
    {Σ : StaticModel}
:= {
    ma_A : InterpretBE;
    ma_B : Type ;
    my_apply :
        AppliedOperator' symbol (ibe_type ma_A) ->
        ma_B ->
        AppliedOperator' symbol (ibe_type ma_A) ;
}.

Arguments my_apply {_} {m} _ _.
Arguments my_apply : simpl never.

Definition MyApply_operand
    {Σ : StaticModel}
    (A : InterpretBE)
    : @MyApply Σ
:= {|
    ma_A := A ;
    ma_B := (ibe_type A) ;
    my_apply := @ao_app_operand symbol (ibe_type A) ;
|}.
Canonical MyApply_operand.


Definition MyApply_ao
    {Σ : StaticModel}
    {A : InterpretBE}
    : @MyApply Σ
:= {|
    ma_A := A ;
    ma_B := (AppliedOperator' symbol (ibe_type A)) ;
    my_apply := @ao_app_ao symbol (ibe_type A) ;
|}.
Canonical MyApply_ao.


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
    := (my_apply .. (my_apply (ao_operator f) y) .. z)
    (at level 90)
    : RuleLhsScope
.

Notation "f [< y , .. , z >]"
    := (my_apply .. (my_apply (ao_operator f) y) .. z)
    (at level 90)
    : ExprScope
.

Notation "f [< y , .. , z >]"
    := (my_apply_c .. (my_apply_c (ao_operator f) y) .. z)
    (at level 90)
    : ConcreteScope
.
Locate "~".
Notation "'$' x" := (bov_variable x)
    (at level 10)
    : RuleLhsScope
.

Notation "'$' x" := (ft_variable x)
    (at level 10)
    : ExprScope
.

Notation "'llrule' l => r 'requires' s"
    := (@mkFlattenedRewritingRule
        _
        (l)%rule_lhs
        (r)%expr
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

(*
Notation "'[^' f x '^]'" :=
    (ft_unary f (x)%expr)
    : ExprScope
.

Notation "'[^' f  x  y '^]'" :=
    (ft_binary f (x)%expr (y)%expr)
    : ExprScope
.
*)

