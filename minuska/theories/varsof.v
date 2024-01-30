From Minuska Require Import
    prelude
    spec_syntax
.

Fixpoint vars_of_Expression
    {Σ : StaticModel}
    (t : Expression)
    : gset variable :=
match t with
| ft_element _ => ∅
| ft_variable x => {[x]}
| ft_nullary _ => ∅
| ft_unary _ t' => vars_of_Expression t'
| ft_binary _ t1 t2 => vars_of_Expression t1 ∪ vars_of_Expression t2
| ft_ternary _ t1 t2 t3 => vars_of_Expression t1 ∪ vars_of_Expression t2 ∪ vars_of_Expression t3
end.

#[export]
Instance VarsOf_Expression
    {Σ : StaticModel}
    : VarsOf Expression variable
:= {|
    vars_of := vars_of_Expression ; 
|}.


Definition vars_of_AP
    {Σ : StaticModel}
    (ap : AtomicProposition)
    : gset variable :=
match ap with
| apeq e1 e2 => vars_of e1 ∪ vars_of e2
end.

#[export]
Instance VarsOf_AP
    {Σ : StaticModel}
    : VarsOf AtomicProposition variable
:= {|
    vars_of := vars_of_AP ; 
|}.

Fixpoint vars_of_aosB
    {Σ : StaticModel}
    {B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VB: VarsOf B var}
    (o : PreTerm' symbol B)
    : gset var :=
match o with
| ao_operator _ => ∅
| ao_app_operand o' b => vars_of b ∪ vars_of_aosB o'
| ao_app_ao o1 o2 => vars_of_aosB o1 ∪ vars_of_aosB o2
end.

#[export]
Instance VarsOf_aosB
    {Σ : StaticModel}
    {B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VB: VarsOf B var}
    : VarsOf (PreTerm' symbol B) var
:= {|
    vars_of := vars_of_aosB ; 
|}.

Definition vars_of_BoV
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : gset variable
:=
match bov with
| bov_variable x => {[x]}
| bov_builtin _ => ∅
end.

#[export]
Instance VarsOf_BoV
    {Σ : StaticModel}
    : VarsOf BuiltinOrVar variable
:= {|
    vars_of := vars_of_BoV ; 
|}.

Definition vars_of_OpenTerm
    {Σ : StaticModel}
    (φ : OpenTerm)
    : gset variable :=
match φ with
| aoo_app o => vars_of o
| aoo_operand bov => vars_of bov
end.

#[export]
Instance VarsOf_OpenTerm 
    {Σ : StaticModel}
    : VarsOf OpenTerm variable
:= {|
    vars_of := vars_of_OpenTerm ; 
|}.

Definition vars_of_SideCondition
    {Σ : StaticModel}
    (c : SideCondition)
    : gset variable :=
match c with
| sc_constraint c' => vars_of c'
end.

#[export]
Instance VarsOf_SideCondition
    {Σ : StaticModel}
    : VarsOf SideCondition variable
:= {|
    vars_of := vars_of_SideCondition ; 
|}.

#[export]
Program Instance VarsOf_list_SideCondition
    {Σ : StaticModel}
    : VarsOf (list SideCondition) variable
:= {|
    vars_of := fun scs => ⋃ (vars_of <$> scs)
|}.

Definition vars_of_Term'B
    {Σ : StaticModel}
    {B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    (φ : Term' symbol B)
    : gset var :=
match φ with
| aoo_app aop => vars_of aop
| aoo_operand otwsc => vars_of otwsc
end.

#[export]
Instance VarsOf_Term'
    {Σ : StaticModel}
    {B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    : VarsOf (Term' symbol B) var
:= {|
    vars_of := vars_of_Term'B ; 
|}.
