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
    (o : AppliedOperator' symbol B)
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
    : VarsOf (AppliedOperator' symbol B) var
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

Definition vars_of_Match
    {Σ : StaticModel}
    (m : Match)
    : gset variable :=
match m with
| mkMatch _ x φ => {[x]} ∪ vars_of φ
end.

#[export]
Instance VarsOf_Match
    {Σ : StaticModel}
    : VarsOf Match variable
:= {|
    vars_of := vars_of_Match ; 
|}.

Definition vars_of_SideCondition
    {Σ : StaticModel}
    (c : SideCondition)
    : gset variable :=
match c with
| sc_constraint c' => vars_of c'
| sc_match m => vars_of m
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

Definition vars_of_AppliedOperatorOr'B
    {Σ : StaticModel}
    {B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    (φ : AppliedOperatorOr' symbol B)
    : gset var :=
match φ with
| aoo_app aop => vars_of aop
| aoo_operand otwsc => vars_of otwsc
end.

#[export]
Instance VarsOf_AppliedOperatorOr'
    {Σ : StaticModel}
    {B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    : VarsOf (AppliedOperatorOr' symbol B) var
:= {|
    vars_of := vars_of_AppliedOperatorOr'B ; 
|}.


Fixpoint AppliedOperator'_fmap
    {A B C : Type}
    (f : B -> C)
    (ao : AppliedOperator' A B)
    : AppliedOperator' A C
:=
match ao with
| ao_operator o => ao_operator o
| ao_app_operand ao' x => ao_app_operand (AppliedOperator'_fmap f ao') (f x)
| ao_app_ao ao1 ao2 => ao_app_ao (AppliedOperator'_fmap f ao1) (AppliedOperator'_fmap f ao2)
end.

#[export]
Instance AppliedOperator'_A_B_fmap (A : Type)
    : FMap (AppliedOperator' A)
    := @AppliedOperator'_fmap A
.


Definition AppliedOperatorOr'_fmap
    {A B C : Type}
    (f : B -> C)
    (aoo : AppliedOperatorOr' A B)
    : AppliedOperatorOr' A C
:=
match aoo with
| aoo_app ao => aoo_app (f <$> ao)
| aoo_operand o => aoo_operand (f o)
end.


#[global]
Instance AppliedOperatorOr'_A_B_fmap (A : Type)
    : FMap (AppliedOperatorOr' A)
    := @AppliedOperatorOr'_fmap A
.

#[global]
Instance AppliedOperatorOr_symbol_fmap
    {Σ : StaticModel}
    : FMap (AppliedOperatorOr' symbol)
.
Proof.
    apply AppliedOperatorOr'_A_B_fmap.
Defined.


Fixpoint AppliedOperator'_collapse_option
    {A B : Type}
    (ao : AppliedOperator' A (option B))
    : option (AppliedOperator' A B)
:=
match ao with
| ao_operator o =>
    Some (ao_operator o)

| ao_app_operand ao' x =>
    ao'' ← AppliedOperator'_collapse_option ao';
    x'' ← x;
    Some (ao_app_operand ao'' x'')

| ao_app_ao ao1 ao2 =>
    ao1'' ← AppliedOperator'_collapse_option ao1;
    ao2'' ← AppliedOperator'_collapse_option ao2;
    Some (ao_app_ao ao1'' ao2'')
end.


Definition AppliedOperatorOr'_collapse_option
    {A B : Type}
    (aoo : AppliedOperatorOr' A (option B))
    : option (AppliedOperatorOr' A B)
:=
match aoo with
| aoo_app ao =>
    tmp ← AppliedOperator'_collapse_option ao;
    Some (aoo_app tmp)
| aoo_operand op =>
    tmp ← op;
    Some (aoo_operand tmp)
end.


Fixpoint AppliedOperator'_zipWith
    {A B C D : Type}
    (fa : A -> A -> A)
    (fbc : B -> C -> D)
    (f1 : AppliedOperator' A B -> C -> D)
    (f2 : B -> AppliedOperator' A C -> D)
    (ao1 : AppliedOperator' A B)
    (ao2 : AppliedOperator' A C)
    : AppliedOperator' A D
:=
match ao1,ao2 with
| ao_operator o1, ao_operator o2 => ao_operator (fa o1 o2)
| ao_operator o1, ao_app_operand app2 op2 =>
    ao_operator o1
| ao_operator o1, ao_app_ao app21 app22 =>
    ao_operator o1
| ao_app_operand app1 op1, ao_app_operand app2 op2 =>
    ao_app_operand
        (AppliedOperator'_zipWith fa fbc f1 f2 app1 app2)
        (fbc op1 op2)
| ao_app_operand app1 op1, ao_operator o2 =>
    ao_operator o2
| ao_app_operand app1 op1, ao_app_ao app21 app22 =>
    ao_app_operand
        ((AppliedOperator'_zipWith fa fbc f1 f2 app1 app21))
        (f2 op1 app22)
| ao_app_ao app11 app12, ao_app_ao app21 app22 =>
    ao_app_ao
        (AppliedOperator'_zipWith fa fbc f1 f2 app11 app21)
        (AppliedOperator'_zipWith fa fbc f1 f2 app12 app22)
| ao_app_ao app11 app12, ao_operator op2 =>
    ao_operator op2
| ao_app_ao app11 app12, ao_app_operand app21 op22 =>
    ao_app_operand 
        (AppliedOperator'_zipWith fa fbc f1 f2 app11 app21)
        (f1 app12 op22)
end.

Fixpoint AO'_getOperator {A B : Type}
    (ao : AppliedOperator' A B)
    : A :=
match ao with
| ao_operator o => o
| ao_app_operand ao' _ => AO'_getOperator ao'
| ao_app_ao ao' _ => AO'_getOperator ao'
end.


