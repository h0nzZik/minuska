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
| ft_unary _ t' => vars_of_Expression t'
| ft_binary _ t1 t2 => vars_of_Expression t1 ∪ vars_of_Expression t2
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
| ap1 _ e => vars_of e
| ap2 _ e1 e2 => vars_of e1 ∪ vars_of e2
end.

#[export]
Instance VarsOf_AP
    {Σ : StaticModel}
    : VarsOf AtomicProposition variable
:= {|
    vars_of := vars_of_AP ; 
|}.


Fixpoint vars_of_Constraint
    { Σ : StaticModel }
    (c : Constraint)
    : gset variable :=
match c with
| c_True => ∅
| c_atomic ap => vars_of ap
| c_and c1 c2 => vars_of_Constraint c1 ∪ vars_of_Constraint c2
(*| c_not c' => vars_of_Constraint c'*)
end.

#[export]
Instance VarsOf_Constraint
    {Σ : StaticModel}
    : VarsOf Constraint variable
:= {|
    vars_of := vars_of_Constraint ; 
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
| aoo_app _ _ o => vars_of o
| aoo_operand _ _ bov => vars_of bov
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

Fixpoint vars_of_WithASideConditionB
    {Σ : StaticModel}
    {B : Type}
    {_VB : VarsOf B variable}
    (φc : WithASideCondition B)
    : gset variable :=
match φc with
| wsc_base φ => vars_of φ
| wsc_sc φ c
    => vars_of_WithASideConditionB φ ∪ vars_of c
end.

#[export]
Instance VarsOf_WithASideConditionB
    {Σ : StaticModel}
    {B : Type}
    {_VB : VarsOf B variable}
    : VarsOf (WithASideCondition B) variable
:= {|
    vars_of := vars_of_WithASideConditionB ; 
|}.

(*
Fixpoint vars_of_AppliedOperator'_symbol_OpenTermWSC
    {Σ : StaticModel}
    (φ : AppliedOperator' symbol OpenTermWSC)
    : gset variable :=
match φ with
| ao_operator o => ∅
| ao_app_operand x y
    => vars_of_AppliedOperator'_symbol_OpenTermWSC x ∪ vars_of_OpenTermWSC y
| ao_app_ao x y
    => vars_of_AppliedOperator'_symbol_OpenTermWSC x ∪ vars_of_AppliedOperator'_symbol_OpenTermWSC y
end.
*)

Definition vars_of_AppliedOperatorOr'B
    {Σ : StaticModel}
    {B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    (φ : AppliedOperatorOr' symbol B)
    : gset var :=
match φ with
| aoo_app _ _ aop => vars_of aop
| aoo_operand _ _ otwsc => vars_of otwsc
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

(*
Fixpoint vars_of_AppliedOperator_sym_fterm
    {Σ : StaticModel}
    (op : AppliedOperator' symbol Expression)
    : gset variable :=
match op with
| ao_operator _ => ∅
| ao_app_operand aps' o =>
    vars_of_AppliedOperator_sym_fterm aps' ∪ vars_of_Expression o
| ao_app_ao aps1 aps2 =>
    vars_of_AppliedOperator_sym_fterm aps1 ∪ vars_of_AppliedOperator_sym_fterm aps2
end.

Fixpoint vars_of_AppliedOperator'_symbol_Expression
    {Σ : StaticModel}
    (φ : AppliedOperator' symbol Expression)
    : gset variable :=
match φ with
| ao_operator _ => ∅
| ao_app_operand  φ' t
    => vars_of_AppliedOperator'_symbol_Expression φ' ∪ vars_of_Expression t
| ao_app_ao φ1 φ2
    => vars_of_AppliedOperator'_symbol_Expression φ1 ∪ vars_of_AppliedOperator'_symbol_Expression φ2
end.

Definition vars_of_RhsPattern
    {Σ : StaticModel}
    (φ : RhsPattern)
    : gset variable :=
match φ with
| aoo_app _ _ aop => vars_of_AppliedOperator'_symbol_Expression aop
| aoo_operand _ _ exp => vars_of_Expression exp
end.

Fixpoint var_of_WithASideCondition_variable
    {Σ : StaticModel}
    (x : WithASideCondition variable)
    : variable :=
match x with
| wsc_base x' => x'
| wsc_sc x' sc => var_of_WithASideCondition_variable x'
end.
*)

Definition vars_of_LocalRewrite
    {Σ : StaticModel}
    (lr : LeftRight)
    (r : LocalRewrite)
    : gset variable :=
match lr,r with
| LR_Left, Build_LocalRewrite _ φ1 φ2 => vars_of φ1
| LR_Right, Build_LocalRewrite _ φ1 φ2 => vars_of φ2
end.


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
| aoo_app _ _ ao => aoo_app _ _ (f <$> ao)
| aoo_operand _ _ o => aoo_operand _ _ (f o)
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
| aoo_app _ _ ao =>
    tmp ← AppliedOperator'_collapse_option ao;
    Some (aoo_app _ _ tmp)
| aoo_operand _ _ op =>
    tmp ← op;
    Some (aoo_operand _ _ tmp)
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