From Minuska Require Import
    prelude
    spec_syntax
.

Fixpoint vars_of_Expression
    {Σ : Signature}
    (t : Expression)
    : gset variable :=
match t with
| ft_element _ => ∅
| ft_variable x => {[x]}
| ft_unary _ t' => vars_of_Expression t'
| ft_binary _ t1 t2 => vars_of_Expression t1 ∪ vars_of_Expression t2
end.

Definition vars_of_AP
    {Σ : Signature}
    (ap : AtomicProposition)
    : gset variable :=
match ap with
| apeq e1 e2 => vars_of_Expression e1 ∪ vars_of_Expression e2
| ap1 _ e => vars_of_Expression e
| ap2 _ e1 e2 => vars_of_Expression e1 ∪ vars_of_Expression e2
end.

Fixpoint vars_of_Constraint
    { Σ : Signature }
    (c : Constraint)
    : gset variable :=
match c with
| c_True => ∅
| c_atomic ap => vars_of_AP ap
| c_and c1 c2 => vars_of_Constraint c1 ∪ vars_of_Constraint c2
| c_not c' => vars_of_Constraint c'
end.

Fixpoint vars_of_aosb
    {Σ : Signature}
    (o : AppliedOperator' symbol BuiltinOrVar)
    : gset variable :=
match o with
| ao_operator _ => ∅
| ao_app_operand o' (bov_builtin _) => vars_of_aosb o'
| ao_app_operand o' (bov_variable x) => {[x]} ∪ vars_of_aosb o'
| ao_app_ao o1 o2 => vars_of_aosb o1 ∪ vars_of_aosb o2
end.

Definition vars_of_BoV
    {Σ : Signature}
    (bov : BuiltinOrVar)
    : gset variable
:=
match bov with
| bov_variable x => {[x]}
| bov_builtin _ => ∅
end.

Definition vars_of_OpenTerm
    {Σ : Signature}
    (φ : OpenTerm)
    : gset variable :=
match φ with
| aoo_app _ _ o => vars_of_aosb o
| aoo_operand _ _ bov => vars_of_BoV bov
end.

Definition vars_of_Match
    {Σ : Signature}
    (m : Match)
    : gset variable :=
match m with
| mkMatch _ x φ => {[x]} ∪ vars_of_OpenTerm φ
end.

Definition vars_of_SideCondition
    {Σ : Signature}
    (c : SideCondition)
    : gset variable :=
match c with
| sc_constraint c' => vars_of_Constraint c'
| sc_match m => vars_of_Match m
end.

Fixpoint vars_of_OpenTermWSC
    {Σ : Signature}
    (φc : OpenTermWSC)
    : gset variable :=
match φc with
| wsc_base φ => vars_of_OpenTerm φ
| wsc_sc φ c
    => vars_of_OpenTermWSC φ ∪ vars_of_SideCondition c
end.

Fixpoint vars_of_AppliedOperator'_symbol_OpenTermWSC
    {Σ : Signature}
    (φ : AppliedOperator' symbol OpenTermWSC)
    : gset variable :=
match φ with
| ao_operator o => ∅
| ao_app_operand x y
    => vars_of_AppliedOperator'_symbol_OpenTermWSC x ∪ vars_of_OpenTermWSC y
| ao_app_ao x y
    => vars_of_AppliedOperator'_symbol_OpenTermWSC x ∪ vars_of_AppliedOperator'_symbol_OpenTermWSC y
end.

Definition vars_of_LhsPattern
    {Σ : Signature}
    (φ : LhsPattern)
    : gset variable :=
match φ with
| aoo_app _ _ aop => vars_of_AppliedOperator'_symbol_OpenTermWSC aop
| aoo_operand _ _ otwsc => vars_of_OpenTermWSC otwsc
end.

Fixpoint vars_of_AppliedOperator_sym_fterm
    {Σ : Signature}
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
    {Σ : Signature}
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
    {Σ : Signature}
    (φ : RhsPattern)
    : gset variable :=
match φ with
| aoo_app _ _ aop => vars_of_AppliedOperator'_symbol_Expression aop
| aoo_operand _ _ exp => vars_of_Expression exp
end.

Fixpoint var_of_WithASideCondition_variable
    {Σ : Signature}
    (x : WithASideCondition variable)
    : variable :=
match x with
| wsc_base x' => x'
| wsc_sc x' sc => var_of_WithASideCondition_variable x'
end.

Definition vars_of_LocalRewrite
    {Σ : Signature}
    (lr : LeftRight)
    (r : LocalRewrite)
    : gset variable :=
match lr,r with
| LR_Left, Build_LocalRewrite _ φ1 φ2 => vars_of_LhsPattern φ1
| LR_Right, Build_LocalRewrite _ φ1 φ2 => vars_of_RhsPattern φ2
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

#[global]
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
| aoo_app _ _ ao => aoo_app _ _ (AppliedOperator'_fmap f ao)
| aoo_operand _ _ o => aoo_operand _ _ (f o)
end.


#[global]
Instance AppliedOperatorOr'_A_B_fmap (A : Type)
    : FMap (AppliedOperatorOr' A)
    := @AppliedOperatorOr'_fmap A
.

#[global]
Instance AppliedOperatorOr_symbol_fmap
    {Σ : Signature}
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