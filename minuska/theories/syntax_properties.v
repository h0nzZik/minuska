From Minuska Require Import
    prelude
    spec_syntax
.

 Section vars_of.

    Definition vars_of_AP
        {Σ : Signature}
        (ap : AtomicProposition)
        : gset variable :=
    match ap with
    | ap1 _ x => {[x]}
    | ap2 _ x y => {[x;y]}
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

    Fixpoint vars_of_OpenTerm
        {Σ : Signature}
        (φ : OpenTerm)
        : gset variable :=
    match φ with
    | ao_operator s => ∅
    | ao_app_operand φ' (bov_variable x)
        => {[x]} ∪ vars_of_OpenTerm φ'
    | ao_app_operand φ' (bov_builtin _)
        => vars_of_OpenTerm φ'
    | ao_app_ao φ1 φ2
        => vars_of_OpenTerm φ1 ∪ vars_of_OpenTerm φ2
    end.

    Definition vars_of_SideCondition
        {Σ : Signature}
        (c : SideCondition)
        : gset variable :=
    match c with
    | sc_constraint c' => vars_of_Constraint c'
    | sc_match x φ => {[x]} ∪ vars_of_OpenTerm φ
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

    Fixpoint vars_of_LhsPattern
        {Σ : Signature}
        (φ : LhsPattern)
        : gset variable :=
    match φ with
    | ao_operator o => ∅
    | ao_app_operand x y
        => vars_of_LhsPattern x ∪ vars_of_OpenTermWSC y
    | ao_app_ao x y
        => vars_of_LhsPattern x ∪ vars_of_LhsPattern y
    end.

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

    Fixpoint vars_of_RhsPattern
        {Σ : Signature}
        (φ : RhsPattern)
        : gset variable :=
    match φ with
    | ao_operator _ => ∅
    | ao_app_operand  φ' t
        => vars_of_RhsPattern φ' ∪ vars_of_Expression t
    | ao_app_ao φ1 φ2
        => vars_of_RhsPattern φ1 ∪ vars_of_RhsPattern φ2
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
    | LR_Left,lr_var x _ => {[var_of_WithASideCondition_variable x]}
    | LR_Left, lr_builtin _ _ => ∅
    | LR_Left, lr_pattern φ _ => vars_of_LhsPattern φ
    | LR_Right, lr_var _ e => vars_of_Expression e
    | LR_Right, lr_builtin _ e => vars_of_Expression e
    | LR_Right, lr_pattern _ φ => vars_of_RhsPattern φ
    end.


End vars_of.
