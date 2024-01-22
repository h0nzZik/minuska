From stdpp Require Import finite.

From Minuska Require Import
    prelude
.

Polymorphic Cumulative
Inductive AppliedOperator' (operator : Type) (operand : Type)
: Type
:=
| ao_operator (s : operator)
| ao_app_operand
    (aps : AppliedOperator' operator operand)
    (b : operand) 
| ao_app_ao
    (aps : AppliedOperator' operator operand)
    (x : AppliedOperator' operator operand)
.


Polymorphic Cumulative
Inductive AppliedOperatorOr'
    (Operator : Type)
    (Operand : Type)
    : Type :=
| aoo_app (ao : AppliedOperator' Operator Operand)
| aoo_operand (operand : Operand)
.


Arguments aoo_operand {Operator Operand}%type_scope operand.
Arguments aoo_app {Operator Operand}%type_scope ao.


Polymorphic
Definition GroundTerm' (symbol : Type) (builtin : Type)
    := (AppliedOperatorOr' symbol builtin)
.

Arguments ao_operator {operator operand}%type_scope s.
Arguments ao_app_operand {operator operand}%type_scope aps b.
Arguments ao_app_ao {operator operand}%type_scope aps x.

Class MVariables (variable : Type) := {
    variable_eqdec :: EqDecision variable ;
    variable_countable :: Countable variable ;
    variable_infinite :: Infinite variable ;
}.

Class Symbols (symbol : Type) := {
    symbol_eqdec :: EqDecision symbol ;
    symbol_countable :: Countable symbol ;
}.

Class Builtin {symbol : Type} {symbols : Symbols symbol} := {
    builtin_value
        : Type ;
    builtin_value_eqdec
        :: EqDecision builtin_value ;
    
    builtin_nullary_function
        : Type ;
    builtin_nullary_function_eqdec
        :: EqDecision builtin_nullary_function ;

    builtin_unary_function
        : Type ;
    builtin_unary_function_eqdec
        :: EqDecision builtin_unary_function ;

    builtin_binary_function
        : Type ;
    builtin_binary_function_eqdec
        :: EqDecision builtin_binary_function ;
    
    builtin_ternary_function
        : Type ;
    builtin_ternary_function_eqdec
        :: EqDecision builtin_ternary_function ;

    builtin_nullary_function_interp
        : builtin_nullary_function
        -> (GroundTerm' symbol builtin_value) ;

    builtin_unary_function_interp
        : builtin_unary_function
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value) ;

    builtin_binary_function_interp
        : builtin_binary_function
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value) ;

    builtin_ternary_function_interp
        : builtin_ternary_function
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value) ;
}.

Class StaticModel := {
    symbol : Type ;
    variable : Type ;
    symbols :: Symbols symbol ;
    builtin :: Builtin ;
    variables :: MVariables variable ;
}.

Class VarsOf
    (A : Type)
    (var: Type)
    {_Ev : EqDecision var}
    {_Cv : Countable var}
    :=
{
    vars_of : A -> gset var ;
}.

Arguments vars_of : simpl never.

Definition GroundTerm {Σ : StaticModel}
    := GroundTerm' symbol builtin_value
.

Inductive Expression
    {Σ : StaticModel}
    :=
| ft_element (e : GroundTerm)
| ft_variable (x : variable)
| ft_nullary (f : builtin_nullary_function)
| ft_unary (f : builtin_unary_function) (t : Expression)
| ft_binary (f : builtin_binary_function) (t1 : Expression) (t2 : Expression)
| ft_ternary (f : builtin_ternary_function) (t1 : Expression) (t2 : Expression) (t3 : Expression)
.

Inductive AtomicProposition {Σ : StaticModel} :=
| apeq (e1 : Expression) (e2 : Expression)
.

Inductive BuiltinOrVar {Σ : StaticModel} :=
| bov_builtin (b : builtin_value)
| bov_variable (x : variable)
.

Definition OpenTerm {Σ : StaticModel}
    := AppliedOperatorOr' symbol BuiltinOrVar
.

Record Match {Σ : StaticModel} := mkMatch {
  m_variable : variable ;
  m_term : OpenTerm ;
}.

Inductive SideCondition {Σ : StaticModel} :=
| sc_constraint (c : AtomicProposition)
| sc_match (m : Match)
.

Inductive WithASideCondition {Σ : StaticModel} (Base : Type) :=
|  wsc_base (φ : Base)
|  wsc_sc (φc : WithASideCondition Base) (sc : SideCondition)
.

Arguments wsc_base {Σ} {Base}%type_scope φ.
Arguments wsc_sc {Σ} {Base}%type_scope φc sc.

Definition OpenTermWSC {Σ : StaticModel}
    := WithASideCondition (@OpenTerm Σ)
.

Definition LhsPattern {Σ : StaticModel} :=
    AppliedOperatorOr' symbol OpenTermWSC
.

Definition RhsPattern {Σ : StaticModel} :=
    AppliedOperatorOr' symbol Expression
.

Record LocalRewrite {Σ : StaticModel} := {
    lr_from : LhsPattern ;
    lr_to : RhsPattern ;
}.

Inductive LocalRewriteOrOpenTermOrBOV {Σ : StaticModel} :=
| lp_rewrite (r : LocalRewrite)
| lp_basicpat (φ : OpenTerm)
| lp_bov (bx : BuiltinOrVar)
. 

Definition UncondRewritingRule {Σ : StaticModel}
    := AppliedOperatorOr' symbol LocalRewriteOrOpenTermOrBOV
.

Definition RewritingRule {Σ : StaticModel}
    := WithASideCondition UncondRewritingRule
.

Inductive LeftRight : Set := LR_Left | LR_Right.

Equations Derive NoConfusion for AppliedOperator'.
Equations Derive NoConfusion for AtomicProposition.
Equations Derive NoConfusion for Expression.
Equations Derive NoConfusion for WithASideCondition.
Equations Derive NoConfusion for LocalRewrite.

Section eqdec.

    #[export]
    Instance AppliedOperator'_eqdec
        {symbol : Type}
        {symbols : Symbols symbol}
        (builtin : Type)
        {builtin_dec : EqDecision builtin}
        : EqDecision (AppliedOperator' symbol builtin)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance GroundTerm'_eqdec
        {A : Type}
        {symbols : Symbols A}
        (T : Type)
        {T_dec : EqDecision T}
        : EqDecision (GroundTerm' A T)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance Expression_eqdec {Σ : StaticModel}
        : EqDecision (Expression)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance LeftRight_eqdec
        : EqDecision LeftRight
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Program Instance LeftRight_fin
        : Finite LeftRight
    := {|
        enum := [LR_Left;LR_Right];
    |}.
    Next Obligation.
        ltac1:(compute_done).
    Qed.
    Next Obligation.
        destruct x;
        ltac1:(compute_done).
    Qed.
    Fail Next Obligation.

    #[export]
    Instance atomicProposition_eqdec {Σ : StaticModel}
        : EqDecision AtomicProposition
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance BuiltinOrVar_eqdec {Σ : StaticModel}
        : EqDecision BuiltinOrVar
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance GroundTerm_eqdec {Σ : StaticModel}
        : EqDecision GroundTerm
    .
    Proof.
        intros e1 e2.
        apply GroundTerm'_eqdec.
        apply builtin_value_eqdec.
    Defined.

    #[export]
    Instance  OpenTerm_eqdec {Σ : StaticModel}
        : EqDecision OpenTerm
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance  Match_eqdec {Σ : StaticModel}
        : EqDecision Match
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance  SideCondition_eqdec {Σ : StaticModel}
        : EqDecision SideCondition
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance  OpenTermWSC_eqdec {Σ : StaticModel}
        : EqDecision OpenTermWSC
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance LhsPattern_eqdec {Σ : StaticModel}
        : EqDecision LhsPattern
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance RhsPattern_eqdec {Σ : StaticModel}
        : EqDecision RhsPattern
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance WithASideCondition_eqdec
        {Σ : StaticModel}
        (A : Type)
        (A_eqdec : EqDecision A)
        : EqDecision (WithASideCondition A)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance LocalRewrite_eqdec {Σ : StaticModel}
        : EqDecision LocalRewrite
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

End eqdec.

Section countable.

    Fixpoint AppliedOperator'_to_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : AppliedOperator' symbol builtin)
        : gen_tree symbol
    :=
    match a with
    | (ao_operator s) => GenLeaf s
    | (ao_app_operand aps b) =>
        (
            let x := (encode (0, encode b)) in
            GenNode (Pos.to_nat x) ([AppliedOperator'_to_gen_tree symbol builtin aps;AppliedOperator'_to_gen_tree symbol builtin aps(* we duplicate it to make the reverse simpler*)])
        )
    | (ao_app_ao aps1 aps2)
        => (
            let xd := (1, encode 0) in
            let x := (encode xd) in
            GenNode (Pos.to_nat x) ([AppliedOperator'_to_gen_tree _ _ aps1; AppliedOperator'_to_gen_tree _ _ aps2])
        )
    end.

    Fixpoint AppliedOperator'_of_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (t : gen_tree symbol)
        : option (AppliedOperator' symbol builtin)
    :=
    match t with
    | (GenLeaf s)
        => Some (ao_operator s)
    | (GenNode n [gt1;gt2]) =>
        let d := (@decode (nat*positive) _ _ (Pos.of_nat n)) in
        match d with
            | Some (0, pb) =>
                let d' := (@decode builtin _ _ pb) in
                match d' with
                | Some b =>
                    let d'' := (AppliedOperator'_of_gen_tree symbol builtin gt1) in
                    match d'' with 
                    | Some as1 => Some (ao_app_operand as1 b)
                    | _ => None
                    end
                | _ => None
                end
            | Some (1, _) =>
                let d'1 := AppliedOperator'_of_gen_tree symbol builtin gt1 in
                let d'2 := AppliedOperator'_of_gen_tree symbol builtin gt2 in
                match d'1, d'2 with
                | Some aps1, Some aps2 => Some (ao_app_ao aps1 aps2)
                | _, _ => None
                end
            | _ => None
            end
    | _ => None
    end
    .

    Lemma AppliedOperator'_of_to_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : AppliedOperator' symbol builtin)
        : AppliedOperator'_of_gen_tree symbol builtin (AppliedOperator'_to_gen_tree symbol builtin a) = Some a
    .
    Proof.
        induction a; simpl.
        { reflexivity. }
        {
            ltac1:(rewrite ! Pos2Nat.id decode_encode).
            rewrite decode_encode.
            rewrite IHa.
            reflexivity.
        }
        {
            rewrite IHa1.
            rewrite IHa2.
            reflexivity.
        }
    Qed.

    #[export]
    Instance appliedOperator_countable
        (symbol_set : Type)
        {symbols : Symbols symbol_set}
        (builtin_set : Type)
        {builtin_eqdec : EqDecision builtin_set}
        {builtin_countable : Countable builtin_set}
        : Countable (AppliedOperator' symbol_set builtin_set)
    .
    Proof.
        apply inj_countable
        with
            (f := AppliedOperator'_to_gen_tree symbol_set builtin_set)
            (g := AppliedOperator'_of_gen_tree symbol_set builtin_set)
        .
        intros x.
        apply AppliedOperator'_of_to_gen_tree.
    Qed.

    Definition GroundTerm'_to_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (e : GroundTerm' symbol builtin)
        : gen_tree (builtin + (AppliedOperator' symbol builtin))%type
    :=
    match e with
    | (aoo_operand b) => GenLeaf (inl _ b)
    | (aoo_app s) => GenLeaf (inr _ s)
    end
    .

    Definition GroundTerm'_from_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (t : gen_tree (builtin+(AppliedOperator' symbol builtin))%type)
        :  option (GroundTerm' symbol builtin)
    :=
    match t with
    | (GenLeaf (inl _ b)) => Some (aoo_operand b)
    | (GenLeaf (inr _ s)) => Some (aoo_app s)
    | _ => None
    end
    .

    Lemma GroundTerm'_to_from_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (e : GroundTerm' symbol builtin)
        : GroundTerm'_from_gen_tree symbol builtin (GroundTerm'_to_gen_tree symbol builtin e) = Some e
    .
    Proof.
        destruct e; reflexivity.
    Qed.

    #[export]
    Instance GroundTerm'_countable
        (symbol_set : Type)
        {symbols : Symbols symbol_set}
        (builtin_set : Type)
        {builtin_eqdec : EqDecision builtin_set}
        {builtin_countable : Countable builtin_set}
        : Countable (GroundTerm' symbol_set builtin_set)
    .
    Proof.
        apply inj_countable
        with
            (f := GroundTerm'_to_gen_tree symbol_set builtin_set)
            (g := GroundTerm'_from_gen_tree symbol_set builtin_set)
        .
        intros x.
        apply GroundTerm'_to_from_gen_tree.
    Defined.

End countable.
