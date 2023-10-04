From Minuska Require Import
    prelude
.

Inductive AppliedOperator' (operator : Set) (operand : Set) :=
| ao_operator (s : operator)
| ao_app_operand
    (aps : AppliedOperator' operator operand) (b : operand) 
| ao_app_ao
    (aps : AppliedOperator' operator operand)
    (x : AppliedOperator' operator operand)
.


Inductive AppliedOperatorOr'
    (Operator : Set)
    (Operand : Set)
    : Set :=
| aoo_app (ao : AppliedOperator' Operator Operand)
| aoo_operand (operand : Operand)
.


Definition GroundTerm' (symbol : Set) (builtin : Set)
    := (AppliedOperatorOr' symbol builtin)
.

Arguments ao_operator {operator operand}%type_scope s.
Arguments ao_app_operand {operator operand}%type_scope aps b.
Arguments ao_app_ao {operator operand}%type_scope aps x.

Class MVariables (variable : Set) := {
    variable_eqdec :: EqDecision variable ;
    variable_countable :: Countable variable ;
    variable_infinite :: Infinite variable ;
}.

Class Symbols (symbol : Set) := {
    symbol_eqdec :: EqDecision symbol ;
    symbol_countable :: Countable symbol ;
}.

Class Builtin {symbol : Set} {symbols : Symbols symbol} := {
    builtin_value
        : Set ;
    builtin_value_eqdec
        :: EqDecision builtin_value ;
    
    builtin_unary_predicate
        : Set ;
    builtin_unary_predicate_eqdec
        :: EqDecision builtin_unary_predicate ;
    
    builtin_binary_predicate
        : Set ;
    builtin_binary_predicate_eqdec
        :: EqDecision builtin_binary_predicate ;

    builtin_unary_function
        : Set ;
    builtin_unary_function_eqdec
        :: EqDecision builtin_unary_function ;

    builtin_binary_function
        : Set ;
    builtin_binary_function_eqdec
        :: EqDecision builtin_binary_function ;

    builtin_unary_predicate_interp
        : builtin_unary_predicate 
        -> (GroundTerm' symbol builtin_value)
        -> Prop ;

    builtin_binary_predicate_interp
        : builtin_binary_predicate 
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value)
        -> Prop ;
    
    builtin_unary_function_interp
        : builtin_unary_function
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value) ;

    builtin_binary_function_interp
        : builtin_binary_function
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value)
        -> (GroundTerm' symbol builtin_value) ;
}.

Class Signature := {
    symbol : Set ;
    variable : Set ;
    symbols :: Symbols symbol ;
    builtin :: Builtin ;
    variables :: MVariables variable ;
}.

Definition GroundTerm {Σ : Signature}
    := GroundTerm' symbol builtin_value
.

Inductive AtomicProposition {Σ : Signature} :=
| ap1 (p : builtin_unary_predicate) (x : variable)
| ap2 (p : builtin_binary_predicate) (x y : variable)
.

Inductive Constraint {Σ : Signature} :=
| c_True
| c_atomic (ap : AtomicProposition)
| c_and (c1 c2 : Constraint)
| c_not (c : Constraint)
.

Inductive BuiltinOrVar {Σ : Signature} :=
| bov_builtin (b : builtin_value)
| bov_variable (x : variable)
.

Definition OpenTerm {Σ : Signature}
    := AppliedOperatorOr' symbol BuiltinOrVar
.
(*
Inductive OpenTerm {Σ : Signature} :=
| ot_aop (aop : AppliedOperator' symbol BuiltinOrVar)
| ot_bov (bov : BuiltinOrVar)
.
*)

(* TODO make a plural *)
Inductive SideCondition {Σ : Signature} :=
| sc_constraint (c : Constraint)
| sc_match (v : variable) (φ : OpenTerm)
.

Inductive WithASideCondition {Σ : Signature} (Base : Set) :=
|  wsc_base (φ : Base)
|  wsc_sc (φc : WithASideCondition Base) (sc : SideCondition)
.

Arguments wsc_base {Σ} {Base}%type_scope φ.
Arguments wsc_sc {Σ} {Base}%type_scope φc sc.

Definition OpenTermWSC {Σ : Signature}
    := WithASideCondition (@OpenTerm Σ)
.

Definition LhsPattern {Σ : Signature} :=
    AppliedOperatorOr' symbol OpenTermWSC
.

Inductive Expression
    {Σ : Signature}
    :=
| ft_element (e : GroundTerm)
| ft_variable (x : variable)
| ft_unary (f : builtin_unary_function) (t : Expression)
| ft_binary (f : builtin_binary_function) (t1 : Expression) (t2 : Expression)
.

Definition RhsPattern {Σ : Signature} :=
    AppliedOperatorOr' symbol Expression
.

Record LocalRewrite {Σ : Signature} := {
    lr_from : LhsPattern ;
    lr_to : RhsPattern ;
}.

Inductive LocalRewriteOrOpenTermOrBOV {Σ : Signature} :=
| lp_rewrite (r : LocalRewrite)
| lp_basicpat (φ : OpenTerm)
| lp_bov (bx : BuiltinOrVar)
. 

Definition UncondRewritingRule {Σ : Signature}
    := AppliedOperator' symbol LocalRewriteOrOpenTermOrBOV
.

Definition RewritingRule {Σ : Signature}
    := WithASideCondition UncondRewritingRule
.

Inductive LeftRight : Set := LR_Left | LR_Right.

Equations Derive NoConfusion for AppliedOperator'.
Equations Derive NoConfusion for AtomicProposition.
Equations Derive NoConfusion for Constraint.
Equations Derive NoConfusion for Expression.
Equations Derive NoConfusion for WithASideCondition.
Equations Derive NoConfusion for LocalRewrite.

Section eqdec.

    #[export]
    Instance AppliedOperator'_eqdec
        {symbol : Set}
        {symbols : Symbols symbol}
        (builtin : Set)
        {builtin_dec : EqDecision builtin}
        : EqDecision (AppliedOperator' symbol builtin)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance GroundTerm'_eqdec
        {A : Set}
        {symbols : Symbols A}
        (T : Set)
        {T_dec : EqDecision T}
        : EqDecision (GroundTerm' A T)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance atomicProposition_eqdec {Σ : Signature}
        : EqDecision AtomicProposition
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance constraint_eqdec {Σ : Signature}
        : EqDecision Constraint
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance BuiltinOrVar_eqdec {Σ : Signature}
        : EqDecision BuiltinOrVar
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance GroundTerm_eqdec {Σ : Signature}
        : EqDecision GroundTerm
    .
    Proof.
        intros e1 e2.
        apply GroundTerm'_eqdec.
        apply builtin_value_eqdec.
    Defined.

    #[export]
    Instance Expression_eqdec {Σ : Signature}
        : EqDecision (Expression)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.


    #[export]
    Instance  OpenTerm_eqdec {Σ : Signature}
        : EqDecision OpenTerm
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance  SideCondition_eqdec {Σ : Signature}
        : EqDecision SideCondition
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance  OpenTermWSC_eqdec {Σ : Signature}
        : EqDecision OpenTermWSC
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance LhsPattern_eqdec {Σ : Signature}
        : EqDecision LhsPattern
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance RhsPattern_eqdec {Σ : Signature}
        : EqDecision RhsPattern
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance WithASideCondition_eqdec
        {Σ : Signature}
        (A : Set)
        (A_eqdec : EqDecision A)
        : EqDecision (WithASideCondition A)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance LocalRewrite_eqdec {Σ : Signature}
        : EqDecision LocalRewrite
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

End eqdec.

Section countable.

    Equations AppliedOperator'_to_gen_tree
        (symbol : Set)
        {symbols : Symbols symbol}
        (builtin : Set)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : AppliedOperator' symbol builtin)
        : gen_tree symbol
    :=
        AppliedOperator'_to_gen_tree _ _ (ao_operator s)
        := GenLeaf s ;

        AppliedOperator'_to_gen_tree _ _ (ao_app_operand aps b)
        := (
            let x := (encode (0, encode b)) in
            GenNode (Pos.to_nat x) ([AppliedOperator'_to_gen_tree symbol builtin aps;AppliedOperator'_to_gen_tree symbol builtin aps(* we duplicate it to make the reverse simpler*)])
        ) ;

        AppliedOperator'_to_gen_tree _ _ (ao_app_ao aps1 aps2)
        := (
            let xd := (1, encode 0) in
            let x := (encode xd) in
            GenNode (Pos.to_nat x) ([AppliedOperator'_to_gen_tree _ _ aps1; AppliedOperator'_to_gen_tree _ _ aps2])
        )
    .
    Opaque AppliedOperator'_to_gen_tree.

    Equations AppliedOperator'_of_gen_tree
        (symbol : Set)
        {symbols : Symbols symbol}
        (builtin : Set)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (t : gen_tree symbol)
        : option (AppliedOperator' symbol builtin)
    :=
        AppliedOperator'_of_gen_tree _ _ (GenLeaf s)
        := Some (ao_operator s);
        
        AppliedOperator'_of_gen_tree _ _ (GenNode n [gt1;gt2])
        with (@decode (nat*positive) _ _ (Pos.of_nat n)) => {
            | Some (0, pb) with (@decode builtin _ _ pb) => {
                | Some b with (AppliedOperator'_of_gen_tree symbol builtin gt1) => {
                    | Some as1 := Some (ao_app_operand as1 b)
                    | _ := None
                }
                | _ := None
            }
            | Some (1, _) with AppliedOperator'_of_gen_tree symbol builtin gt1, AppliedOperator'_of_gen_tree symbol builtin gt2 => {
                | Some aps1, Some aps2 := Some (ao_app_ao aps1 aps2)
                | _, _ := None
            }
            | _ := None
        };
        AppliedOperator'_of_gen_tree _ _ _
        := None
    .
    Opaque AppliedOperator'_of_gen_tree.

    Lemma AppliedOperator'_of_to_gen_tree
        (symbol : Set)
        {symbols : Symbols symbol}
        (builtin : Set)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : AppliedOperator' symbol builtin)
        : AppliedOperator'_of_gen_tree symbol builtin (AppliedOperator'_to_gen_tree symbol builtin a) = Some a
    .
    Proof.
        ltac1:(funelim (AppliedOperator'_to_gen_tree symbol builtin a)).
        {
            ltac1:(simp AppliedOperator'_to_gen_tree).
            ltac1:(simp AppliedOperator'_of_gen_tree).
            reflexivity.
        }
        {
            ltac1:(simp AppliedOperator'_to_gen_tree).
            ltac1:(simp AppliedOperator'_of_gen_tree).
            ltac1:(rewrite ! Pos2Nat.id decode_encode).
            unfold AppliedOperator'_of_gen_tree_clause_2.
            unfold AppliedOperator'_of_gen_tree_clause_2_clause_1.
            rewrite decode_encode.
            ltac1:(rewrite H).
            unfold AppliedOperator'_of_gen_tree_clause_2_clause_1_clause_1.
            reflexivity.
        }
        {
            ltac1:(simp AppliedOperator'_to_gen_tree).
            ltac1:(simp AppliedOperator'_of_gen_tree).
            ltac1:(rewrite ! Pos2Nat.id decode_encode).
            unfold AppliedOperator'_of_gen_tree_clause_2.
            unfold AppliedOperator'_of_gen_tree_clause_2_clause_2.
            unfold AppliedOperator'_of_gen_tree_clause_2_clause_2_clause_1.
            ltac1:(rewrite H).
            ltac1:(rewrite H0).
            reflexivity.
        }
    Qed.

    #[export]
    Instance appliedOperator_countable
        (symbol_set : Set)
        {symbols : Symbols symbol_set}
        (builtin_set : Set)
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

    Equations GroundTerm'_to_gen_tree
        (symbol : Set)
        {symbols : Symbols symbol}
        (builtin : Set)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (e : GroundTerm' symbol builtin)
        : gen_tree (builtin + (AppliedOperator' symbol builtin))%type
    :=
        GroundTerm'_to_gen_tree _ _ (aoo_operand _ _ b)
        := GenLeaf (inl _ b) ;
        
        GroundTerm'_to_gen_tree _ _ (aoo_app _ _ s)
        := GenLeaf (inr _ s)
    .

    Opaque GroundTerm'_to_gen_tree.

    Equations GroundTerm'_from_gen_tree
        (symbol : Set)
        {symbols : Symbols symbol}
        (builtin : Set)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (t : gen_tree (builtin+(AppliedOperator' symbol builtin))%type)
        :  option (GroundTerm' symbol builtin)
    :=
        GroundTerm'_from_gen_tree _ _ (GenLeaf (inl _ b))
        := Some (aoo_operand _ _ b);
        
        GroundTerm'_from_gen_tree _ _ (GenLeaf (inr _ s))
        := Some (aoo_app _ _ s);
        
        GroundTerm'_from_gen_tree _ _ _
        := None
    .
    Opaque GroundTerm'_from_gen_tree.

    Lemma GroundTerm'_to_from_gen_tree
        (symbol : Set)
        {symbols : Symbols symbol}
        (builtin : Set)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (e : GroundTerm' symbol builtin)
        : GroundTerm'_from_gen_tree symbol builtin (GroundTerm'_to_gen_tree symbol builtin e) = Some e
    .
    Proof.
        ltac1:(funelim (GroundTerm'_to_gen_tree symbol builtin e)).
        { reflexivity. }
        { reflexivity. }
    Qed.

    #[export]
    Instance GroundTerm'_countable
        (symbol_set : Set)
        {symbols : Symbols symbol_set}
        (builtin_set : Set)
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
    Qed.

End countable.