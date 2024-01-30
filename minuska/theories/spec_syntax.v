From stdpp Require Import finite.

From Minuska Require Import
    prelude
.

#[universes(polymorphic=yes, cumulative=yes)]
Inductive PreTerm' (operator : Type) (operand : Type)
: Type
:=
| pt_operator (s : operator)
| pt_app_operand
    (aps : PreTerm' operator operand)
    (b : operand) 
| pt_app_ao
    (aps : PreTerm' operator operand)
    (x : PreTerm' operator operand)
.


#[universes(polymorphic=yes, cumulative=yes)]
Variant Term'
    (Operator : Type)
    (Operand : Type)
    : Type :=
| term_preterm (ao : PreTerm' Operator Operand)
| term_operand (operand : Operand)
.


Arguments term_operand {Operator Operand}%type_scope operand.
Arguments term_preterm {Operator Operand}%type_scope ao.


Polymorphic
Definition GroundTerm' (symbol : Type) (builtin : Type)
    := (Term' symbol builtin)
.

Arguments pt_operator {operator operand}%type_scope s.
Arguments pt_app_operand {operator operand}%type_scope aps b.
Arguments pt_app_ao {operator operand}%type_scope aps x.

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
    := Term' symbol BuiltinOrVar
.

Inductive SideCondition {Σ : StaticModel} :=
| sc_constraint (c : AtomicProposition)
.

Definition RhsPattern {Σ : StaticModel} :=
    Term' symbol Expression
.


Inductive LeftRight : Set := LR_Left | LR_Right.

Record RewritingRule {Σ : StaticModel}
:= mkRewritingRule
{
    fr_from : OpenTerm ;
    fr_to : RhsPattern ;
    fr_scs : list SideCondition ;
}.

Definition RewritingTheory {Σ : StaticModel}
    := list RewritingRule
.
