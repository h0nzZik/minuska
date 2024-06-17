From Minuska Require Import
    prelude
    spec
    properties
    minusl_syntax
    syntax_properties
    unification_interface
.


Require Import Wellfounded.
From stdpp Require Import lexico well_founded.

Require Import Program.
From Coq Require Import Logic.Eqdep_dec.

From Equations Require Export Equations.

(*
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Sample (choose(0, 10)).*)


Definition Satisfies_variable_GroundTerm'
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (x : variable)
    := ρ !! x = Some t
.

#[export]
Instance Satisfies_variable_GroundTerm
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        variable
        variable
:= {|
    satisfies :=
        fun
            (ρ : Valuation2)
            (t : TermOver builtin_value)
            (x : variable) => Satisfies_variable_GroundTerm' ρ t x
|}.


Equations? sat2v
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver variable)
    : Prop
    by wf (TermOver_size φ) lt
:=
    sat2v ρ t (t_over x) := Satisfies_variable_GroundTerm' ρ t x ;
    sat2v ρ (t_over _) (t_term s l) := False ;
    sat2v ρ (t_term s' l') (t_term s l) :=
        ((s' = s) /\
        (length l' = length l) /\
        forall i t' φ' (pf1 : l !! i = Some φ') (pf2 : l' !! i = Some t'),
            sat2v ρ t' φ'
        )
    ;
.
Proof.
    abstract(
    unfold satisfies in *; simpl in *;
    simpl;
    apply take_drop_middle in pf1;
    rewrite <- pf1;
    rewrite sum_list_with_app; simpl;
    ltac1:(lia)).
Defined.

#[export]
Instance Satisfies_TOV_GroundTerm
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        (TermOver variable)
        variable
:= {|
    satisfies := fun ρ g φ => sat2v ρ g φ
|}.

Record SymCfg {Σ : StaticModel} := {
    scfg_pattern : TermOver variable ;
    scfg_side_conditions : list SideCondition2 ;
}.

Definition Satisfies_SymCfg_GroundTerm'
    {Σ : StaticModel}
    (ρ : Valuation2)
    (g : TermOver builtin_value)
    (scfg : SymCfg)
:=
    ((satisfies ρ g scfg.(scfg_pattern))
    * (satisfies ρ tt scfg.(scfg_side_conditions)))%type
.

#[export]
Instance Satisfies_SymCfg_GroundTerm
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        (SymCfg)
        variable
:= {|
    satisfies := fun ρ g φ => Satisfies_SymCfg_GroundTerm' ρ g φ
|}.

Definition Satisfies_listSymCfg_GroundTerm'
    {Σ : StaticModel}
    (ρ : Valuation2)
    (g : TermOver builtin_value)
    (lφ : list SymCfg)
:=
    forall φ, φ ∈ lφ -> satisfies ρ g φ
.

#[export]
Instance Satisfies_listSymCfg_GroundTerm
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        (list SymCfg)
        variable
:= {|
    satisfies := Satisfies_listSymCfg_GroundTerm'
|}.

Definition SymexStep {Σ : StaticModel}
:=
    list SymCfg -> list SymCfg
.

Definition refines {Σ : StaticModel} (g : TermOver builtin_value) (φ : list SymCfg)
:= { ρ : Valuation2 & satisfies ρ g φ}.

Definition SymexStep_sound
    {Σ : StaticModel}
    (Act : Set)
    (Γ : RewritingTheory2 Act)
    (step : SymexStep)
:=
    ∀ (φ : list SymCfg) (g g' : TermOver builtin_value),
        refines g φ ->
        refines  g' (step φ) ->
        rewriting_relation Γ g g'
.

Definition SymexStep_complete
    {Σ : StaticModel}
    (Act : Set)
    (Γ : RewritingTheory2 Act)
    (step : SymexStep)
:=
    ∀ (φ : list SymCfg) (g g' : TermOver builtin_value),
        rewriting_relation Γ g g' ->
        refines g φ ->
        refines  g' (step φ)
.


