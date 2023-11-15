From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
.



Definition valuation_satisfies_scs
    {Σ : Signature}
    (ρ : Valuation)
    (scs : list SideCondition)
    : Prop
:= Forall (valuation_satisfies_sc ρ) scs
.

Record FlattenedRewritingRule {Σ : Signature} := {
    fr_from : OpenTerm ;
    fr_to : RhsPattern ;
    fr_scs : list SideCondition ;
}.

Definition flattened_rewrites_in_valuation_to
    {Σ : Signature}
    (ρ : Valuation)
    (r : FlattenedRewritingRule)
    (from to : GroundTerm)
    : Prop
:= in_val_GroundTerm_satisfies_OpenTerm
    ρ from (fr_from r)
/\ GroundTerm_satisfies_RhsPattern
    ρ to (fr_to r)
/\ valuation_satisfies_scs ρ (fr_scs r)
.

Definition flattened_rewrites_to
    {Σ : Signature}
    (r : FlattenedRewritingRule)
    (from to : GroundTerm)
    : Prop
:= exists ρ, flattened_rewrites_in_valuation_to ρ r from to
.

Definition FRR_wf
    {Σ : Signature}
    (r : FlattenedRewritingRule)
    : Prop
:=
    vars_of_RhsPattern (fr_to r) ⊆ vars_of_OpenTerm (fr_from r)
    (* TODO: add a requirement saying that all variables that occur on the lhs
       of some constraint, and specifically a pattern matching constraint,
       are reachable from the set of variables occuring in `fr_from r`
       in the graph induced by the list of pattern matching goals
    *)
.