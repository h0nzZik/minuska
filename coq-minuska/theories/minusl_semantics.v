From Minuska Require Import
    prelude
    spec
    basic_properties
    minusl_syntax
    spec
    properties
.

Section MinusL_sem.
    Context
        {Σ : StaticModel}
        (Label : Set)
    .

    Inductive MinusL_rewrites
        (D : MinusL_LangDef Label)
        (program : ProgramT)
        :
        (TermOver builtin_value) ->
        (TermOver builtin_value) ->
        (list Label)  ->
        (TermOver builtin_value) ->
        (TermOver builtin_value) ->
        Type :=

    | mlr_refl :
        forall ctrl state,
            MinusL_rewrites D program ctrl state [] ctrl state

    | mlr_rule : 
        forall
            (lc : TermOver BuiltinOrVar) (ld : TermOver BuiltinOrVar)
            (a : Label)
            (rc : TermOver Expression2) (rd : TermOver Expression2)
            (c : SideCondition),
            (mld_rewrite Label lc ld a rc rd c) ∈ (mlld_decls Label D) ->
        forall (ctrl1 state1 ctrl2 state2 : TermOver builtin_value) (nv : NondetValue)
            (ρ : Valuation2),
            satisfies ρ ctrl1 lc ->
            satisfies ρ state1 ld ->
            satisfies ρ (program, (nv,ctrl2)) rc ->
            satisfies ρ (program, (nv,state2)) rd ->
            satisfies ρ (program, nv) c ->
        MinusL_rewrites D program ctrl1 state1 [a] ctrl2 state2

    | mlr_trans :
        forall
            (ctrl1 state1 ctrl2 state2 ctrl3 state3 : TermOver builtin_value)
            (w1 w2 : list Label),
        MinusL_rewrites D program ctrl1 state1 w1 ctrl2 state2 ->
        MinusL_rewrites D program ctrl2 state2 w2 ctrl3 state3 ->
        MinusL_rewrites D program ctrl1 state1 (w1 ++ w2) ctrl3 state3

    | mlr_context :
        forall
            (ctx : TermOver BuiltinOrVar)
            (h : variable)
            (c : SideCondition),
            (mld_context Label ctx h c) ∈ (mlld_decls Label D) ->
        forall (ctrl1 state1 ctrl2 state2 r v : TermOver builtin_value)
            (w : list Label)
            (ρ1 : Valuation2)
            (ρ2 : Valuation2)
            (nv : NondetValue),
            (∀ x, x ∈ vars_of ctx -> x <> h -> ρ1 !! x = ρ2 !! x) ->
            satisfies (<[h := r]>ρ1) ctrl1 ctx ->
            satisfies ρ1 (program, nv) c ->
            satisfies (<[h := v]>ρ2) ctrl2 ctx ->
            satisfies ρ2 (program, nv) (MinusL_isValue Label D (e_ground v)) ->
            MinusL_rewrites D program r state1 w v state2 ->
            MinusL_rewrites D program ctrl1 state1 w ctrl2 state2
    .

End MinusL_sem.