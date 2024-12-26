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
        (Act : Set)
    .

    Inductive MinusL_rewrites
        (D : MinusL_LangDef Act)
        (program : ProgramT)
        :
        (TermOver builtin_value) ->
        (TermOver builtin_value) ->
        (list Act)  ->
        (TermOver builtin_value) ->
        (TermOver builtin_value) ->
        Type :=

    | mlr_refl :
        forall ctrl state,
            MinusL_rewrites D program ctrl state [] ctrl state

    | mlr_rule : 
        forall
            (lc : TermOver BuiltinOrVar) (ld : TermOver BuiltinOrVar)
            (a : Act)
            (rc : TermOver Expression2) (rd : TermOver Expression2)
            (scs : list SideCondition2),
            (mld_rewrite Act lc ld a rc rd scs) ∈ (mlld_decls Act D) ->
        forall (ctrl1 state1 ctrl2 state2 : TermOver builtin_value) (nv : NondetValue)
            (ρ : Valuation2),
            satisfies ρ ctrl1 lc ->
            satisfies ρ state1 ld ->
            satisfies ρ (program, (nv,ctrl2)) rc ->
            satisfies ρ (program, (nv,state2)) rd ->
            satisfies ρ (program, nv) scs ->
        MinusL_rewrites D program ctrl1 state1 [a] ctrl2 state2

    | mlr_trans :
        forall
            (ctrl1 state1 ctrl2 state2 ctrl3 state3 : TermOver builtin_value)
            (w1 w2 : list Act),
        MinusL_rewrites D program ctrl1 state1 w1 ctrl2 state2 ->
        MinusL_rewrites D program ctrl2 state2 w2 ctrl3 state3 ->
        MinusL_rewrites D program ctrl1 state1 (w1 ++ w2) ctrl3 state3

    | mlr_context :
        forall
            (c : TermOver BuiltinOrVar)
            (h : variable)
            (scs : list SideCondition2),
            (mld_context Act c h scs) ∈ (mlld_decls Act D) ->
        forall (ctrl1 state1 ctrl2 state2 r v : TermOver builtin_value)
            (w : list Act)
            (ρ1 : Valuation2)
            (ρ2 : Valuation2)
            (nv : NondetValue),
            (∀ x, x ∈ vars_of_to_l2r c -> x <> h -> ρ1 !! x = ρ2 !! x) ->
            satisfies (<[h := r]>ρ1) ctrl1 c ->
            satisfies ρ1 (program, nv) scs ->
            satisfies (<[h := v]>ρ2) ctrl2 c ->
            satisfies ρ2 (program, nv) (MinusL_isValue Act D (e_ground v)) ->
            MinusL_rewrites D program r state1 w v state2 ->
            MinusL_rewrites D program ctrl1 state1 w ctrl2 state2
    .

End MinusL_sem.