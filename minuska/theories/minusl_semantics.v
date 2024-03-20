From Minuska Require Import
    prelude
    spec_syntax
    minusl_syntax
    spec_semantics
.


Section MinusL_sem.
    Context
        {Σ : StaticModel}
        (Act : Set)
    .

    Inductive MinusL_rewrites
        (D : MinusL_LangDef Act)
        :
        (TermOver builtin_value) ->
        (TermOver builtin_value) ->
        (list Act)  ->
        (TermOver builtin_value) ->
        (TermOver builtin_value) ->
        Type :=

    | mlr_refl :
        forall ctrl state,
            MinusL_rewrites D ctrl state [] ctrl state

    | mlr_rule : 
        forall
            (lc : TermOver BuiltinOrVar) (ld : TermOver BuiltinOrVar)
            (a : Act)
            (rc : TermOver Expression) (rd : TermOver Expression)
            (scs : list SideCondition),
            (mld_rewrite Act lc ld a rc rd scs) ∈ (mlld_decls Act D) ->
        forall (ctrl1 state1 ctrl2 state2 : TermOver builtin_value)
            (ρ : Valuation),
            satisfies ρ ctrl1 lc ->
            satisfies ρ state1 ld ->
            satisfies ρ ctrl2 rc ->
            satisfies ρ state2 rd ->
            satisfies ρ () scs ->
        MinusL_rewrites D ctrl1 state1 [a] ctrl2 state2

    | mlr_trans :
        forall
            (ctrl1 state1 ctrl2 state2 ctrl3 state3 : TermOver builtin_value)
            (w1 w2 : list Act),
        MinusL_rewrites D ctrl1 state1 w1 ctrl2 state2 ->
        MinusL_rewrites D ctrl2 state2 w2 ctrl3 state3 ->
        MinusL_rewrites D ctrl1 state1 (w1 ++ w2) ctrl3 state3

    | mlr_context :
        forall
            (c : TermOver BuiltinOrVar)
            (h : variable)
            (Hh : length (filter (eq h) (vars_of_to_l2r c)) = 1)
            (scs : list SideCondition)
            (Hhscs : h ∉ vars_of scs),
            (mld_context Act c h Hh scs Hhscs) ∈ (mlld_decls Act D) ->
        forall (ctrl1 state1 ctrl2 state2 r v : TermOver builtin_value)
            (w : list Act)
            (ρ1 : Valuation)
            (ρ2 : Valuation),
            (∀ x, x ∈ vars_of_to_l2r c -> x <> h -> ρ1 !! x = ρ2 !! x) ->
            satisfies (<[h := uglify' r]>ρ1) ctrl1 c ->
            satisfies ρ1 () scs ->
            satisfies (<[h := uglify' v]>ρ2) ctrl2 c ->
            satisfies ρ2 () (MinusL_isValue Act D (ft_element (uglify' v))) ->
            MinusL_rewrites D r state1 w v state2 ->
            MinusL_rewrites D ctrl1 state1 w ctrl2 state2
    .

End MinusL_sem.