From Coq Require Import Setoid.

From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    flattened
    flatten
    basic_matching
.


Definition apply_match
    {Σ : StaticModel}
    {CΣ : ComputableBuiltins}
    (ρ : Valuation)
    (m : Match)
    : option Valuation
:=
    t ← ρ !! (m_variable m);
    ρ' ← try_match t (m_term m);
    merge_valuations ρ ρ'
.

Definition apply_match'
    {Σ : StaticModel}
    {CΣ : ComputableBuiltins}
    (oρ : option Valuation)
    (m : Match)
    : option Valuation
:=
    ρ ← oρ;
    apply_match ρ m
.

Definition reduce_matches
    {Σ : StaticModel}
    {CΣ : ComputableBuiltins}
    (oρ : option Valuation)
    (matches : list Match)
    : option Valuation
:=
    fold_left apply_match' matches oρ
.

Theorem on_a_good_reordering
    {Σ : StaticModel}
    :
    ∀(l0 : list Match) (initial_vars : gset variable),
    (∃ ρ0 : Valuation,
        valuation_satisfies_all_matches ρ0 l0
    ) ->
    ∃ (l : list Match),
        l ≡ₚ l0 /\
        ∀ (ρ : Valuation), initial_vars ⊆ dom ρ ->
        ∃ (ρ' : Valuation),
            reduce_matches (Some ρ) l = Some ρ' /\
            map_subseteq ρ ρ' /\
            valuation_satisfies_all_matches ρ' l0
.
Proof.
    intros l0 initial_vars [ρ0 Hρ0].
    exists ((order_enabled_first initial_vars l0).1 ++ (order_enabled_first initial_vars l0).2).
    split.
    {
        apply order_enabled_first_perm.
    }

    intros ρ Hρinit.
    ltac1:(cut(
        forall (ll : list Match),
            nicely_ordered initial_vars ll ->
            l0 ≡ₚ ll ->
            ∃ (ρρ' : Valuation),
                reduce_matches (Some ρ) ll = Some ρρ' /\
                map_subseteq ρ ρρ' /\
                valuation_satisfies_all_matches ρρ' ll
    )).
    {
        intros H.
        specialize (H ((order_enabled_first initial_vars l0).1 ++ (order_enabled_first initial_vars l0).2)).
        ltac1:(ospecialize (H _ _)).
        {
            apply order_enabled_first_nicely_ordered.
            exists ((order_enabled_first initial_vars l0).1 ++ (order_enabled_first initial_vars l0).2).
            split.
            {
                apply order_enabled_first_perm.
            }
        }
        {

        }
    }
    {
        intros H.
    }


    intros ρ Hinit.
    revert ρ0 Hρ0 ρ Hinit.
    induction l0.
    {
        intros ρ0 Hρ0 ρ Hinit.
        simpl.
        rewrite order_enabled_first_nil.
        simpl.
        exists ρ.
        split.
        {
            reflexivity.
        }
        split.
        {
            apply map_subseteq_po.
        }
        unfold valuation_satisfies_all_matches.
        intros x ot H.
        rewrite elem_of_nil in H.
        inversion H.
    }
    {
        intros ρ0 Hρ0.
        ltac1:(ospecialize (IHl0 ρ0 _)).
        {
            clear -Hρ0.
            unfold valuation_satisfies_all_matches in *.
            intros x ot Hxot.
            ltac1:(ospecialize (Hρ0 x ot _)).
            {
                clear -Hxot.
                ltac1:(set_solver).
            }
            apply Hρ0.
        }
    }
Abort.


