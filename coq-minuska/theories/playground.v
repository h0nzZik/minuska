From Minuska Require Import
    prelude
    spec
    basic_properties
    quickchick_setup
    (* symex *)
    substitution_parallel
.

Definition genSubstitutionSized (sz : nat) : G (gmap variable (TermOver BuiltinOrVar)) :=
    bindGen (
        listOf (
            bindGen genVariable (fun x =>
                bindGen (genPatternSized sz) (fun g =>
                    returnGen (x, g)
                )
            )
        )
    ) (fun l => returnGen (list_to_map l))
.

#[local]
Instance subp_eqdec : EqDecision SubP.
Proof.
    apply _.
Defined.

Sample (genSubstitutionSized 3).

QuickChick (forAll (genSubstitutionSized 3)(fun a =>
    forAll (genSubstitutionSized 3)(fun b =>
        forAll (genSubstitutionSized 3)(fun c =>
            bool_decide (subp_compose (subp_compose a b) c = subp_compose a (subp_compose b c))
        )
    )
)).

(* 
(* Sample (genValuationSized 1). *)
(* Search bool. *)
Definition replace_and_collect_property_1
    (program : ProgramT)
    (g : TermOver builtin_value)
    (et : TermOver Expression2)
    (ρ : Valuation2)
    (nv : NondetValue)
    : bool
:=
    implb
        (sat2Eb program ρ g et nv)
        (sat2Bb ρ g (replace_and_collect et).1)
.

(* Set Printing Universes. *)
(* Set Debug "backtrace". *)
Definition myP1 := forAll
        (genTermOverExprSized 3)
        (
            fun et =>
            forAll
                (genTermSized 3)
                (
                    fun g =>
                    forAll
                        (genValuationSized 3)
                        (fun rho => replace_and_collect_property_1 (t_over (inl false)) g et rho mytt)
                )
        ).

QuickChick (
    myP1
).
(* Of course it does not work. The property is too strong.
    In general, the replace_and_collect does not preserve satisfaction
    but only satisfiability.
 *)
Compute (replace_and_collect (t_over (e_fun int_one []))).
Compute (sat2Bb ∅ (t_over (inr 1%Z)) (replace_and_collect (t_over (e_fun int_one []))).1).

Definition replace_and_collect_property_2
    (program : ProgramT)
    (g : TermOver builtin_value)
    (et : TermOver Expression2)
    (ρ : Valuation2)
    (nv : NondetValue)
    : bool
:=
    implb
        (sat2Bb ρ g (replace_and_collect et).1)
        (sat2Eb program ρ g et nv)
.



Definition myP2 := forAll
        (genTermOverExprSized 3)
        (
            fun et =>
            forAll
                (genTermSized 3)
                (
                    fun g =>
                    forAll
                        (genValuationSized 3)
                        (fun rho => replace_and_collect_property_2 (t_over (inl false)) g et rho mytt)
                )
        ).
(* Print MyUnit. *)
QuickChick (
    myP2
).
replace_and_collect *)
