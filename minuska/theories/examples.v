From Coq.Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable decidable finite list list_numbers gmap strings.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
Set Equations Transparent.

Require Import Wellfounded.
From Ltac2 Require Import Ltac2.

From Minuska Require Import minuska string_variables empty_builtin.


Module example_1.

    #[local]
    Instance MySymbols : Symbols string := Build_Symbols _ _ _.

    #[local]
    Program Instance Σ : Signature := {|
        symbol := string ;
        variable := string ;
        symbols :=  MySymbols;
        variables := StringVariables ;
    |}.
    Next Obligation.
        apply EmptyBuiltin.
    Defined.

    Definition rule_sub_2 : RewritingRule :=
        rr_local_rewrite {|
            lr_from
                := pat_app
                    (pat_sym "Succ")
                    (pat_app 
                        (pat_sym "Succ")
                        (pat_var "X")
                    );
            lr_to := spat_var "X" ;
        |}
    .

    Definition weird_binary_succ : Element :=
        el_appsym (aps_app_aps (aps_app_aps (aps_operator "Succ") (aps_operator "Zero")) (aps_operator "Zero"))
    .

    Lemma rewrites_3_to_1:
        rewrites_to rule_sub_2
            (el_appsym
                (aps_app_aps
                    (aps_operator "Succ")
                    (aps_app_aps
                        (aps_operator "Succ")
                        (aps_app_aps
                            (aps_operator "Succ")
                            (aps_operator "Zero")
                        )
                    )
                )
            )
            (el_appsym
                (aps_app_aps
                    (aps_operator "Succ")
                    (aps_operator "Zero")
                )
            )
    .
    Proof.
        unfold rewrites_to.
        unfold rule_sub_2.
        exists ({[
            "X" := (el_appsym (aps_app_aps (aps_operator "Succ") (aps_operator "Zero")))
        ]}).
        Print rewrites_in_valuation_to.
        unfold rewrites_in_valuation_to.
        repeat split.
    Qed.

End example_1.