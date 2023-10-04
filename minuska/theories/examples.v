From Coq.Logic Require Import ProofIrrelevance.

From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    empty_builtin
.


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

    Definition left_SSX := (lp_otwsc
                        (wsc_base
                            (ao_app_ao
                                (ao_operator "Succ")
                                (ao_app_operand
                                    (ao_operator "Succ")
                                    (bov_variable "X")
                                )
                            )
                        )
                    )
    .

    Definition right_X := (rp_exp 
                        (ft_variable "X")
                    ).

    Definition rule_sub_2 : RewritingRule :=
        wsc_base (
            ao_app_operand 
                (ao_operator "TopCell")
                (lp_rewrite
                    (lr_pattern
                        left_SSX
                        right_X
                    )
                )
        )
    .

    Lemma rewrites_3_to_1:
        rewrites_to rule_sub_2
        (ao_app_ao
            (ao_operator "TopCell")
                (ao_app_ao
                    (ao_operator "Succ")
                    (ao_app_ao
                        (ao_operator "Succ")
                        (ao_app_ao
                            (ao_operator "Succ")
                            (ao_operator "Zero")
                        )
                    )
                )
        )
        (ao_app_ao
            (ao_operator "TopCell")
            (ao_app_ao
                (ao_operator "Succ")
                (ao_operator "Zero")
            )
        )
    .
    Proof.
        unfold rewrites_to.
        unfold rule_sub_2.
        exists ({[
            "X" := (val_gterm (ao_app_ao (ao_operator "Succ") (ao_operator "Zero")))
        ]}).
        unfold rewrites_in_valuation_to.
        repeat constructor.
    Qed.

End example_1.