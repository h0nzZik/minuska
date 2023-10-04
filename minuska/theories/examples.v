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

    Definition left_SSX : LhsPattern :=
        (aoo_operand _ _
            (wsc_base
                (aoo_app _ _ 
                    (ao_app_ao
                        (ao_operator "Succ")
                        (ao_app_operand
                            (ao_operator "Succ")
                            (bov_variable "X")
                        )
                    )
                )
            )
        )
    .

    Definition right_X : RhsPattern :=
        (aoo_operand _ _ 
            (ft_variable "X")
        )
    .

    Definition rule_sub_2 : RewritingRule :=
        wsc_base
            (aoo_operand _ _
                (
                    (lp_rewrite
                        {|
                            lr_from := left_SSX;
                            lr_to :=right_X;
                        |}
                    )
                )
            )
    .

    Notation "φ1 => φ2" := (Build_LocalRewrite _ φ1 φ2) (at level 90).

    Print GroundTerm'.
    Lemma rewrites_3_to_1:
        rewrites_to rule_sub_2
        (aoo_app _ _
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
        (aoo_app _ _
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
            "X" := (aoo_app _ _ (ao_app_ao (ao_operator "Succ") (ao_operator "Zero")))
        ]}).
        unfold rewrites_in_valuation_to.
        unfold GroundTerm_satisfies_RewritingRule.
        unfold GroundTerm_satisfies_UncondRewritingRule.
        unfold left_SSX, right_X.
        repeat constructor.
    Qed.

End example_1.