From Coq.Logic Require Import ProofIrrelevance.

Require Extraction.

From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    empty_builtin
    flattened
    naive_interpreter
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


    Program Instance CΣ : @ComputableSignature Σ := {|
        builtin_unary_predicate_interp_bool := fun _ _ => false ;
        builtin_binary_predicate_interp_bool := fun _ _ _ => false ;
    |}.
    Next Obligation.
        destruct p.
    Qed.
    Next Obligation.
        destruct p.
    Qed.
    Fail Next Obligation.

    (*
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

    *)

    Print GroundTerm.
    Print BuiltinOrVar.
    Print OpenTerm.
    Print AppliedOperatorOr'.
    Print AppliedOperator'.
    Print RhsPattern.
    Print Expression.

    Definition rule_1 : FlattenedRewritingRule := {|
        fr_from := aoo_app _ _  (ao_app_ao (ao_operator "s") ((ao_app_operand (ao_operator "s") (bov_variable "X"))));
        fr_to := aoo_operand _ _  (ft_variable "X");
        fr_scs := [] ;
    |}.

    Definition Γ : FlattenedRewritingTheory := [rule_1].

    Definition interp :=
        naive_interpreter Γ
    .

    Fixpoint my_number' (n : nat) : AppliedOperator' symbol builtin_value  :=
    match n with
    | 0 => ao_operator "0"
    | S n' => ao_app_ao (ao_operator "s") (my_number' n')
    end
    .

    Definition my_number (n : nat) : GroundTerm :=
        aoo_app _ _ (my_number' n)
    .


    Compute (my_number 2).
    Compute (interp (my_number 2)).

    Extraction "example_lang" interp.

End example_1.