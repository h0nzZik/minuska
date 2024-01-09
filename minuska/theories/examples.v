From Coq.Logic Require Import ProofIrrelevance.

Require Extraction.
Extraction Language OCaml.

From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    empty_builtin
    flattened
    naive_interpreter
.

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))"
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
    (*
        fr_from := aoo_app _ _  (ao_app_ao (ao_operator "s") ((ao_app_operand (ao_operator "s") (bov_variable "X"))));
        fr_to := aoo_operand _ _  (ft_variable "X");
    *)
        fr_from := aoo_app _ _ 
            (ao_app_ao (ao_operator "top")
                (ao_app_ao
                    (ao_operator "s")
                    ((ao_app_operand (ao_operator "s") (bov_variable "X")))
                )
            );
        fr_to := aoo_app symbol Expression  (
            ao_app_operand
                (ao_operator "top")
                (ft_variable "X")
        );
        fr_scs := [] ;
    |}.

    Definition Γ : FlattenedRewritingTheory := [rule_1].

    Definition interp :=
        naive_interpreter Γ
    .

    Fixpoint interp_loop
        (fuel : nat)
        (g : GroundTerm)
        : option GroundTerm
    :=
    match fuel with
    | 0 => Some g
    | S fuel' => g' ← interp g; interp_loop fuel' g'
    end
    .

    Fixpoint my_number' (n : nat) : AppliedOperator' symbol builtin_value  :=
    match n with
    | 0 => ao_operator "0"
    | S n' => ao_app_ao (ao_operator "s") (my_number' n')
    end
    .

    Fixpoint my_number'_inv
        (g : AppliedOperator' symbol builtin_value)
        : option nat
    :=
    match g with
    | ao_operator s => if bool_decide (s = "0") then Some 0 else None
    | ao_app_ao s arg =>
        match s with
        | ao_operator s => if bool_decide (s = "s") then
            n ← my_number'_inv arg;
            Some (S n)
        else None
        | _ => None
        end
    | ao_app_operand _ _ => None
    end
    .

    Definition my_number (n : nat) : GroundTerm :=
        aoo_app _ _ (ao_app_ao (ao_operator "top") (my_number' n))
    .

    Definition my_number_inv (g : GroundTerm) : option nat
    :=
    match g with
    | aoo_app _ _ (ao_app_ao (ao_operator "top") g') => my_number'_inv g'
    | _ => None
    end
    .

    Lemma my_number_inversion' : forall n,
        my_number'_inv (my_number' n) = Some n
    .
    Proof.
        induction n; simpl.
        { reflexivity. }
        {
            rewrite bind_Some.
            exists n.
            auto.
        }
    Qed.

    Lemma my_number_inversion : forall n,
        my_number_inv (my_number n) = Some n
    .
    Proof.
        intros n. simpl. apply my_number_inversion'.
    Qed.

    Compute (my_number 2).
    Compute (interp (my_number 2)).

    Definition interp_loop_number fuel := 
        fun n =>
        let og' := ((interp_loop fuel) ∘ my_number) n in
        g' ← og';
        my_number_inv g'
    .

    Extraction "ExampleLang.ml" interp_loop_number.

End example_1.