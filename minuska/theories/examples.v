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
    Program Instance MySymbols : Symbols := {|
        symbol := string ;
    |}.

    #[local]
    Instance Σ : Signature := {|
        builtin := EmptyBuiltin ;
        variables := StringVariables ;
        symbols :=  MySymbols;
    |}.

    Program Definition rule_sub_2 : RewritingRule :=
        rr_local_rewrite {|
            lr_from
                := pat_app
                    (pat_sym "Succ")
                    (pat_app 
                        (pat_sym "Succ")
                        (pat_var "X")
                    );
            lr_to := pat_var "X" ;
        |}
    .
    Solve All Obligations with set_solver.

End example_1.