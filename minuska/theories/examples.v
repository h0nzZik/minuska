From Coq.Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable decidable list list_numbers gmap strings.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
Set Equations Transparent.

Require Import Wellfounded.
From Ltac2 Require Import Ltac2.

From Minuska Require Import minuska string_variables empty_builtin.


Module example_1.

    Record SymbolSet : Set := {
        ss_name : string ;
        ss_pf : ss_name ∈ ["Zero"; "Succ" ] ;
    }.

    #[local]
    Instance symbolSet_eqdec : EqDecision SymbolSet.
    Proof.
        intros [s1 pf1] [s2 pf2].
        destruct (decide (s1 = s2)) as [e|n].
        {
            subst. left. apply f_equal. apply proof_irrelevance.
        }
        {
            right. intros HContra. apply n. clear n.
            inversion HContra. reflexivity.
        }
    Defined.

    #[local]
    Instance MySymbols : Symbols := {|
        symbol := SymbolSet ;
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
                    {| ss_name := "Succ"; |}
                    [pat_app 
                        {| ss_name := "Succ" |}
                        [pat_var "X"]
                    ];
            lr_to := pat_var "X" ;
        |}
    .
    Solve All Obligations with set_solver.

End example_1.