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

    Definition SymbolSet := {s:string | s ∈ ["Zero"; "Succ" ] }.

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

    Lemma NoDup_sig
        (A : Type)
        (P : A -> Prop)
        (l : list (sig P)):
        NoDup (proj1_sig <$> l) ->
        NoDup l
    .
    Proof.
        induction l; intros H.
        { constructor. }
        {
            destruct a as [x p].
            cbn in H.
            inversion H. subst. clear H.
            constructor.
            {
                intros HContra.
                apply H2. clear H2.
                clear -HContra.
                induction l.
                {
                    inversion HContra.
                }
                {
                    cbn.
                    destruct a as [ax ap].
                    cbn.
                    inversion HContra; subst; clear HContra.
                    {
                        left.
                    }
                    {
                        right. apply IHl. exact H1.
                    }
                }
            }
            {
                auto with nocore.
            }
        }
    Qed.

    #[local]
    Program Instance SymbolSet_finite : Finite SymbolSet := {|
        enum := [exist _ "Zero" _; exist _ "Succ" _];
        NoDup_enum := _ ;
        elem_of_enum := _ ;
    |}.
    Next Obligation.
        ltac1:(set_solver).
    Qed.
    Next Obligation.
        ltac1:(set_solver).
    Qed.
    Next Obligation.
        apply NoDup_sig.
        cbn.
        remember (decide (NoDup ["Zero"; "Succ"])) as r.
        ltac1:(compute in Heqr).
        destruct r. assumption. inversion Heqr.
    Qed.
    Next Obligation.
        ltac1:(destruct x).
    Qed.

    #[local]
    Program Instance MySymbols : Symbols := {|
        symbol := SymbolSet ;
    |}.
    Next Obligation.
    Search Finite Countable.
        apply (finite_countable SymbolSet_finite).
    

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