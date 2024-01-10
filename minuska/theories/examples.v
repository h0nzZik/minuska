From Coq.Logic Require Import ProofIrrelevance.


From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    empty_builtin
    flattened
    naive_interpreter
    default_static_model
    notations
.




Module example_1.

    Definition rule_1 : FlattenedRewritingRule :=
        rule ("top" [< "s" [< "s" [< $"X" >] >] >])
          => ("top" [< $"X" >])
          requires []
    .

    (*Print rule_1.*)

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

End example_1.


Module two_counters.

    Definition top := "top".
    Definition state := "state".
    Definition s := "s".
    Definition M := "M".
    Definition N := "N".

    Definition rule_1 : FlattenedRewritingRule :=
        rule top [< state [< s [< $M >], $N >] >]
          => top [< state [< $M, s [< $N >]  >] >]
          requires []
    .

    (*Print rule_1.*)

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

    Definition pair_to_state (mn : nat*nat) : GroundTerm :=
        aoo_app _ _ (ao_app_ao (ao_operator "top")
        (
            ao_app_ao
                (
                ao_app_ao (ao_operator "state")
                    (example_1.my_number' mn.1)
                )
                (example_1.my_number' mn.2)
        )
        )
    .

    Definition state_to_pair (g : GroundTerm) : option (nat*nat) :=
    match g with
    | aoo_app _ _ (ao_app_ao (ao_operator "top")
        (ao_app_ao (ao_app_ao (ao_operator "state") (m')) n'))
        => 
            m ← example_1.my_number'_inv m';
            n ← example_1.my_number'_inv n';
            Some (m, n)
    | _ => None
    end
    .

    Lemma pair_state_inversion : forall m n,
        state_to_pair (pair_to_state (m,n)) = Some (m,n)
    .
    Proof.
        intros m n.
        simpl.
        rewrite bind_Some.
        exists m.
        split.
        { rewrite example_1.my_number_inversion'. reflexivity. }
        rewrite bind_Some.
        exists n.
        split.
        { rewrite example_1.my_number_inversion'. reflexivity. }
        reflexivity.
    Qed.

    Definition interp_loop_number fuel := 
        fun (m n : nat) =>
        let og' := ((interp_loop fuel) ∘ pair_to_state) (m,n) in
        g' ← og';
        state_to_pair g'
    .

End two_counters.

Module fib.

Definition d0 := "d0".
Definition s := "s".
Definition plus := "plus".
Definition fibb := "fibb".
Definition N := "N".
Definition M := "M".
Definition rules := [
rule "top"[<plus [<d0[<>], $N>] >] => "top"[< $N>] requires [];
rule "top"[<plus [<s [<$N>], $M>] >] => "top"[< s [<plus [<$N, $M>]>]>] requires [];
rule "top"[<fibb [<d0[<>]>] >] => "top"[< d0[<>]>] requires [];
rule "top"[<fibb [<s [<d0[<>]>]>] >] => "top"[< s [<d0[<>]>]>] requires [];
rule "top"[<fibb [<s [<s [<$N>]>]>] >] => "top"[< plus [<fibb [<s [<$N>]>], fibb [<$N>]>]>] requires []].
Definition term_to_reduce :=
(fibb [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<s [<d0[<>]>]>]>]>]>]>]>]>]>]>]>]>]>]>]>]>]>]>]>])%concrete
.

End fib.

