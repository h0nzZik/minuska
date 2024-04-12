From Minuska Require Import
    prelude
    spec
    string_variables
    builtins
    spec_interpreter
    naive_interpreter
    interpreter_results
    default_static_model
    notations
    frontend
    interp_loop
.


Variant Act := default_act | invisible_act.

#[global]
Instance Act_eqDec : EqDecision Act.
Proof.
    ltac1:(solve_decision).
Defined.

Module example_1.

    #[local]
    Instance Σ : StaticModel :=
        default_model (default_builtin.β)
    .
    
    Definition X : variable := "X".

    Definition cfg {_br : BasicResolver} := (@t_term _ operand_type "cfg").
    Arguments cfg {_br} _%_rs.

    Definition s {_br : BasicResolver} := (@t_term _ operand_type "S").
    Arguments s {_br} _%_rs.

    Definition Decls : list Declaration := [
        decl_rule (
            rule ["my_rule"]:
                cfg [ s [ s [ t_over ($X) ] ] ]
                ~>{default_act} cfg [ t_over ($X) ]
        )
    ].

    Definition Γ : (RewritingTheory2 Act)*(list string)
        := Eval vm_compute in (to_theory Act (process_declarations Act default_act (Decls))).

    Definition interp :=
        naive_interpreter Γ.1
    .

    Compute (naive_interpreter Γ.1 (t_term "S" [t_term "S" [t_term "0" nil]])).

    Fixpoint my_number' (n : nat) : TermOver builtin_value  :=
    match n with
    | 0 => t_term "0" nil
    | S n' => t_term "S" [(my_number' n')]
    end
    .

    Fixpoint my_number'_inv
        (g : TermOver builtin_value)
        : option nat
    :=
    match g with
    | t_term s nil => if bool_decide (s = "0") then Some 0 else None
    | t_term s [arg] =>
        if bool_decide (s = "S") then
            n ← my_number'_inv arg;
            Some (S n)
        else None
    | _ => None
    end
    .

    Definition my_number (n : nat) : (TermOver builtin_value) :=
        t_term "cfg" [(my_number' n)]
    .

    Definition my_number_inv (g : (TermOver builtin_value)) : option nat
    :=
    match g with
    | t_term "cfg" [g'] => my_number'_inv g'
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

    Definition interp_loop_number (fuel : nat) := 
        fun n : nat =>
        let fg' := (((interp_in_from Γ) fuel) ∘ my_number) n in
        my_number_inv fg'.1.2
    .

    Example ex_1: interp_loop_number 1 2 = Some 0.
    Proof. reflexivity. Qed.

    Example ex_2: interp_loop_number 1 5 = Some 3.
    Proof. reflexivity. Qed.

    Example ex_3: interp_loop_number 1 6 = Some 4.
    Proof. reflexivity. Qed.

    Example ex_4: interp_loop_number 1 20 = Some 18.
    Proof. reflexivity. Qed.

End example_1.
