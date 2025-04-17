From Minuska Require Import
    prelude
    spec
.

Inductive MyQuerySymbol : Set :=
| qs_program
.

#[local]
Instance MyQuerySymbol_eqdec : EqDecision MyQuerySymbol.
Proof.
    ltac1:(solve_decision).
Defined.

#[export]
Program Instance MyQuerySymbol_fin : Finite MyQuerySymbol := {|
    enum := [qs_program];
|}.
Next Obligation.
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.


#[local]
Instance MyProgramInfo
    {symbol : Type}
    {symbols : Symbols symbol}
    {NondetValue : Type}
    {mysignature : Signature}
    {builtin : Model mysignature NondetValue}
    : @ProgramInfo symbol symbols NondetValue mysignature builtin
:= {|
    QuerySymbol := MyQuerySymbol ;
    ProgramT := @TermOver' symbol builtin_value ;
    pi_symbol_interp := fun my_program q es =>
        match q with
        | qs_program => my_program
        end ;
|}.

Definition my_binding : list (string*string) := [
    ("program.ast", "qs_program")
].

(* Print Grammar. *)