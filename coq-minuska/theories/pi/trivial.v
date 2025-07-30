From Minuska Require Import
    prelude
    spec
    ocaml_interface
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
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
    {NondetValue : Type}
    {mysignature : Signature}
    {builtin : Model mysignature NondetValue}
    : @ProgramInfo TermSymbol TermSymbols NondetValue mysignature builtin
:= {|
    QuerySymbol := MyQuerySymbol ;
    ProgramT := @TermOver' TermSymbol BasicValue ;
    pi_TermSymbol_interp := fun my_program q es =>
        match q with
        | qs_program => Some my_program
        end ;
|}.

Definition bindings (P HP F A M : Type)
    :
    string -> SymbolInfo P HP F A _ M
:=
fun s =>
match s with
| "program.ast" => si_query _ _ _ _ _ _ qs_program
| _ => si_none _ _ _ _ _ _
end.
