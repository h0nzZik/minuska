From Minuska Require Import
    prelude
    spec
.

Variant IntFunSymbol :=
| int_plus
| int_minus
| int_uminus
| int_zero
| int_one
| int_eq
| int_le
| int_lt
.

Variant IntPredSymbol :=
| int_is
.

#[local]
Instance IntFunSymbol_eqdec : EqDecision IntFunSymbol.
Proof.
    ltac1:(solve_decision).
Defined.

#[local]
Instance IntPredSymbol_eqdec : EqDecision IntPredSymbol.
Proof.
    ltac1:(solve_decision).
Defined.

Definition int_signature : Signature := {|
    builtin_function_symbol := IntFunSymbol ;
    builtin_predicate_symbol := IntPredSymbol ;
|}.
