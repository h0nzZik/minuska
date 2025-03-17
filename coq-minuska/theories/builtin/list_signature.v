From Minuska Require Import
    prelude
    spec
.

Variant ListFunSymbol :=
| list_nil
| list_cons
| list_head
| list_tail
| list_is_nil
.

Variant ListPredSymbol :=
| list_is
.

#[local]
Instance ListFunSymbol_eqdec : EqDecision ListFunSymbol.
Proof.
    ltac1:(solve_decision).
Defined.

#[local]
Instance ListPredSymbol_eqdec : EqDecision ListPredSymbol.
Proof.
    ltac1:(solve_decision).
Defined.

Definition list_signature : Signature := {|
    builtin_function_symbol := ListFunSymbol ;
    builtin_predicate_symbol := ListPredSymbol ;
|}.

