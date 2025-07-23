From Minuska Require Import
    prelude
    spec
.

Variant BoolFunSymbol :=
| bool_fun_true
| bool_fun_false
| bool_fun_neg
| bool_fun_and
| bool_fun_or
| bool_fun_iff
| bool_fun_xor
.

Variant BoolPredSymbol :=
| bool_pred_is
| bool_pred_is_false
| bool_pred_is_true
.

#[local]
Instance BoolFunSymbol_eqdec : EqDecision BoolFunSymbol.
Proof.
    ltac1:(solve_decision).
Defined.

#[local]
Instance BoolPredSymbol_eqdec : EqDecision BoolPredSymbol.
Proof.
    ltac1:(solve_decision).
Defined.

#[local]
Program Instance BoolFunSymbol_fin : Finite BoolFunSymbol := {|
    enum := [
        bool_fun_true;
        bool_fun_false;
        bool_fun_neg;
        bool_fun_and;
        bool_fun_or;
        bool_fun_iff;
        bool_fun_xor
    ]
|}.
Next Obligation.
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.


#[local]
Program Instance BoolPredSymbol_fin : Finite BoolPredSymbol := {|
    enum := [
        bool_pred_is;
        bool_pred_is_false;
        bool_pred_is_true
    ]
|}.
Next Obligation.
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.

Program Definition bool_signature : Signature := {|
    builtin_function_symbol := BoolFunSymbol ;
    builtin_predicate_symbol := BoolPredSymbol ;
|}.
Fail Next Obligation.
