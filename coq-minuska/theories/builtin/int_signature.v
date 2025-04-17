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

#[local]
Program Instance IntFunSymbol_fin : Finite IntFunSymbol := {|
    enum := [
        int_plus;
        int_minus;
        int_uminus;
        int_zero;
        int_one;
        int_eq;
        int_le;
        int_lt
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
Program Instance IntPredSymbol_fin : Finite IntPredSymbol := {|
    enum := [
        int_is
    ]
|}.
Next Obligation.
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.

Program Definition int_signature : Signature := {|
    builtin_function_symbol := IntFunSymbol ;
    builtin_predicate_symbol := IntPredSymbol ;
    bps_ar := fun p =>
        match p with
        | int_is => 1
        end ;
    bps_neg := fun p =>
        match p with
        | int_is => None
        end ;
    bps_neg_ar := _;
    bps_neg__sym := _;
|}.
Next Obligation.
    destruct p,p'; simpl in *; ltac1:(lia).
Qed.
Next Obligation.
    destruct p,p'; simpl in *; ltac1:(simplify_eq/=).
Qed.
Fail Next Obligation.
