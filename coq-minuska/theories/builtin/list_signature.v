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

#[local]
Program Instance ListFunSymbol_fin : Finite ListFunSymbol := {|
    enum := [
        list_nil;
        list_cons;
        list_head;
        list_tail;
        list_is_nil
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
Program Instance ListPredSymbol_fin : Finite ListPredSymbol := {|
    enum := [
        list_is
    ]
|}.
Next Obligation.
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.

Program Definition list_signature : Signature := {|
    builtin_function_symbol := ListFunSymbol ;
    builtin_predicate_symbol := ListPredSymbol ;
    bps_ar := fun p =>
        match p with
        | list_is => 1
        end ;
    bps_neg := fun p =>
        match p with
        | list_is => None
        end ;
    bps_neg_ar := _ ;
    bps_neg__sym := _;
|}.
Next Obligation.
    destruct p,p'; simpl in *; reflexivity.
Qed.
Next Obligation.
    destruct p,p'; simpl in *; ltac1:(simplify_eq/=).
Qed.
Fail Next Obligation.


