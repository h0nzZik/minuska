From Coq Require Export ssreflect ssrfun ssrbool.

From Coq.micromega Require Export Lia.

From stdpp Require Export
    base
    countable
    decidable
    gmap
    sets
    list
    list_numbers
    numbers
.
(* This is unset by stdpp. We need to set it again.*)
#[global]
Set Transparent Obligations.

From Equations Require Export Equations.

#[global]
Set Equations Transparent.

Require Export Wellfounded.

From Ltac2 Require Export Ltac2.

Add Search Blacklist "_graph_mut".
Add Search Blacklist "_graph_rect".
Add Search Blacklist "_graph_equation".
Add Search Blacklist "FunctionalElimination_".

(* Convert Equations eq decision to stdpp's eq decision*)
#[export]
Instance EquationsEqdec
    (T : Type)
    {dec : Equations.Prop.Classes.EqDec T}:
    EqDecision T
.
Proof.
    intros x y.
    apply eq_dec.
Defined.
