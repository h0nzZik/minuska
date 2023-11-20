From Minuska Require Import
    prelude
.

Definition is_a_path
    {T : Type}
    (R : relation T)
    (l : list T)
    : Prop
:=
    NoDup l /\
    ∀ (i:nat) (x y : T),
        l !! i = Some x ->
        l !! (S i) = Some y ->
        R x y
.

Definition is_a_path_from_to
    {T : Type}
    (R : relation T)
    (l : list T)
    (from to : T)
    : Prop
:=
    is_a_path R l /\
    l !! 0 = Some from /\
    list.last l = Some to
.

Definition is_a_cycle
    {T : Type}
    (R : relation T)
    (l : list T)
    : Prop
:= is_a_path R l /\
    ∃ x y,
        list.last l = Some x /\
        l !! 0 = Some y /\
        R x y
.

Definition has_a_cycle_over
    {T : Type}
    (nodes : list T)
    (R : relation T)
:=
    ∃ (l : list T), l ⊆ nodes /\ is_a_cycle R l
.

Definition is_reachable_from
    {T : Type}
    (R : relation T)
    (from to : T)
:=
    ∃ l, is_a_path_from_to R l from to
.

Definition is_reachable_from_nodes
    {T : Type}
    (R : relation T)
    (nodes : list T)
    (to : T)
:=
    ∃ from, from ∈ nodes /\ is_reachable_from R from to
.

Definition all_are_reachable_from_nodes
    {T : Type}
    (R : relation T)
    (nodes : list T)
    (targets : list T)
:=
    ∀ to, to ∈ targets -> is_reachable_from_nodes R nodes to
.


Theorem has_a_cycle_dec
    {T : Type}
    {_eT : EqDecision T}
    (R : relation T)
    {decR : RelDecision R}
    (nodes : list T)
    : Decision (has_a_cycle_over nodes R)
.
Proof.
    (* TODO *)
Abort.

Theorem all_are_reachable_from_nodes_dec
    {T : Type}
    {_eT : EqDecision T}
    (R : relation T)
    (nodes : list T)
    (targets : list T)
    : Decision (all_are_reachable_from_nodes R nodes targets)
.
Proof.
    (* TODO *)
Abort.