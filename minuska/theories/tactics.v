From Coq.Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable decidable finite list list_numbers gmap strings.

From Ltac2 Require Import Ltac2.
Check @ex.
Ltac2 rec destruct_ex_go (h : ident) :=

try (
    let h_hyp := Control.hyp h in
    let h_type := Constr.type h_hyp in
    lazy_match! h_type with
| (@ex _ _) => (
        Message.print (Message.of_string "Here");
        let x := Fresh.in_goal ident:(x) in
        let hx := Fresh.in_goal ident:(Hx) in
        destruct $h_hyp as [ $x $hx ];
        destruct_ex_go hx
    )
end).

Ltac2 Notation "destruct_ex" "?" h(ident) :=
    destruct_ex_go h
.

Ltac2 destruct_ex_bang_hyp (h : ident) :=
    hnf in $h ;
    progress (destruct_ex_go h)
.

Ltac2 Notation "destruct_ex" "!" h(ident) :=
    destruct_ex_bang_hyp h
.

Ltac2 destruct_ex_question_hyp () :=
repeat (
    match! goal with
    | [h : _ |- _] => progress (destruct_ex_go h)
    end
).

Ltac2 Notation "destruct_ex?" :=
    destruct_ex_question_hyp ()
. 

Ltac2 Notation "destruct_ex" "!" :=
    progress (destruct_ex?)
.

Example ex_destruct_ex:
    (exists x, exists y, x = y + 1) ->
    True.
Proof.
    intros H.
    destruct_ex_bang_hyp ident:(H).
Abort.