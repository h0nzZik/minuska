From Coq Require Export ssreflect ssrfun ssrbool.

Require Import Logic.PropExtensionality.
From Coq.micromega Require Export Lia.

From stdpp Require Export
    base
    countable
    decidable
    finite
    fin_maps
    fin_sets
    gmap
    hlist
    sets
    strings
    tactics
    list
    list_numbers
    numbers
    pmap
    pretty
.

(* This is unset by stdpp. We need to set it again.*)

#[global]
Set Transparent Obligations.

(*
From Equations Require Export Equations.


#[global]
Set Equations Transparent.
*)

Require Export Wellfounded.

From Ltac2 Require Export Ltac2.

Add Search Blacklist "_graph_mut".
Add Search Blacklist "_graph_rect".
Add Search Blacklist "_graph_equation".
Add Search Blacklist "FunctionalElimination_".

(*
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
*)
(* "Inspect pattern", as in https://github.com/mattam82/Coq-Equations/issues/232 *)
Definition inspect {Y} (x : Y) : {y | x = y}.
Proof. now exists x. Defined.

(* https://github.com/bedrocksystems/BRiCk/blob/master/theories/prelude/under_rel_proper.v *)
#[export] Instance under_mono {T : Type} {R : relation T} `{!RewriteRelation R}
    `{!Symmetric R} `{!Transitive R}:
    Proper (flip R ==> eq ==> impl) (Under_rel T R).
Proof. ltac1:(move=> b a /= + c _ <- +). rewrite Under_relE. ltac1:(apply: transitivity). Qed.

#[export] Instance under_flip_mono {T : Type} {R : relation T} `{!RewriteRelation R}
    `{!Symmetric R} `{!Transitive R} :
    Proper (R ==> eq ==> flip impl) (Under_rel T R).
Proof. ltac1:(move=> b a /= + c _ <- +). rewrite Under_relE. ltac1:(apply: transitivity). Qed.

(* https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/.60Proper.20.2E.2E.2E.20.28Under_rel.20.2E.2E.2E.29.60/near/290318612 *)
#[export]
Instance under_proper {T : Type} {R : relation T} `{!RewriteRelation R}
    `{!Symmetric R} `{!Transitive R}
:
    Proper (R ==> eq ==> iff) (@Under_rel T R)
.
Proof.
    ltac1:(move=> x y Heq ? _ <-).
        rewrite Under_relE.
    ltac1:(have ? : RewriteRelation R by []).
    ltac1:(by split; rewrite Heq).
Qed.

#[export]
Instance: Params (@Under_rel) 2 := {}.

#[export]
Instance under_rel_refl: Reflexive (@Under_rel Prop eq).
Proof.
    {
        intros x. ltac1:(over).
    }
Qed.

#[export]
Instance under_rel_trans: Transitive (@Under_rel Prop eq).
Proof.
    {
        intros x y z Hx Hy.
        apply Under_rel_from_rel in Hx.
        apply Under_rel_from_rel in Hy.
        subst.
        ltac1:(over).
    }
Qed.

#[export]
Instance under_rel_symm: Symmetric (@Under_rel Prop eq).
Proof.
    {
        intros x y Hx.
        apply Under_rel_from_rel in Hx.
        subst.
        ltac1:(over).
    }
Qed.

#[export]
Instance under_rel_equiv: Equivalence (@Under_rel Prop eq).
Proof.
    constructor.
    {
        apply under_rel_refl.
    }
    {
        apply under_rel_symm.
    }
    {
        apply under_rel_trans.
    }
Qed.

#[export]
Instance under_rel_subrel: (subrelation iff (Under_rel Prop eq)).
Proof.
    intros x y Hxy.
    apply propositional_extensionality in Hxy.
    subst.
    ltac1:(over).
Qed.


Lemma list_find_elem_of_isSome
    {A : Type}
    (P : A -> Prop)
    {_dP : forall x, Decision (P x)}
    (l : list A)
    (x : A)
    :
    x ∈ l -> P x -> isSome (list_find P l).
Proof.
    ltac1:(induction 1 as [|x y l ? IH]; intros; simplify_option_eq; eauto).
    specialize (IH ltac:(assumption)).
    Set Printing Coercions.
    unfold is_true, isSome in *.
    destruct (list_find P l) eqn:Hfound; simpl.
    { reflexivity. }
    { inversion IH. }
Qed.
