From Coq Require Export ssreflect ssrfun ssrbool.

Require Import Coq.Logic.FunctionalExtensionality.
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

(*
#[global]
Set Transparent Obligations.
*)

#[export]
Obligation Tactic := idtac.

(*
Require Import Equations.Type.All.
Set Equations Transparent.*)
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


Lemma rev_list_ind_T [A : Type] :
    forall P:list A-> Type,
    P [] ->
    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list A, P (rev l). 
Proof.
    intros P ? ? l; induction l; auto.
Qed.

Lemma rev_ind_T :
∀ [A : Type] (P : list A → Type),
  P [] → (∀ (x : A) (l : list A), P l → P (l ++ [x])) → ∀ l : list A, P l
.
Proof.
    intros A P ? ? l. rewrite <- (rev_involutive l).
    apply (rev_list_ind_T P); cbn; auto.
Qed.


Definition analyze_list_from_end {A : Type} (l : list A)
    : (l = nil) + ( ({ l' : list A & { x : A & l = l'++[x] } }))
.
Proof.
    induction l.
    {
        left. reflexivity.
    }
    {
        right.
        destruct IHl as [IHl|IHl].
        {
            subst. exists []. exists a. reflexivity.
        }
        {
            destruct IHl as [l' [x Hl']].
            subst.
            exists (a::l'). exists x. simpl. reflexivity.
        }
    }
Qed.


Lemma elem_of_list_fmap_T_1
    {A B : Type}
    {_eB : EqDecision B}
    (f : A → B) (l : list A) (x : B)
    :
    x ∈ f <$> l ->
    { y : A & x = f y ∧ y ∈ l }
.
Proof.
    induction l; simpl; intros HH.
    { rewrite elem_of_nil in HH. inversion HH. }
    {
        destruct (decide (x = f a)).
        {
            subst x.
            exists a.
            split>[reflexivity|].
            left.
        }
        {
            specialize(IHl ltac:(set_solver)).
            destruct IHl as [y [H1y H2y]].
            exists y.
            split>[exact H1y|].
            right. exact H2y.
        }
    }
Qed.


Lemma sum_list_with_compose {A B : Type} (g : A -> B) (f : B -> nat)
    :
    sum_list_with (f ∘ g) = (sum_list_with f) ∘ (fmap g)
.
Proof.
    apply functional_extensionality.
    intros l.
    induction l; simpl.
    {
        reflexivity.
    }
    {
        rewrite IHl. unfold compose. reflexivity.
    }
Qed.

Lemma sum_list_with_S (l : list nat):
    sum_list_with S l = sum_list l + length l
.
Proof.
    induction l; simpl.
    {
        reflexivity.
    }
    {
        rewrite IHl.
        ltac1:(lia).
    }
Qed.

Lemma sum_list_fmap
    {T: Type}
    (f : T -> nat)
    (l : list T)
    :
    sum_list ( f <$> l) = sum_list_with f l
.
Proof.
    induction l; simpl.
    { reflexivity. }
    {
        unfold fmap in IHl.
        rewrite IHl.
        reflexivity.
    }
Qed.

Lemma sum_list_with_sum_list_with
    {T: Type}
    (f : T -> nat)
    (l : list (list T))
    :
    sum_list_with (sum_list_with f) l = sum_list_with f (concat l)
.
Proof.
    induction l; simpl.
    { reflexivity. }
    {
        rewrite IHl.
        rewrite sum_list_with_app.
        reflexivity.
    }
Qed.


Program Fixpoint pfmap
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    : list B
:=
match l with
| nil => nil
| x::xs => (f x _)::(pfmap xs (fun (x' : A) (pf' : x' ∈ xs) => f x' _))
end
.
Next Obligation.
    intros. subst. rewrite elem_of_cons. left. reflexivity.
Defined.
Next Obligation.
    intros. subst. rewrite elem_of_cons. right. exact pf'.
Defined.
Fail Next Obligation.


Program Fixpoint pflookup
    {A : Type}
    (l : list A)
    (i : nat)
    (pflt : i < length l)
    : { x : A | x ∈ l}
:=
match l with
| [] => _
| x::xs =>
    match i with
    | 0 => (exist _ x _ )
    | S i' =>
        let tmp := pflookup xs i' _ in
        let x' := proj1_sig tmp in
        let pf := proj2_sig tmp in
        (exist _ x' _)
    end
end.
Next Obligation.
    abstract(ltac1:(intros; subst; simpl in *; lia)).
Qed.
Next Obligation.
    abstract(left).
Qed.
Next Obligation.
    intros. subst. simpl in *.
    abstract(ltac1:(lia)).
Qed.
Next Obligation.
    intros. subst. simpl in *.
    rewrite elem_of_cons.
    right. assumption.
Defined.
Fail Next Obligation.


Lemma pflookup_spec
    {A : Type}
    (l : list A)
    (i : nat)
    (pflt : i < length l)
    :
    Some (proj1_sig (pflookup l i pflt)) = l !! i
.
Proof.
    revert i pflt.
    induction l; intros i pflt.
    {
        simpl in pflt. ltac1:(lia).
    }
    {
        destruct i;
            simpl in *.
        {
            reflexivity.
        }
        {
            apply IHl.
        }
    }
Qed.

Lemma length_pfmap
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    :
    length (pfmap l f) = length l
.
Proof.
    induction l; simpl.
    { reflexivity. }
    {
        rewrite IHl. reflexivity.
    }
Qed.

Lemma pfmap_lookup_Some_lt
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    (i : nat)
    (y : B)
    :
    pfmap l f !! i = Some y ->
    i < length l
.
Proof.
    revert i f.
    induction l; intros i f H.
    {
        simpl in H.
        rewrite lookup_nil in H.
        inversion H.
    }
    {
        simpl in *.
        destruct i.
        {
            ltac1:(lia).
        }
        {
            simpl in H.
            specialize (IHl i _ H).
            ltac1:(lia).
        }
    }
Qed.

Arguments pfmap_lookup_Some_lt {A B}%_type_scope {l}%_list_scope {f}%_function_scope {i}%_nat_scope {y} _.

Lemma pfmap_lookup_Some_1
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    (i : nat)
    (y : B)
    (pf : pfmap l f !! i = Some y)
    :
    let pflt : i < length l := pfmap_lookup_Some_lt pf in
    y = (let xpf := (pflookup l i pflt) in (f (proj1_sig xpf) (proj2_sig xpf) ))
.
Proof.
    simpl.
    revert i y f pf.
    induction l; intros i y f pf.
    {
        simpl in pf. ltac1:(exfalso). rewrite lookup_nil in pf. inversion pf.
    }
    {
        destruct i.
        {
            simpl in *. inversion pf; subst.
            f_equal.
            apply proof_irrelevance.
        }
        {
            simpl in *.
            (* specialize (IHl i y). *)
            ltac1:(unshelve(erewrite IHl at 1))>[()|()|apply pf|].
            simpl.
            assert (Htmp0: ((@pfmap_lookup_Some_lt A _ l
          (λ (x' : A) (pf' : x' ∈ l),
             f x'
               (@flip2 Prop iff (λ x y0 : Prop, impl y0 x) iff_flip_impl_subrelation 
                  (x' ∈ a :: l) (x' = a ∨ x' ∈ l) (@elem_of_cons A l x' a)
                  (@or_intror (x' = a) (x' ∈ l) pf'))) i y pf)) = ((pflookup_obligation_3 A (a :: l) (S i) (@pfmap_lookup_Some_lt A _ (a :: l) f (S i) y pf) a l
          erefl i erefl))).
            {
                apply proof_irrelevance.
            }
            rewrite Htmp0.
            apply f_equal.
            apply proof_irrelevance.
        }
    }
Qed.


Lemma bind_Some_T_1
    (A B : Type)
    (f : A -> option B)
    (mx : option A)
    (y : B)
    :
    (mbind f mx) = Some y ->
    {x : A & mx = Some x /\ f x = Some y}
.
Proof.
    intros HH.
    destruct mx; simpl in *.
    {
        exists a.
        split>[reflexivity|exact HH].
    }
    { inversion HH. }
Qed.

Lemma bind_Some_T_2
    (A B : Type)
    (f : A -> option B)
    (mx : option A)
    (y : B)
    :
    {x : A & mx = Some x /\ f x = Some y} ->
    (mbind f mx) = Some y
.
Proof.
    intros HH.
    destruct HH as [x HH].
    destruct HH as [H1 H2].
    destruct mx; simpl in *.
    {
        inversion H1; subst; clear H1.
        exact H2.
    }
    {
        inversion H1.
    }
Qed.

Lemma bind_None_T_1 (A B : Type) (f : A → option B) (mx : option A):
  mbind f mx = None ->
  (mx = None) +
  ({ x : A & mx = Some x ∧ f x = None })
.
Proof.
    intros H.
    destruct mx; simpl in *.
    {
        right. exists a. split>[reflexivity|]. exact H.
    }
    {
        left. reflexivity.
    }
Qed.

Definition list_collect
    {A : Type}
    (l : list (option A))
    : option (list A)
:=
    foldr (fun ox ol => x ← ox; l' ← ol; Some (x::l')) (Some []) l
.

Lemma list_collect_Some_length
    {A : Type}
    (l : list (option A))
    (l' : list A)
    :
    list_collect l = Some l' ->
    length l = length l'
.
Proof.
    revert l'.
    induction l; intros l' HH; destruct l'; simpl in *.
    { reflexivity. }
    {
        ltac1:(simplify_eq/=).
    }
    {
        ltac1:(simplify_option_eq).
    }
    {
        ltac1:(simplify_option_eq).
        erewrite IHl.
        reflexivity.
        reflexivity.
    }
Qed.




Lemma length_filter_l_1_impl_h_in_l
    {A : Type}
    {_edA : EqDecision A}
    (l : list A)
    (h : A):
    length (filter (eq h) l) = 1 ->
    h ∈ l
.
Proof.
    intros H.
    induction l; simpl in *.
    { inversion H. }
    {
        rewrite filter_cons in H.
        destruct (decide (h = a)).
        {
            subst. left.
        }
        {
            right. apply IHl. apply H.
        }
    }
Qed.

Lemma h_in_l_impl_length_filter_l_gt_1
    {T : Type}
    (P : T -> Prop)
    {_dP: forall x, Decision (P x)}
    (l : list T)
    (h : T)
    :
    h ∈ l ->
    P h ->
    length (filter P l) >= 1
.
Proof.
    induction l; simpl.
    {
        intros HH. inversion HH.
    }
    {
        intros HH1 HH2.
        rewrite elem_of_cons in HH1.
        destruct HH1 as [HH1|HH1].
        {
            subst. rewrite filter_cons.
            destruct (decide (P a))>[|ltac1:(contradiction)].
            simpl.
            ltac1:(lia).
        }
        {
            specialize (IHl HH1 HH2).
            rewrite filter_cons.
            ltac1:(case_match).
            {
                simpl. ltac1:(lia).
            }
            {
                exact IHl.
            }
        }
    }
Qed.


Lemma length_filter_l_1_impl_h_in_l'
    {T : Type}
    (P : T -> Prop)
    {_dP: forall x, Decision (P x)}
    (l : list T)
    :
    length (filter P l) = 1 ->
    exists h, 
    h ∈ l /\ P h
.
Proof.
    intros H.
    induction l; simpl in *.
    { inversion H. }
    {
        rewrite filter_cons in H.
        destruct (decide (P a)).
        {
            subst. exists a. split. left. assumption.
        }
        {
            specialize (IHl H).
            destruct IHl as [h [H1h H2h]].
            exists h. split.
            right. assumption. assumption.
        }
    }
Qed.


Inductive MyUnit := mytt.


