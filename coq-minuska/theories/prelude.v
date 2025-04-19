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

Lemma length_list_collect_Some
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


Lemma list_collect_inv
    {A : Type}
    (l_in : list (option A))
    (l_out : list A)
:
    list_collect l_in = Some l_out ->
    Forall (isSome) l_in
.
Proof.
    revert l_out.
    induction l_in; intros l_out H1.
    {
        constructor.
    }
    {
        simpl in H1.
        rewrite bind_Some in H1.
        destruct H1 as [x [H1x H2x]].
        subst a.
        rewrite bind_Some in H2x.
        destruct H2x as [l' [H1l' H2l']].
        injection H2l' as H2l'.
        constructor.
        {
            reflexivity.
        }
        {
            eapply IHl_in.
            apply H1l'.
        }
    }
Qed.


Lemma list_collect_Exists
    {A : Type}
    (l_in : list (option A))
    :
    Exists (not ∘ isSome) l_in ->
    list_collect l_in = None
.
Proof.
    induction l_in; intros H1; simpl.
    { inversion H1. }
    {
        rewrite bind_None.
        destruct a.
        {
            right.
            inversion H1; subst; clear H1.
            {
                exists a.
                split>[reflexivity|].
                rewrite bind_None.
                left.
                apply IHl_in.
                rewrite Exists_exists.
                simpl in H0.
                ltac1:(exfalso).
                apply H0.
                reflexivity.
            }
            {
                exists a.
                split>[reflexivity|].
                rewrite bind_None.
                left.
                apply IHl_in.
                apply H0.
            }
        }
        {
            left. reflexivity.
        }
    }
Qed.

Lemma list_collect_Forall
    {A : Type}
    (l_in : list (option A))
    :
    Forall isSome l_in ->
    exists l_out,
        list_collect l_in = Some l_out
        /\ l_in = (Some <$> l_out)
.
Proof.
    induction l_in; intros H1; simpl.
    {
        exists [].
        repeat split.
    }
    {
        apply Forall_cons in H1.
        destruct H1 as [H1 H2].
        specialize (IHl_in H2).
        destruct IHl_in as [l_out [H1l_out H2l_out]].
        subst.
        destruct a; simpl in H1.
        {
            clear H1.
            exists (a::l_out).
            simpl.
            (repeat split).
            rewrite H1l_out. clear H1l_out.
            rewrite bind_Some.
            exists l_out.
            repeat split.
        }
        {
            inversion H1.
        }
    }
Qed.


Lemma list_collect_Exists_1
    {A : Type}
    (l_in : list (option A))
    :
    list_collect l_in = None ->
    Exists (not ∘ isSome) l_in
.
Proof.
    induction l_in; intros HH; simpl in *.
    {
        inversion HH.
    }
    {
        rewrite bind_None in HH.
        destruct HH as [HH|HH].
        {
            subst a.
            left.
            simpl.
            intros HContra.
            inversion HContra.
        }
        {
            destruct HH as [x [H1x H2x]].
            rewrite bind_None in H2x.
            subst a.
            destruct H2x as [H2x|H2x].
            {
                right. apply IHl_in. apply H2x.
            }
            {
                destruct H2x as [x0 [H1x0 H2x0]].
                inversion H2x0.
            }
        }
    }
Qed.

Lemma list_collect_Forall_T
    {A : Type}
    (l_in : list (option A))
    :
    Forall isSome l_in ->
    { l_out : _ & list_collect l_in = Some l_out
        /\ l_in = (Some <$> l_out) }
.
Proof.
    induction l_in; intros H1; simpl.
    {
        exists [].
        repeat split.
    }
    {
        apply Forall_cons in H1.
        destruct H1 as [H1 H2].
        specialize (IHl_in H2).
        destruct IHl_in as [l_out [H1l_out H2l_out]].
        subst.
        destruct a; simpl in H1.
        {
            clear H1.
            exists (a::l_out).
            simpl.
            (repeat split).
            rewrite H1l_out. clear H1l_out.
            rewrite bind_Some.
            exists l_out.
            repeat split.
        }
        {
            inversion H1.
        }
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

Lemma list_filter_Forall_not
    {T : Type}
    (P : T -> Prop)
    {_dP : forall x, Decision (P x)}
    (l : list T)
    :
    Forall (fun x => not (P x)) l ->
    filter P l = []
.
Proof.
    induction l; simpl; intros H.
    {
        reflexivity.
    }
    {
        apply Forall_cons in H.
        destruct H as [H1 H2].
        specialize (IHl H2). clear H2.
        rewrite filter_cons.
        destruct (decide (P a)).
        {
            ltac1:(contradiction).
        }
        apply IHl.
    }
Qed.


Lemma length_filter_eq__eq__length_filter_in__zero
    {T : Type}
    {_edT: EqDecision T}
    (h : T)
    (l : list (list T))
    :
    length (filter (eq h) (concat l)) = 0 ->
    length (filter (elem_of h) l) = 0
.
Proof.
    induction l; simpl; intros HH.
    {
        ltac1:(lia).
    }
    {
        rewrite filter_app in HH.
        rewrite filter_cons.
        destruct (decide (h ∈ a)) as [Hin|Hnotin].
        {
            simpl. rewrite length_app in HH.
            assert(Htmp := h_in_l_impl_length_filter_l_gt_1 (eq h) a h Hin eq_refl).
            ltac1:(exfalso).
            ltac1:(lia).
        }
        {
            simpl. rewrite length_app in HH.
            apply IHl. ltac1:(lia).
        }
    }
Qed.

Lemma length_filter_eq__eq__length_filter_in__one
    {T : Type}
    {_edT: EqDecision T}
    (h : T)
    (l : list (list T))
    :
    length (filter (eq h) (concat l)) = 1 ->
    length (filter (elem_of h) l) = 1
.
Proof.
    {
        induction l; simpl; intros HH.
        {
            ltac1:(lia).
        }
        {
            rewrite filter_cons.
            rewrite filter_app in HH.
            rewrite length_app in HH.
            destruct (decide (h ∈ a)) as [Hin|Hnotin].
            {
                assert(Htmp := h_in_l_impl_length_filter_l_gt_1 (eq h) a h Hin eq_refl).
                simpl in *.
                assert (length (filter (eq h) (concat l)) = 0).
                {
                    ltac1:(lia).
                }
                apply length_filter_eq__eq__length_filter_in__zero in H.
                rewrite H.
                reflexivity.                
            }
            {
                apply IHl. clear IHl.
                assert (length (filter (eq h) a) = 0).
                {
                    clear -Hnotin.
                    induction a.
                    {
                        simpl. reflexivity.
                    }
                    {
                        rewrite elem_of_cons in Hnotin.
                        apply Decidable.not_or in Hnotin.
                        destruct Hnotin as [Hnotin1 Hnotin2].
                        rewrite filter_cons.
                        destruct (decide (h = a))>[ltac1:(subst;contradiction)|].
                        apply IHa. exact Hnotin2.
                    }
                }
                ltac1:(lia).
            }
        }
    }
Qed.

Lemma filter_fmap
    {T1 T2: Type}
    (f : T1 -> T2)
    (P : T2 -> Prop)
    {_decP : forall x, Decision (P x)}
    {_decfP : forall x, Decision ((P ∘ f) x)}
    (l : list T1)
    :
    filter P (f <$> l) = f <$> (filter (P ∘ f) l)
.
Proof.
    induction l.
    {
        simpl. rewrite filter_nil. reflexivity.
    }
    {
        rewrite filter_cons.
        rewrite fmap_cons.
        rewrite filter_cons.
        rewrite IHl.
        unfold compose.
        simpl in *.
        ltac1:(repeat case_match); try (ltac1:(contradiction)).
        {
            reflexivity.
        }
        {
            reflexivity.
        }
    }
Qed.

Lemma on_a_shared_prefix
    {T : Type}
    (_edT : EqDecision T)
    (b : T)
    (l1 l2 l1' l2' : list T)
    :
    b ∉ l1 ->
    b ∉ l1' ->
    l1 ++ b::l2 = l1' ++ b::l2' ->
    l1 = l1'
.
Proof.
    revert l1'.
    induction l1; simpl; intros l1' H1 H2 H3.
    {
        destruct l1'; simpl in *.
        { reflexivity. }
        {
            ltac1:(exfalso).
            inversion H3; subst; clear H3.
            apply H2. clear H2.
            rewrite elem_of_cons. left. reflexivity.
        }
    }
    {
        destruct l1'.
        {
            ltac1:(exfalso).
            inversion H3; subst; clear H3.
            apply H1. clear H1.
            rewrite elem_of_cons. left. reflexivity.
        }
        {
            rewrite elem_of_cons in H1.
            rewrite elem_of_cons in H2.
            apply Decidable.not_or in H1.
            apply Decidable.not_or in H2.
            destruct H1 as [H11 H12].
            destruct H2 as [H21 H22].
            simpl in H3. inversion H3; subst; clear H3.
            specialize (IHl1 l1' H12 H22 H1).
            subst l1'.
            reflexivity.
        }
    }
Qed.


Lemma set_filter_pred_impl
    {A B : Type}
    {_EA : EqDecision A}
    {_Elo : ElemOf A B}
    {_Els : Elements A B}
    {_Em : Empty B}
    {_Sg : Singleton A B}
    {_IB : Intersection B}
    {_DB : Difference B}
    {_U : Union B}
    {_FS : @FinSet A B _Elo _Em _Sg _U _IB _DB _Els _EA}
    (P1 P2 : A -> Prop)
    {_DP1 : ∀ (x : A), Decision (P1 x)}
    {_DP2 : ∀ (x : A), Decision (P2 x)}
    (thing : B)
    :
    (forall (x : A), P1 x -> P2 x) ->
    @filter A B (set_filter) P1 _ thing ⊆ @filter A B (set_filter) P2 _ thing
.
Proof.
    intros Himpl.
    unfold subseteq.
    ltac1:(apply (proj2 (@elem_of_subseteq A B _ (@filter A B _ P1 _DP1 thing) (@filter A B _ P2 _DP2 thing)))).
    intros x.
    intros Hx.
    ltac1:(apply (proj1 (elem_of_filter P1 thing x)) in Hx).
    ltac1:(apply (proj2 (elem_of_filter P2 thing x))).
    ltac1:(naive_solver).
Qed.

Lemma map_lookup_Some
    {A B : Type}
    (f : A -> B)
    (l : list A)
    (i : nat)
    (y : B)
    :
    (map f l) !! i = Some y ->
    {x : A & (l !! i = Some x /\ y = f x)}
.
Proof.
    revert i.
    induction l; simpl; intros i HH.
    {
        rewrite lookup_nil in HH. inversion HH.
    }
    {
        destruct i.
        {
            simpl in HH. inversion HH; subst; clear HH.
            exists a. split; reflexivity.
        }
        {
            simpl in HH.
            specialize (IHl _ HH).
            destruct IHl as [x [H1x H2x]].
            subst y.
            exists x.
            simpl.
            split>[assumption|reflexivity].
        }
    }
Qed.

Lemma fmap_Some_T_1 (A B : Type) (f : A → B) (mx : option A) (y : B):
  f <$> mx = Some y ->
  {x : A & mx = Some x ∧ y = f x }
.
Proof.
    intros H.
    destruct mx; simpl in *.
    {
        inversion H; subst; clear H.
        exists a.
        split;reflexivity.
    }
    {
        inversion H.
    }
Qed.


Lemma sum_list_with_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 >= f2 x2) ->
    sum_list_with f1 l1 >= sum_list_with f2 l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 ≥ sum_list_with f2 l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.

Lemma sum_list_with_eq_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 = f2 x2) ->
    sum_list_with f1 l1 = sum_list_with f2 l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 = sum_list_with f2 l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.

Lemma sum_list_with_eq_plus_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (g : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 = f2 x2 + g x2) ->
    sum_list_with f1 l1 = sum_list_with f2 l2 + sum_list_with g l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 = sum_list_with f2 l2 + sum_list_with g l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.




Lemma list_filter_Forall_all
    {T : Type}
    (P : T -> Prop)
    {_dP : forall x, Decision (P x)}
    (l : list T)
    :
    Forall P l ->
    filter P l = l
.
Proof.
    induction l; simpl; intros H.
    {
        reflexivity.
    }
    {
        apply Forall_cons in H.
        destruct H as [H1 H2].
        specialize (IHl H2). clear H2.
        rewrite filter_cons.
        destruct (decide (P a)).
        {
            rewrite IHl. reflexivity.
        }
        ltac1:(contradiction).
    }
Qed.


Lemma count_one_split
    {T : Type}
    (P : T -> Prop)
    (_dP : forall x, Decision (P x))
    (l : list T)
    :
    length (filter P l) = 1 ->
    exists (la : list T) (b : T) (lc : list T),
    l = la ++ b::lc
    /\ P b
    /\ Forall (fun x => not (P x)) la
    /\ Forall (fun x => not (P x)) lc
.
Proof.
    remember (list_find P l) as lf.
    destruct lf.
    {
        symmetry in Heqlf.
        destruct p.
        apply list_find_Some in Heqlf.
        intros HH.
        destruct Heqlf as [H1 [H2 H3]].
        apply take_drop_middle in H1.
        exists (take n l).
        exists t.
        exists (drop (S n) l).
        split.
        {
            symmetry. exact H1.
        }
        split>[exact H2|].
        split.
        {
            rewrite Forall_forall.
            intros x Hx.
            rewrite elem_of_list_lookup in Hx.
            destruct Hx as [i Hi].
            rewrite lookup_take_Some in Hi.
            destruct Hi as [Hi H'i].
            eapply H3.
            { apply Hi. }
            { apply H'i. }
        }
        {
            rewrite Forall_forall.
            intros x Hx HContra.
            rewrite elem_of_list_lookup in Hx.
            destruct Hx as [i Hi].
            apply take_drop_middle in Hi.
            rewrite <- Hi in H1.
            rewrite <- H1 in HH.
            clear H1 Hi.
            rewrite filter_app in HH.
            rewrite filter_cons in HH.
            destruct (decide (P t))>[|ltac1:(contradiction)].
            rewrite filter_app in HH.
            rewrite filter_cons in HH.
            destruct (decide (P x))>[|ltac1:(contradiction)].
            rewrite length_app in HH. simpl in HH.
            rewrite length_app in HH. simpl in HH.
            ltac1:(lia).
        }
    }
    {
        symmetry in Heqlf.
        apply list_find_None in Heqlf.
        intros Hlength.
        apply length_filter_l_1_impl_h_in_l' in Hlength.
        destruct Hlength as [h [H1h H2h]].
        rewrite Forall_forall in Heqlf.
        ltac1:(exfalso).
        ltac1:(naive_solver).
    }
Qed.


Lemma sum_list_with_perm
    {T : Type}
    (f : T -> nat)
    (l1 l2 : list T)
    :
    l1 ≡ₚ l2 ->
    sum_list_with f l1 = sum_list_with f l2
.
Proof.
    intros H.
    induction H.
    {
        reflexivity.
    }
    {
        simpl. rewrite IHPermutation. reflexivity.
    }
    {
        simpl. ltac1:(lia).
    }
    {
        ltac1:(congruence).
    }
Qed.

Lemma flat_map_lookup_Some
    {A B : Type}
    (f : A -> list B)
    (l : list A)
    (i : nat)
    (y : B)
    :
    (flat_map f l) !! i = Some y ->
    { j : nat & { x : A & { k : nat & l !! j = Some x /\ (f x) !! k = Some y } } }
.
Proof.
    revert i.
    induction l; simpl; intros i HH.
    {
        rewrite lookup_nil in HH.
        inversion HH.
    }
    {
        destruct (decide (i < length (f a))) as [Hlt|Hgeq].
        {
            rewrite lookup_app_l in HH>[|exact Hlt].
            exists 0.
            exists a.
            exists i.
            simpl.
            split>[reflexivity|].
            exact HH.            
        }
        {
            rewrite lookup_app_r in HH.
            specialize (IHl _ HH).
            destruct IHl as [j [x [k [H1 H2]]]].
            exists (S j).
            exists x.
            exists k.
            simpl.
            split>[apply H1|].
            exact H2.
            ltac1:(lia).
        }
    }
Qed.


Inductive MyUnit := mytt.


Definition slice {A : Type} {_eqA : EqDecision A} (from : nat) (to : nat) (l : list A) :=
    take (to - from) (drop from l)
.

Ltac2 simplify_fmap_eq () :=
    repeat (
        match! goal with
        | [h: ([] = (_ <$> _)) |- _] =>
            symmetry in $h
        | [h: (_::_ = (_ <$> _)) |- _] =>
            symmetry in $h
        | [h: ((?f <$> ?l) = []) |- _] =>
            apply fmap_nil_inv in $h; subst
        | [h: ((?f <$> ?l) = (?x::?xs)) |- _] =>
            apply fmap_cons_inv in $h;
            Std.destruct
                false
                [{
                    Std.indcl_arg := Std.ElimOnIdent(h);
                    Std.indcl_eqn := None;
                    Std.indcl_as := Some(Std.IntroAndPattern(
                        [
                            Std.IntroNaming(Std.IntroAnonymous);
                            Std.IntroAction(
                                Std.IntroOrAndPattern(Std.IntroAndPattern([
                                    Std.IntroNaming(Std.IntroAnonymous);
                                    Std.IntroNaming(Std.IntroAnonymous)
                                ]))
                            )
                        ]
                        )) ;
                    Std.indcl_in := None;
                }]
                None;
            ltac1:(destruct_and?);
            subst; simpl in *;
            ()
        end
    )
.

Ltac2 simplify_take_drop () :=
    repeat (
        match! goal with
        | [h: context c [take 0 _] |- _] =>
            rewrite take_0 in $h
        | [h: context c [drop 0 _] |- _] =>
            rewrite drop_0 in $h
        | [h: context c [take (S _) (_::_)] |- _] =>
            rewrite firstn_cons in $h; simpl in *
        | [h: context c [take (S _) ?l] |- _] =>
            destruct $l; simpl in *
        | [h: context c [drop (S _) (_::_)] |- _] =>
            rewrite skipn_cons in $h; simpl in *
        | [h: context c [drop (S _) ?l] |- _] =>
            destruct $l; simpl in *
        end
    )
.

Ltac2 case_on_length () :=
    repeat(
        simpl in *;
        match! goal with
        | [h: ((length ?args) = (S _)) |- _] =>
            destruct $args; simpl in $h; try ltac1:(lia)
        | [h: ((length ?args) = O) |- _] =>
            destruct $args; simpl in $h; try ltac1:(lia)
        | [h: ((S _) = (S _)) |- _] =>
            apply Nat.succ_inj in $h
        end
    )
.
