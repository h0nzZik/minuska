From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    unification_interface
    termoverbov_subst
    termoverbov_subst_properties
    substitution_sequential
    substitution_sequential_properties
    substitution_parallel
    substitution_parallel_properties
    textbook_unification_alg
    substitution_parseq_conv
.

Require Import Wellfounded.
From stdpp Require Import lexico well_founded.

Require Import Program.
From Coq Require Import Logic.Eqdep_dec.

From Equations Require Export Equations.

Lemma eqns_vars_hd_comm
{Σ : BackgroundModel}
(e1 e2 : eqn)
(es : list eqn)
: eqns_vars (e1::e2::es) = eqns_vars (e2::e1::es)
.
Proof.
unfold eqns_vars. simpl. ltac1:(set_solver).
Qed.

Definition wft {Σ : BackgroundModel} (V : gset Variabl) (t : @TermOver' TermSymbol BuiltinOrVar)
: Prop
:= vars_of t ⊆ V
.

Definition wfeqn {Σ : BackgroundModel} (V : gset Variabl) (e : eqn)
: Prop
:=
wft V (e.1) /\ wft V (e.2)
.

Definition wfeqns {Σ : BackgroundModel} (V : gset Variabl) (es : list eqn) : Prop :=
Forall (wfeqn V) es
.

Fixpoint wfsub {Σ : BackgroundModel} (V : gset Variabl) (s : SubS)
: Prop
:=
match s with
| [] => True
| (x,t)::s' =>
    x ∈ V /\ wft (V ∖ {[x]}) t  /\ wfsub (V ∖ {[x]}) (s')
end
.

Fixpoint vars_of_sub {Σ : BackgroundModel} (s : SubS) : gset Variabl
:=
match s with
| [] => ∅
| (x,_)::s' => {[x]} ∪ vars_of_sub s'
end
.

Lemma wf_concat {Σ : BackgroundModel} (V : gset Variabl) (s1 s2 : SubS)
:
wfsub V s1 ->
wfsub (V ∖ (vars_of_sub s1)) s2 ->
wfsub V (s1 ++ s2)
.
Proof.
revert V.
induction s1; intros V HH1 HH2; simpl in *.
{
    rewrite difference_empty_L in HH2.
    exact HH2.
}
{
    destruct a; simpl in *.
    destruct HH1 as [HH11 [HH12 HH13]].
    split.
    { exact HH11. }
    split.
    {
    exact HH12.
    }
    {
    apply IHs1.
    { exact HH13. }
    { 
        ltac1:(replace (V ∖ {[v]} ∖ vars_of_sub s1) with (V ∖ ({[v]} ∪ vars_of_sub s1)) by set_solver).
        exact HH2.
    }
    }
}
Qed.

Definition sub_lt {Σ : BackgroundModel} (s1 s2 : SubS) :=
∃ s3, s1 = s2 ++ s3
.

Lemma on_distinct_vars {Σ : BackgroundModel} (a1 a2 : Variabl) (V : gset Variabl):
a1 ∈ V ->
a1 <> a2 ->
a1 ∈ (V ∖ {[a2]})
.
Proof.
intros HH1 HH2.
ltac1:(set_solver).
Qed.

Lemma wft_minus {Σ : BackgroundModel} (V : gset Variabl) (t : @TermOver' TermSymbol BuiltinOrVar) (a : Variabl) :
wft V t ->
a ∉ vars_of t ->
wft (V ∖ {[a]}) t
.
Proof.
ltac1:(induction t using TermOver_rect); intros HH1 HH2.
{
    simpl in HH2.
    destruct a0; simpl in *.
    {
    unfold wft. unfold vars_of; simpl. unfold vars_of; simpl.
    apply empty_subseteq.
    }
    {
    unfold wft. unfold vars_of; simpl. unfold vars_of; simpl.
    unfold wft in HH1. unfold vars_of in HH1; simpl in HH1. unfold vars_of in HH1; simpl in HH1.
    ltac1:(rewrite singleton_subseteq_l in HH1).
    ltac1:(rewrite singleton_subseteq_l).
    unfold vars_of in HH2; simpl in HH2.
    unfold vars_of in HH2; simpl in HH2.
    ltac1:(set_solver).
    }
}
{
    simpl in *. unfold wft in HH1; simpl in HH1.
    unfold wft; simpl.
    unfold vars_of in HH1; simpl in HH1.
    unfold vars_of; simpl.
    revert HH1 HH2 H.
    induction l; intros HH1 HH2 H.
    {
    simpl. apply empty_subseteq.
    }
    {
    simpl. rewrite union_subseteq.
    split.
    {
        ltac1:(set_solver).
    }
    {
        ltac1:(set_solver).
    }
    }
}
Qed.

Fixpoint is_unifier_of
{Σ : BackgroundModel}
(s : SubS)
(es : list eqn)
:=
match es with
| [] => True
| (t1,t2)::es' => (subs_app s t1 = subs_app s t2) /\ is_unifier_of s es'
end
.

(* Here I strengten the 'least_of' .... *)
Definition least_of
{Σ : BackgroundModel}
(s : SubS)
(es : list eqn)
:=
∀ s', is_unifier_of s' es /\ subs_is_normal s' ->
∃ s1, 
    subs_is_normal s1 /\
    ∀ x, subs_app s' (t_over (bov_Variabl x)) = subs_app (s ++ s1) (t_over (bov_Variabl x))
.



Lemma helper_lemma_2
{Σ : BackgroundModel}
(x : Variabl)
(t : @TermOver' TermSymbol BuiltinOrVar)
(es : list eqn)
(s : SubS)
:
subs_app s (t_over (bov_Variabl x)) = subs_app s t ->
is_unifier_of s es ->
is_unifier_of s (sub t x es)
.
Proof.
revert x t s.
induction es; intros x t ss HH1 HH2; simpl in *.
{ exact I. }
{
    destruct a; simpl in *.
    destruct HH2 as [HH2 HH3].
    split.
    {
    rewrite <- helper_lemma_1>[|assumption].
    rewrite <- helper_lemma_1>[|assumption].
    exact HH2.
    }
    {
    apply IHes; assumption.
    }
}
Qed.

Definition sub_ext
{Σ : BackgroundModel}
(ss : SubS)
(es : list eqn)
:=
(fun e => (subs_app ss e.1, subs_app ss e.2)) <$> es
.


Lemma sub_ext_nil
{Σ : BackgroundModel }
(es : list eqn)
:
sub_ext nil es = es 
.
Proof.
induction es; simpl.
{ reflexivity. }
{
    rewrite IHes. destruct a. reflexivity.
}
Qed.

Lemma sub_ext_cons
{Σ : BackgroundModel}
(ss : SubS)
x t
(es : list eqn)
:
sub_ext ((x, t)::ss) es = sub_ext ss (sub t x es)
.
Proof.
induction es; simpl.
{ reflexivity. }
{
    destruct a; simpl.
    rewrite IHes. reflexivity.
}
Qed.


Lemma least_of_nil_nil
    {Σ : BackgroundModel}
:
    least_of [] []
.
Proof.
    unfold least_of.
    intros s' [Hs'1 Hs'2].
    exists s'. simpl.
    split.
    { exact Hs'2. }
    { intros x. reflexivity. }
Qed.

(* Maybe I can make the relation is_unifier_of such that
the unifier may map only Variabls that occur somewhere in the relation?
*)
Lemma is_unifier_of_cons
{Σ : BackgroundModel}
(ss : SubS)
(es : list eqn)
x t
: 
is_unifier_of ss (sub t x es) ->
is_unifier_of ((x,t)::ss) es
.
Proof.
revert ss.
induction es; simpl; intros ss HH.
{ exact I. }
{
    destruct a; simpl in *.
    destruct HH as [HH1 HH2].
    specialize (IHes _ HH2).
    rewrite HH1.
    split>[reflexivity|].
    exact IHes.
}
Qed.

Lemma unify_no_Variabl_out_of_thin_air
{Σ : BackgroundModel}
(es : list eqn)
(ss : SubS)
:
unify es = Some ss ->
(list_to_set (fmap fst ss)) ∪ (⋃ (fmap (vars_of ∘ snd) ss)) ⊆ eqns_vars es
.
Proof.
revert ss.
ltac1:(funelim (unify es)); intros ss HH.
{
    ltac1:(simp unify in HH).
    inversion HH; subst; clear HH.
    simpl.
    ltac1:(set_solver).
}
{
    clear Heq. inversion e; subst; clear e.
    eapply transitivity.
    { eapply H. ltac1:(congruence). }
    rewrite eqns_vars_cons.
    ltac1:(set_solver).
}
{
    ltac1:(congruence).
}
{
    ltac1:(congruence).
}
{
    rewrite bind_Some in HH.
    destruct HH as [x0 [H1x0 H2x0]].
    (* rewrite HH in Heqcall. *)
    (* rewrite bind_Some in Heqcall. *)
    (* destruct Heqcall as [x0 [H1x0 H2x0]]. *)
    inversion H2x0; subst; clear H2x0.
    clear Heq.
    repeat (rewrite fmap_cons).
    rewrite list_to_set_cons.
    rewrite eqns_vars_cons.
    ltac1:(rewrite ![((_).*1)]/=).
    ltac1:(rewrite ![((_).1)]/=).
    ltac1:(rewrite ![((_).2)]/=).
    ltac1:(rewrite !vars_of_builtin).
    ltac1:(rewrite !vars_of_Variabl).
    rewrite union_list_cons.
    unfold compose at 1.
    ltac1:(rewrite ![((_).2)]/=).
    ltac1:(rewrite !vars_of_builtin).
    specialize (H _ H1x0).
    destruct (decide (x ∈ eqns_vars es)).
    {
    rewrite eqns_vars_sub in H>[|assumption].
    ltac1:(rewrite vars_of_builtin in H).
    ltac1:(set_solver).
    }
    {
    rewrite sub_notin in H>[|assumption].
    ltac1:(set_solver).
    }
}
{
    ltac1:(simplify_eq/=).
}
{
    ltac1:(simp unify in HH).
    unfold unify_unfold_clause_6_1 in HH.
    (* rewrite Heq in HH. *)
    inversion HH.
}
{
    ltac1:(congruence).
}
{
    rewrite HH in Heqcall.
    rewrite bind_Some in HH.
    destruct HH as [x0 [H1x0 H2x0]].

    inversion H2x0; subst; clear H2x0.
    clear Heq.
    ltac1:(rewrite !fmap_cons).
    ltac1:(rewrite !union_list_cons).
    ltac1:(rewrite !list_to_set_cons).
    ltac1:(rewrite !eqns_vars_cons).
    unfold compose at 1.
    ltac1:(rewrite ![((_).*1)]/=).
    ltac1:(rewrite ![((_).1)]/=).
    ltac1:(rewrite ![((_).2)]/=).
    ltac1:(rewrite !vars_of_builtin).
    ltac1:(rewrite !vars_of_Variabl).
    specialize (H _ H1x0).
    destruct (decide (x ∈ eqns_vars es)).
    {
    rewrite eqns_vars_sub in H>[|assumption].
    ltac1:(rewrite vars_of_builtin in H).
    ltac1:(set_solver).
    }
    {
    rewrite sub_notin in H>[|assumption].
    ltac1:(set_solver).
    }
}
{
    clear Heq. subst.
    eapply transitivity.
    { apply H. ltac1:(congruence). }
    rewrite eqns_vars_cons.
    ltac1:(set_solver).
}
{
    (* rewrite HH in HH. *)
    rewrite bind_Some in HH.
    destruct HH as [x0 [H1x0 H2x0]].

    inversion H2x0; subst; clear H2x0.
    clear Heq.
    ltac1:(rewrite !fmap_cons).
    rewrite list_to_set_cons.
    rewrite eqns_vars_cons.
    unfold compose at 1.
    ltac1:(rewrite ![((_).*1)]/=).
    ltac1:(rewrite ![((_).1)]/=).
    ltac1:(rewrite ![((_).2)]/=).
    ltac1:(rewrite !vars_of_Variabl).
    rewrite union_list_cons.
    specialize (H _ H1x0).
    destruct (decide (x ∈ eqns_vars es)).
    {
    rewrite eqns_vars_sub in H>[|assumption].
    ltac1:(rewrite vars_of_Variabl in H).
    ltac1:(set_solver).
    }
    {
    rewrite sub_notin in H>[|assumption].
    ltac1:(set_solver).
    }
}
{
    ltac1:(congruence).
}
{
    (* rewrite HH in Heqcall. *)
    rewrite bind_Some in HH.
    destruct HH as [x0 [H1x0 H2x0]].
    inversion H2x0; subst; clear H2x0.
    rewrite fmap_cons.
    rewrite list_to_set_cons.
    rewrite eqns_vars_cons.
    simpl.
    ltac1:(rewrite vars_of_Variabl).
    specialize (H _ H1x0).

    destruct (decide (x ∈ eqns_vars es)).
    {
    rewrite eqns_vars_sub in H>[|assumption].
    ltac1:(set_solver).
    }
    {
    rewrite sub_notin in H>[|assumption].
    ltac1:(set_solver).
    }
}
{
    ltac1:(simplify_eq/=).
}
{
    ltac1:(simp unify in HH). 
    (* rewrite Heq in HH. *)
    simpl in HH.
    inversion HH.
}
{
    ltac1:(congruence).
}
{
    (* rewrite HH in Heqcall. *)
    rewrite bind_Some in HH.
    destruct HH as [x0 [H1x0 H2x0]].
    inversion H2x0; subst; clear H2x0.
    specialize (H _ H1x0).
    rewrite fmap_cons.
    rewrite list_to_set_cons.
    rewrite eqns_vars_cons.
    simpl.
    ltac1:(rewrite vars_of_Variabl).
        destruct (decide (x ∈ eqns_vars es)).
    {
    rewrite eqns_vars_sub in H>[|assumption].
    ltac1:(set_solver).
    }
    {
    rewrite sub_notin in H>[|assumption].
    ltac1:(set_solver).
    }
}
{
    clear Heq.
    destruct a as [HH1 HH2].
    subst.
    rewrite eqns_vars_cons.
    simpl.
    (* rewrite HH in Heqcall. *)
    specialize (H _ HH).
    ltac1:(rewrite eqns_vars_app in H).
    ltac1:(rewrite eqns_vars_zip in H)>[assumption|].
    ltac1:(rewrite 2!vars_of_t_term).
    exact H.
}
{
    ltac1:(congruence).
}
Qed.

Lemma subs_app_unbound_var_1
{Σ : BackgroundModel}
(ss : SubS)
(x : Variabl)
:
x ∉ ss.*1 ->
subs_app ss (t_over (bov_Variabl x)) = (t_over (bov_Variabl x))
.
Proof.
induction ss; intros HH.
{
    simpl. reflexivity.
}
{
    simpl in HH. specialize(IHss ltac:(set_solver)).
    simpl.
    destruct a; simpl in *.
    destruct (decide (v = x)).
    {
    subst. ltac1:(exfalso). ltac1:(set_solver).
    }
    {
    exact IHss.
    }
}
Qed.

Lemma subs_app_unbound_var_2
{Σ : BackgroundModel}
(ss : SubS)
(x : Variabl)
:
x ∉ ⋃ (vars_of <$> ss.*2) ->
forall (t : @TermOver' TermSymbol BuiltinOrVar),
x ∉ vars_of t ->
x ∉ vars_of (subs_app ss t)
.
Proof.
revert x .
induction ss; intros x HH1 t HH2.
{
    simpl. exact HH2.
}
{
    rewrite fmap_cons in HH1.
    rewrite fmap_cons in HH1.
    simpl.
    destruct a; simpl in *.
    apply IHss.
    { ltac1:(set_solver). }
    destruct (decide (v ∈ vars_of t)).
    {
    ltac1:(rewrite vars_of_TermOverBoV_subst).
    { assumption. }
    { ltac1:(set_solver). }
    }
    {
    rewrite subst_notin2.
    { assumption. }
    { assumption. }
    }
}
Qed.

Lemma is_unifier_of_app
{Σ : BackgroundModel}
u es1 es2
:
is_unifier_of u (es1 ++ es2) <->
(is_unifier_of u es1 /\ is_unifier_of u es2)
.
Proof.
induction es1.
{
    simpl. ltac1:(naive_solver).
}
{
    simpl. destruct a. simpl in *.
    ltac1:(naive_solver).
}
Qed.


Inductive unify_failure {Σ : BackgroundModel} : list eqn -> Prop :=
| uf_varin_fail_1  : forall x t es,
x ∈ vars_of t ->
t <> (t_over (bov_Variabl x)) ->
unify_failure (((t_over (bov_Variabl x)), t) :: es)

| uf_varin_fail_2  : forall x t es,
x ∈ vars_of t ->
t <> (t_over (bov_Variabl x)) ->
unify_failure ((t, (t_over (bov_Variabl x))) :: es)

| uf_diff_builtin : forall b1 b2 es,
b1 <> b2 ->
unify_failure (((t_over (bov_builtin b1)),(t_over (bov_builtin b2))) :: es)

| uf_over_term : forall b s l es,
unify_failure (((t_over (bov_builtin b)),(t_term s l))::es)

| uf_term_over : forall b s l es,
unify_failure (((t_term s l), (t_over (bov_builtin b)))::es)

| uf_term_sym : forall s1 s2 l1 l2 es,
s1 <> s2 ->
unify_failure (((t_term s1 l1),(t_term s2 l2))::es)

| uf_term_len : forall s1 s2 l1 l2 es,
length l1 <> length l2 ->
unify_failure (((t_term s1 l1),(t_term s2 l2))::es)

(*
| uf_subterm : forall es (s : TermSymbol) (l1 l2 : list (@TermOver' TermSymbol BuiltinOrVar)) (idx : nat) (t1 t2 : @TermOver' TermSymbol BuiltinOrVar),
l1 !! idx = Some t1 ->
l2 !! idx = Some t2 ->
unify_failure ((t1,t2)::(drop (S idx) (zip l1 l2))++es) ->
unify_failure (((t_term s l1),(t_term s l2))::es)
*)

| uf_subterm : forall es (s : TermSymbol) (l1 l2 : list (@TermOver' TermSymbol BuiltinOrVar)) (idx : nat),
unify_failure ((take idx (zip l1 l2))++es) ->
unify_failure (((t_term s l1),(t_term s l2))::es)

| uf_rec : forall es t1 t2,
unify_failure es ->
unify_failure ((t1,t2)::es)

| uf_rec_sub2_l : forall es x t,
unify_failure (sub t x es) ->
unify_failure ((t_over (bov_Variabl x),t)::es)

| uf_rec_sub2_r : forall es x t,
unify_failure (sub t x es) ->
unify_failure ((t, t_over (bov_Variabl x))::es)
(*
| uf_rec_sub : forall es t1 t2 ss,
unify_failure (sub_ext ss es) ->
unify_failure ((t1,t2)::es)
*)
.

(*
Lemma unify_some_not_failure
{Σ : BackgroundModel}
(es : list eqn)
(u : SubS)
:
unify es = Some u ->
~ (unify_failure es)
.
Proof.
ltac1:(funelim (unify es)); intros HH HContra;
    ltac1:(simplify_eq/=); try ltac1:(congruence).
{
    inversion HContra.
}
{
    rewrite <- Heqcall in HH.
    specialize (H _ HH).
    apply H. clear H HH Heqcall Heq.
    inversion HContra; ltac1:(simplify_eq/=).
    assumption.
}
{
    rewrite <- Heqcall in HH. clear Heqcall.
    rewrite bind_Some in HH.
    destruct HH as [rest [H1rest H2rest]].
    ltac1:(simplify_eq/=).
    specialize (H _ H1rest).
    apply H. clear H.
    inversion HContra; ltac1:(simplify_eq/=).
    assumption.
}
Qed.*)


Lemma unify_sound
{Σ : BackgroundModel}
(es : list eqn)
:
match unify es with
| None => True
| Some ss =>
    (is_unifier_of ss es /\ least_of ss es /\ subs_is_normal ss)
end
.
Proof.
ltac1:(funelim(unify es)).
{
    simpl in *.
    ltac1:(simp unify). repeat split.
    apply least_of_nil_nil.
    {
        apply Forall_nil.
        exact I.
    }
}
{
    (* rewrite <- Heqcall. *)
    (destruct (unify es) as [ss|]).
    {
        clear Heq. ltac1:(simplify_eq/=).
        repeat split.
        {
            
            apply H.
        }
        {
            unfold least_of.
            intros s' Hs'.
            simpl in Hs'.
            destruct Hs' as [[Hs'0 Hs'1] Hs'2].
            destruct H as [H1 [H2 Hnormal]].
            unfold least_of in H2.
            specialize (H2 s').
            ltac1:(ospecialize (H2 _)).
            {
                split.
                { exact Hs'1. }
                { exact Hs'2. }
            }
            destruct H2 as [s1 Hs1].
            destruct Hs1 as [Hs1' Hs1].
            exists s1.
            split.
            {
                exact Hs1'.
            }
            {
                intros x.
                specialize (Hs1 x).
                rewrite Hs1.
                reflexivity.
            }
        }
        {
            destruct H as [? [? Hthis]].
            exact Hthis.
        }
    }
    {
        apply H.
    }
}
{
    (* rewrite <- Heqcall. *)
    exact I.
}
{
    (* rewrite <- Heqcall.  *)
    clear Heqcall.
    exact I.
}
{
    (* rewrite <- Heqcall.  *)
    clear Heqcall.
    simpl.
    ltac1:( repeat (case_match; simpl in *; simplify_eq/=)).
    {
        repeat split.
        {
            destruct H as [H2 H3]. clear H1 e.
            apply is_unifier_of_cons. exact H2.
        }
        {
            destruct H as [H2 [H3 Hnorm]].
            clear H1 e.
            intros sss Hsss.
            specialize (H3 sss).
            ltac1:(ospecialize (H3 _)).
            {
                split.
                {
                    apply helper_lemma_2.
                    {
                        simpl in Hsss.
                        destruct Hsss as [Hsss1 Hsss2].
                        symmetry.
                        apply Hsss1.
                    }
                    {
                        simpl in Hsss. apply Hsss.
                    }
                }
                {
                    destruct Hsss as [? Hsss].
                    apply Hsss.
                }
            }
            destruct H3 as [s1 Hs1]. simpl in *.
            destruct Hsss as [Hsss1 Hsss2].
            destruct Hs1 as [Hs1' Hs1].
            exists s1.
            split.
            {
                exact Hs1'.
            }
            {
                intros x0.
                specialize (Hs1 x0).
                rewrite subs_app_app in Hs1.
                rewrite subs_app_app.
                destruct (decide (x = x0))>[|auto].
                subst.
                rewrite subs_app_builtin.
                rewrite subs_app_builtin in Hsss1.
                rewrite subs_app_builtin.
                destruct Hsss1 as [? ?].
                ltac1:(congruence).
            }
        }
        {
            destruct H as [H2 [H3 Hnorm]].
            unfold subs_is_normal.
            rewrite Forall_cons.
            split.
            {
                simpl.
                ltac1:(discriminate).
            }
            {
                apply Hnorm.
            }
        }
    }
    {
        apply H.
    }
}
{
    ltac1:(simplify_eq/=).
}
{
    ltac1:(repeat case_match; simplify_eq/=).
    exact I.
}
{
    exact I.
}
{
    (* rewrite <- Heqcall.  *)
    clear Heqcall. simpl.
    ltac1:(repeat (case_match; simplify_eq/=)).
    {
        clear e H1.
        destruct H as [H1 [H2 Hnorm]].
        repeat split.
        {
            simpl.
            apply is_unifier_of_cons. assumption.
        }
        {
            intros ss Hss. specialize (H2 ss).
            ltac1:(ospecialize (H2 _)).
            {
                simpl in Hss.
                destruct Hss as [[Hsss0 Hss1] Hss2].
                split.
                {
                    eapply helper_lemma_2; assumption.
                }
                {
                    assumption.
                }
            }
            {
                destruct H2 as [s1 Hs1].
                destruct Hs1 as [Hs1' Hs1].
                exists s1.
                split.
                {
                    exact Hs1'.
                }
                {
                    intros x0. rewrite Hs1. simpl.
                    destruct (decide (x = x0))>[|reflexivity].
                    subst. simpl in Hss.
                    destruct Hss as [Hss1 Hss2].
                    do 2 (rewrite subs_app_app).
                    assert (Hs1x0 := Hs1 x0).
                    (rewrite subs_app_app in Hs1x0).
                    rewrite <- Hs1x0.
                    rewrite subs_app_builtin.
                    rewrite subs_app_builtin.
                    rewrite subs_app_builtin in Hss1.
                    apply Hss1.
                }
            }
        }
        {
            unfold subs_is_normal.
            rewrite Forall_cons.
            split.
            {
                simpl.
                ltac1:(discriminate).
            }
            {
                apply Hnorm.
            }
        }
    }
    {
        exact H.
    }
}
{
    (* rewrite <- Heqcall. *)
    clear Heqcall.
    ltac1:(repeat (case_match; simplify_eq/=; try assumption)).
    destruct H as [H1 [H2 Hnorm]].
    repeat split.
    { assumption. }
    {
        intros ss Hss.
        specialize (H2 ss).
        ltac1:(ospecialize (H2 _)).
        {
            simpl in Hss.
            destruct Hss as [[H3 H4] H5].
            split; assumption.
        }
        destruct H2 as [s1 Hs1].
        destruct Hs1 as [Hs1' Hs1].
        exists s1.
        split.
        {
            exact Hs1'.
        }
        {
            intros x.
            rewrite Hs1.
            reflexivity.
        }
    }
    {
        exact Hnorm.
    }
}
{
    (* rewrite <- Heqcall.  *)
    ltac1:(simp unify in Heqcall).
    unfold unify_unfold_clause_2 in Heqcall.
    clear Heqcall.
    clear HH.
    ltac1:(repeat (case_match; simpl in *; simplify_eq/=)).
    clear e H1 Heq n0 H2.
    destruct H as [HH1 [HH2 Hnorm]].
    (repeat split).
    {
        apply is_unifier_of_cons.
        apply HH1.
    }
    {
        intros ss Hss.
        specialize (HH2 ss).
        ltac1:(ospecialize (HH2 _)).
        {
            simpl in Hss.
            destruct Hss as [[Hss0 Hss1] Hss2].
            split.
            {
                eapply helper_lemma_2.
                { apply Hss0. }
                exact Hss1.
            }
            {
                apply Hss2.
            }
        }
        destruct HH2 as [s1 Hs1].
        destruct Hs1 as [Hs1' Hs1].
        exists s1.
        split.
        {
            exact Hs1'.
        }
        {
            intros x0.
            simpl.
            simpl in Hss.
            destruct Hss as [Hss1 Hss2].
            destruct (decide (x = x0)).
            {
                subst.
                rewrite <- Hs1.
                apply Hss1.
            }
            {
                subst.
                rewrite <- Hs1.
                reflexivity.
            }
        }
    }
    {
        unfold subs_is_normal.
        rewrite Forall_cons.
        split.
        {
            simpl.
            ltac1:(congruence).
        }
        {
            exact Hnorm.
        }
    }
    { exact I. }
}
{
    (* rewrite <- Heqcall.  *)
    clear Heqcall. simpl.
    exact I.
}
{
    (* rewrite <- Heqcall.  *)
    clear Heqcall. simpl.
    clear Heq.
    clear HH.
    ltac1:(repeat (case_match; simpl in *; simplify_eq/=)).
    {
        clear e H1.
        destruct H as [HH1 [HH2 Hnorm]].
        rewrite subs_app_term.
        rewrite subs_app_term.
        simpl.
        (repeat split).
        {
            apply f_equal.
            apply list_eq.
            intros i.
            rewrite list_lookup_fmap.
            rewrite list_lookup_fmap.
            ltac1:(replace (map) with (@fmap list list_fmap) by reflexivity).
            rewrite list_lookup_fmap.
            ltac1:(destruct (l0 !! i) eqn:Hl0i).
            {
            (* ltac1:(rewrite Hl0i). *)
                simpl.
                apply f_equal.
                rewrite subst_notin2.
                { reflexivity. }
                {
                    intros HContra.
                    apply n. clear n.
                    apply take_drop_middle in Hl0i.            
                    rewrite <- Hl0i.
                    rewrite vars_of_t_term.
                    rewrite fmap_app.
                    rewrite union_list_app_L.
                    simpl.
                    rewrite elem_of_union.
                    clear -HContra.
                    ltac1:(set_solver).
                }
            }
            {
                (* ltac1:(rewrite Hl0i). *)
                simpl.
                reflexivity.
            }
        }
        {
            apply is_unifier_of_cons.
            apply HH1.
        }
        {
            assert (Hnoota := unify_no_Variabl_out_of_thin_air _ _ H0).
            intros u Hu.
            unfold least_of in HH2.

            destruct Hu as [H1u H2u].
            assert (HH21 := HH2 l).
            ltac1:(ospecialize (HH21 _)).
            {
                split.
                { apply HH1. }
                { exact Hnorm. }
            }
            simpl in H1u.
            destruct H1u as [Hu1 Hu2].
            (*
            destruct HH21 as [s1 Hs1].
            *)

            assert(HH2u := HH2 u).
            ltac1:(ospecialize (HH2u _)).
            {
                split.
                {
                    apply helper_lemma_2.
                    apply Hu1.
                    exact Hu2.
                }
                {
                    exact H2u.
                }
            }
            destruct HH2u as [s1 Hs1].
            
            destruct Hs1 as [Hs1' Hs1].
            exists (s1).
            split.
            {
                exact Hs1'.
            }
            {
                intros x0.
                ltac1:(rename s1 into r).
                (*rewrite subs_app_app.*)

                assert (Hunb := subs_app_unbound_var_2 l x).
                ltac1:(ospecialize (Hunb _)).
                {
                rewrite list_fmap_compose in Hnoota.
                destruct (decide (x ∈ eqns_vars es)).
                {
                    rewrite eqns_vars_sub in Hnoota>[|assumption].
                    ltac1:(set_solver).
                }
                {
                    rewrite sub_notin in Hnoota>[|assumption].
                    ltac1:(set_solver).
                }
                }
                assert (Hunb1 := Hunb _ n).
                
                simpl.

                (* [l] does not contain [x] on its lhs *)
                assert (Hnlx : x ∉ l.*1).
                {
                destruct (decide (x ∈ eqns_vars es)) as [Hin2|Hnotin2].
                {
                    rewrite eqns_vars_sub in Hnoota>[|exact Hin2].
                    ltac1:(set_solver).
                }
                {
                    rewrite sub_notin in Hnoota>[|exact Hnotin2].
                    ltac1:(set_solver).
                }
                }
                destruct (decide (x = x0)).
                {
                    subst. ltac1:(rename x0 into x).
                    apply subs_app_unbound_var_1 in Hnlx as Hnlx'.
                    eapply helper_lemma_3 in Hs1 as Hs1''.
                    rewrite <- Hs1''. clear Hs1''.
                    exact Hu1.
                }
                {
                    apply Hs1.
                }
            }
        }
        {
            unfold subs_is_normal.
            rewrite Forall_cons.
            split.
            {
                simpl.
                ltac1:(discriminate).
            }
            {
                exact Hnorm.
            }
        }
    }
{
    exact H.
}
}
{
    ltac1:(simplify_eq/=).
}
{
    ltac1:(simp unify).
    unfold unify_unfold_clause_6_2.
    (* rewrite Heq. *)
    exact I.
}
{
    (* rewrite <- Heqcall. *)
    exact I.
}
{
    (* rewrite <- Heqcall.  *)
    clear Heqcall.
    
    clear HH.
    destruct (unify (sub (t_term s l0) x es)) as [Hr |].
    {
        simpl.
        destruct H as [HH1 [HH2 Hnorm]].
        destruct (decide (x = x))>[|ltac1:(congruence)].
        (repeat split).
        {
            f_equal.
            f_equal.
            apply list_eq.
            intros i.
            ltac1:(replace (map) with (@fmap _ list_fmap) by reflexivity).
            rewrite list_lookup_fmap.
            destruct (l0 !! i) eqn:Heqt.
            {
                (* ltac1:(rewrite Heqt). *)
                simpl.
                apply f_equal.
                rewrite subst_notin2.
                { reflexivity. }
                intros HContra.
                apply n. clear n Heq.
                rewrite vars_of_t_term.
                apply take_drop_middle in Heqt.
                rewrite <- Heqt.
                rewrite fmap_app.
                rewrite union_list_app.
                rewrite fmap_cons.
                simpl.
                ltac1:(set_solver).
            }
            {
                (* ltac1:(rewrite Heqt). *)
                reflexivity.
            }
        }
        {
            clear e.
            apply is_unifier_of_cons.
            exact HH1.
        }
        {
            clear e.
            intros u Hu.
            simpl in Hu.
            destruct Hu as [[Hu1 Hu2] Hu3].
            specialize (HH2 u).
            ltac1:(ospecialize (HH2 _)).
            {
                split.
                {
                    apply helper_lemma_2.
                    symmetry. apply Hu1. apply Hu2.
                }
                {
                    exact Hu3.
                }
            }
            destruct HH2 as [rest Hrest].
            destruct Hrest as [H0rest Hrest].
            exists rest.
            split.
            {
                exact H0rest.
            }
            {
                intros x0.
                simpl.
                destruct (decide (x = x0)).
                {
                    subst.
                    ltac1:(rename x0 into x).
                    eapply helper_lemma_3 in Hrest as Hrest1.
                    rewrite <- Hrest1. clear Hrest1.
                    symmetry. apply Hu1.
                }
                {
                    eapply helper_lemma_3 in Hrest as Hrest1.
                    rewrite <- Hrest1. clear Hrest1.
                    reflexivity.
                }
            }
        }
        {
            unfold subs_is_normal.
            rewrite Forall_cons.
            split.
            {
                simpl.
                ltac1:(discriminate).
            }
            {
                apply Hnorm.
            }

        }
    }
    {
        simpl. exact H.
    }
}
{
    destruct a as [HH1 HH2].
    clear Heq.
    (* rewrite <- Heqcall. *)
    destruct (unify (zip l1 l2 ++ es)) eqn:Heq2.
    {
        subst.
        destruct H as [HH3 [HH4 Hnorm]].
        simpl.
        repeat split.
        {
            rewrite is_unifier_of_app in HH3.
            destruct HH3 as [HH31 HH32].
            rewrite subs_app_term.
            rewrite subs_app_term.
            f_equal.
            apply list_eq.
            intros i.
            rewrite list_lookup_fmap.
            rewrite list_lookup_fmap.
            destruct (l1!!i) eqn:Hl1i.
            {
                (* ltac1:(rewrite Hl1i). *)
                destruct (l2!!i) eqn:Hl2i.
                {
                    (* ltac1:(rewrite Hl2i). *)
                    simpl.
                    f_equal.
                    remember (zip l1 l2) as z.
                    destruct (z !! i) eqn:Hzi.
                    {
                        apply take_drop_middle in Hzi as Hzi'.
                        rewrite <- Hzi' in HH31.
                        rewrite is_unifier_of_app in HH31.
                        simpl in HH31.
                        destruct p; simpl in *.
                        destruct HH31 as [HH311 [WHATIWANT HH312]].
                        clear Hzi'.
                        subst z.
                        rewrite lookup_zip_with in Hzi.
                        rewrite Hl1i in Hzi. simpl in Hzi.
                        rewrite Hl2i in Hzi. simpl in Hzi.
                        ltac1:(simplify_eq/=).
                        exact WHATIWANT.
                    }
                    {
                        subst z.
                        rewrite lookup_zip_with in Hzi.
                        rewrite bind_None in Hzi.
                        destruct Hzi.
                        {
                            ltac1:(simplify_eq/=).
                        }
                        destruct H as [x [H1x H2x]].
                        rewrite bind_None in H2x.
                        destruct H2x.
                        { ltac1:(simplify_eq/=). }
                        destruct H as [x' [H1x' H2x']].
                        { ltac1:(simplify_eq/=). }
                    }
                }
                {
                    apply lookup_lt_Some in Hl1i.
                    apply lookup_ge_None in Hl2i.
                    ltac1:(lia).
                }
            }
            {
                (* ltac1:(rewrite Hl1i). *)
                simpl.
                destruct (l2 !! i) eqn:Hl2i.
                {
                    apply lookup_lt_Some in Hl2i.
                    apply lookup_ge_None in Hl1i.
                    ltac1:(lia).
                }
                {
                    (* ltac1:(rewrite Hl2i). *)
                    reflexivity.
                }
            }
        }
        {
            rewrite is_unifier_of_app in HH3.
            apply HH3.
        }
        {
            intros u Hu.
            simpl in Hu.
            destruct Hu as [[H1u H2u] Hnorm'].
            specialize (HH4 u).
            rewrite is_unifier_of_app in HH4.
            rewrite subs_app_term in H1u.
            rewrite subs_app_term in H1u.
            inversion H1u; subst; clear H1u.
            ltac1:(ospecialize (HH4 _)).
            {
                split; try assumption.
                clear - H2u HH2 H0.
                revert l2 HH2 H0 H2u.
                induction l1; intros l2 HH2 H0 H2u.
                {
                    destruct l2; simpl in *.
                    { repeat split; exact H2u. }
                    { ltac1:(lia). }
                }
                {
                    simpl in *.
                    destruct l2; simpl in *.
                    {
                        repeat split; exact H2u.
                    }
                    {
                        inversion H0; subst; clear H0.
                        repeat split; try assumption.
                        apply IHl1.
                        { ltac1:(lia). }
                        { apply H2. }
                        { exact H2u. }
                    }
                }
            }
            destruct HH4 as [rest Hrest].
            destruct Hrest as [H0rest Hrest].
            exists rest.
            split.
            {
                exact H0rest.
            }
            {   
                intros x.
                specialize (Hrest x).
                apply Hrest.
            }
        }
        {
            exact Hnorm.
        }
    }
    {
        exact H.
    }
}
{
    (* rewrite <- Heqcall. *)
    exact I.
}
Qed.

Lemma subst_preserves_subterm
{Σ : BackgroundModel}
t1 t2 v:
is_subterm_b t1 t2  ->
forall t,
is_subterm_b (TermOverBoV_subst t1 v t) (TermOverBoV_subst t2 v t)
.
Proof.
revert t1.
induction t2; intros t1 Hsub t; simpl in *.
{
    destruct a; simpl in *.
    {
    ltac1:(repeat case_match; try congruence).
    unfold is_left in *.
    ltac1:(repeat case_match; try congruence).
    clear H Hsub H2.
    ltac1:(simplify_eq/=).
    }
    {
    ltac1:(unfold is_left in *; repeat case_match; simplify_eq/=).
    rewrite H1.
    destruct t; simpl; (ltac1:(unfold is_left in *; (repeat case_match); simplify_eq/=; try congruence)).
    unfold is_left in *.
    ltac1:(repeat case_match;simplify_eq/=; congruence).
    }
}
{
    unfold is_left in *.
    ltac1:(repeat case_match;simplify_eq/=; try congruence).
    ltac1:(apply existsb_exists).
    rewrite Forall_forall in H.
    apply existsb_exists in Hsub.
    destruct Hsub as [t' [H1t' H2t']].
    rewrite <- elem_of_list_In in H1t'.
    assert (H' := H _ H1t' _ H2t' t).
    (*exists t'.*)
    eexists.
    rewrite in_map_iff.
    split>[|apply H'].
    exists t'.
    rewrite <- elem_of_list_In.
    split; try assumption.
    reflexivity.
}
Qed.

Lemma subs_app_preserves_subterm
{Σ : BackgroundModel}
(t1 t2 : @TermOver' TermSymbol BuiltinOrVar)
:
is_subterm_b t1 t2 ->
forall s,
    is_subterm_b (subs_app s t1) (subs_app s t2)
.
Proof.
intros HH1 s.
revert t1 t2 HH1.
induction s; intros t1 t2 HH1.
{
    simpl. exact HH1.
}
{
    simpl.
    destruct a; simpl in *.
    apply IHs.
    apply subst_preserves_subterm.
    exact HH1.
}
Qed.

(*Require Import Coq.Logic.Classical_Prop. *)

Lemma var_is_subterm
{Σ : BackgroundModel}
x t
:
x ∈ vars_of t ->
is_subterm_b (t_over (bov_Variabl x)) t = true
.
Proof.
intros H2X.
induction t; simpl in *.
{
    ltac1:(case_match); try reflexivity.
    destruct a.
    {
    ltac1:(rewrite vars_of_builtin in H2X).
    ltac1:(set_solver).
    }
    {
    unfold is_left in H.
    ltac1:((repeat case_match); try congruence).
    ltac1:(rewrite vars_of_Variabl in H2X).
    rewrite elem_of_singleton in H2X.
    subst.
    ltac1:(exfalso). apply n. reflexivity.
    }
}
{
    rewrite Forall_forall in H.
    ltac1:(rewrite vars_of_t_term in H2X).
    rewrite elem_of_union_list in H2X.
    destruct H2X as [X [H1X H2X]].
    rewrite elem_of_list_fmap in H1X.
    destruct H1X as [y [H1y H2y]].
    subst.
    specialize (H _ H2y H2X).
    rewrite existsb_exists.
    exists y.
    rewrite <- elem_of_list_In.
    split; assumption.
}
Qed.

Lemma is_subterm_size
{Σ : BackgroundModel}
(t1 t2 : @TermOver' TermSymbol BuiltinOrVar)
:
is_subterm_b t1 t2 ->
TermOver_size t1 <= TermOver_size t2
.
Proof.
revert t1.
induction t2; intros t1 HH; simpl in *;
    unfold is_left in *; ltac1:((repeat case_match); simplify_eq/=; try congruence; try lia).
{
    clear H1.
    rewrite Forall_forall in H.
    unfold is_true in HH.
    rewrite existsb_exists in HH.
    destruct HH as [x [H1x H2x]].
    rewrite <- elem_of_list_In in H1x.
    specialize (H _ H1x _ H2x).
    eapply transitivity>[apply H|]. clear H H2x.
    rewrite elem_of_list_lookup in H1x.
    destruct H1x as [i Hi].
    apply take_drop_middle in Hi.
    rewrite <- Hi.
    rewrite sum_list_with_app.
    simpl.
    ltac1:(lia).
}
Qed.

Lemma is_subterm_antisym
{Σ : BackgroundModel}
(t1 t2 : @TermOver' TermSymbol BuiltinOrVar)
:
is_subterm_b t1 t2 ->
is_subterm_b t2 t1 ->
t1 = t2
.
Proof.
destruct t2; simpl in *; unfold is_left in *; ltac1:((repeat case_match); simplify_eq/=; try congruence).
intros HH1 HH2.
apply existsb_exists in HH1.
destruct HH1 as [x [HH11 HH12]].
apply is_subterm_size in HH12.
apply is_subterm_size in HH2.
simpl in HH2.
rewrite <- elem_of_list_In in HH11.
rewrite elem_of_list_lookup in HH11.
destruct HH11 as [i Hi].
apply take_drop_middle in Hi.
rewrite <- Hi in HH2.
rewrite sum_list_with_app in HH2.
simpl in HH2.
ltac1:(lia).
Qed.

Lemma is_unifier_of_extensive
{Σ : BackgroundModel}
(u : SubS)
(es : list eqn)
:
is_unifier_of u es ->
forall rest,
    is_unifier_of (u++rest) es
.
Proof.
    intros.
    induction es.
    {
        simpl. exact I.
    }
    {
        simpl. destruct a as [t1 t2].
        simpl in *.
        destruct H as [HH1 HH2].
        specialize (IHes HH2).
        split>[|apply IHes].
        clear -HH1 HH2.
        induction rest.
        { rewrite app_nil_r. apply HH1.  }
        rewrite subs_app_app in IHrest.
        rewrite subs_app_app in IHrest.
        rewrite subs_app_app.
        rewrite subs_app_app.
        simpl.
        destruct a as [x t].
        ltac1:(congruence).
    }
Qed.

Lemma unify_failure_is_severe
{Σ : BackgroundModel}
(es : list eqn)
:
unify_failure es ->
~ exists s : SubS,
    is_unifier_of s es
.
Proof.
    intros Hfail.
    induction Hfail.
    {
        intros HContra.
        destruct HContra as [s Hs].
        simpl in Hs.
        destruct t; simpl in *.
        {
        destruct a; simpl in *.
        {
            rewrite vars_of_builtin in H.
            ltac1:(set_solver).
        }
        {
            rewrite vars_of_Variabl in H.
            rewrite elem_of_singleton in H.
            subst x0.
            apply H0.
            reflexivity.
        }
        }
        {
        clear H0.
        destruct Hs as [H1s H2s].
        (*
            From H1s it follows that (x,t') ∈ s (for some t')
        *)
        rewrite vars_of_t_term in H.
        rewrite elem_of_union_list in H.
        destruct H as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [t [H1t H2t]].
        subst.

        apply var_is_subterm in H2X as H2X'.
        apply subs_app_preserves_subterm with (s := s) in H2X'.
        apply is_subterm_size in H2X'.
        rewrite H1s in H2X'.
        clear H1s H2s.
        rewrite subs_app_term in H2X'.
        simpl in H2X'.

        rewrite elem_of_list_lookup in H2t.
        destruct H2t as [it Hit].
        apply take_drop_middle in Hit.
        rewrite <- Hit in H2X'.
        rewrite fmap_app in H2X'.
        rewrite fmap_cons in H2X'.
        rewrite sum_list_with_app in H2X'.
        simpl in H2X'.
        ltac1:(lia).
        }
    }
    {
        intros HContra.
        destruct HContra as [s Hs].
        simpl in Hs.
        destruct t; simpl in *.
        {
        destruct a; simpl in *.
        {
            rewrite vars_of_builtin in H.
            ltac1:(set_solver).
        }
        {
            rewrite vars_of_Variabl in H.
            rewrite elem_of_singleton in H.
            subst x0.
            apply H0.
            reflexivity.
        }
        }
        {
        clear H0.
        destruct Hs as [H1s H2s].
        (*
            From H1s it follows that (x,t') ∈ s (for some t')
        *)
        rewrite vars_of_t_term in H.
        rewrite elem_of_union_list in H.
        destruct H as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [t [H1t H2t]].
        subst.

        apply var_is_subterm in H2X as H2X'.
        apply subs_app_preserves_subterm with (s := s) in H2X'.
        apply is_subterm_size in H2X'.
        rewrite <- H1s in H2X'.
        clear H1s H2s.
        rewrite subs_app_term in H2X'.
        simpl in H2X'.

        rewrite elem_of_list_lookup in H2t.
        destruct H2t as [it Hit].
        apply take_drop_middle in Hit.
        rewrite <- Hit in H2X'.
        rewrite fmap_app in H2X'.
        rewrite fmap_cons in H2X'.
        rewrite sum_list_with_app in H2X'.
        simpl in H2X'.
        ltac1:(lia).
        }
    }
    {
        intros [s Hs].
        simpl in Hs.
        destruct Hs as [Hs1 Hs2].
        rewrite subs_app_builtin in Hs1.
        rewrite subs_app_builtin in Hs1.
        ltac1:(simplify_eq/=).
    }
    {
        intros HContra.
        destruct HContra as [s0 [H1s0 H2s0]].
        rewrite subs_app_term in H1s0.
        rewrite subs_app_builtin in H1s0.
        inversion H1s0.
    }
    {
        intros [s0 [H1s0 H2s0]].
        rewrite subs_app_term in H1s0.
        rewrite subs_app_builtin in H1s0.
        inversion H1s0.
    }
    {
        intros [s0 [H1s0 H2s0]].
        rewrite subs_app_term in H1s0.
        rewrite subs_app_term in H1s0.
        ltac1:(simplify_eq/=).
    }
    {
        intros [s0 [H1s0 H2s0]].
        rewrite subs_app_term in H1s0.
        rewrite subs_app_term in H1s0.
        ltac1:(simplify_eq/=).
        apply (f_equal length) in H0.
        rewrite length_fmap in H0.
        rewrite length_fmap in H0.
        ltac1:(simplify_eq/=).
    }
    {
        intros [s0 [H1s0 H2s0]].
        rewrite subs_app_term in H1s0.
        rewrite subs_app_term in H1s0.
        ltac1:(simplify_eq/=).
        apply (f_equal length) in H1s0 as H1s0'.
        rewrite length_fmap in H1s0'.
        rewrite length_fmap in H1s0'.
        apply IHHfail.
        exists s0.
        rewrite is_unifier_of_app.
        split>[|apply H2s0].
        ltac1:(cut(is_unifier_of s0 (zip l1 l2))).
        {
        intros HHH.
        rewrite <- (take_drop idx (zip l1 l2)) in HHH.
        rewrite is_unifier_of_app in HHH.
        apply HHH.
        }
        clear - H1s0.
        revert l2 H1s0.
        induction l1; intros l2 H1s0.
        {
        simpl. exact I.
        }
        {
        simpl.
        destruct l2; simpl in *.
        {
            inversion H1s0.
        }
        inversion H1s0; subst; clear H1s0.
        split>[reflexivity|].
        apply IHl1.
        apply H1.
        }
    }
    {
        intros [s [H1s H2s]].
        apply IHHfail. clear IHHfail.
        exists s.
        exact H2s.
    }
    {
        intros [s [H1s H2s]].
        apply IHHfail. clear IHHfail.
        apply helper_lemma_2 with (es := es) in H1s.
        exists s.
        exact H1s.
        exact H2s.
    }
    {
        intros [s [H1s H2s]].
        apply IHHfail. clear IHHfail.
        symmetry in H1s.
        apply helper_lemma_2 with (es := es) in H1s.
        exists s.
        exact H1s.
        exact H2s.
    }
Qed.

Hint Constructors unify_failure : core.
Lemma unify_sound2
    {Σ : BackgroundModel}
    (es : list eqn)
:
    unify es = None ->
    unify_failure es
.
Proof.
    ltac1:(funelim (unify es)); intros HNone.
    {
        ltac1:(simp unify in HNone).
        inversion HNone.
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        specialize (H HNone).
        solve [eauto].
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        constructor.
        intros HContra.
        ltac1:(simplify_eq/=).
    }
    {
        clear -e.
        rewrite vars_of_builtin in e.
        ltac1:(set_solver).
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        rewrite bind_None in HNone.
        destruct HNone as [HNone|HNone].
        {
            specialize (H HNone).
            solve [eauto].
        }
        {
            destruct HNone as [x0 [H1x0 H2x0]].
            inversion H2x0.
        }
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        specialize (H HNone).
        solve [eauto].
    }
    {
        solve [eauto].
    }
    {
        solve [eauto].
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        rewrite bind_None in HNone.
        destruct HNone as [HNone|HNone].
        {
            specialize (H HNone).
            solve [eauto].
        }
        {
            destruct HNone as [x0 [H1x0 H2x0]].
            inversion H2x0.
        }
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        specialize (H HNone).
        solve [eauto].
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        rewrite bind_None in HNone.
        destruct HNone as [HNone|HNone].
        {
            specialize (H HNone).
            solve [eauto].
        }
        {
            destruct HNone as [x0 [H1x0 H2x0]].
            inversion H2x0.
        }
    }
    {
        solve [eauto].
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        rewrite bind_None in HNone.
        destruct HNone as [HNone|HNone].
        {
            specialize (H HNone).
            solve [eauto].
        }
        {
            destruct HNone as [x0 [H1x0 H2x0]].
            inversion H2x0.
        }
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        specialize (H HNone).
        solve [eauto].
    }
    {
        solve [eauto].
    }
    {
        solve [eauto].
    }
    {
        (* rewrite <- Heqcall in HNone. *)
        rewrite bind_None in HNone.
        destruct HNone as [HNone|HNone].
        {
            specialize (H HNone).
            solve [eauto].
        }
        {
            destruct HNone as [x0 [H1x0 H2x0]].
            inversion H2x0.
        }
    }
    {
        destruct a as [HH1 HH2].
        subst.
        apply uf_subterm with (idx := length (zip l1 l2)).
        rewrite firstn_all.
        apply H.
        ltac1:(congruence).
    }
    {
        clear Heq.
        apply Decidable.not_and in n.
        destruct n; solve [eauto].
        unfold Decidable.decidable.
        destruct (decide (s1 = s2)); auto.
    }
Qed.

Program Definition
    textbook_unification_algorithm
    {Σ : BackgroundModel}
:
    UnificationAlgorithm
:= {|
    ua_unify := fun t1 t2 => make_parallel ∘ reverse <$> (textbook_unification_alg.unify [(t1,t2)]) ;
|}.
Next Obligation.
    assert(Hsound := unify_sound [(t1,t2)]).
    destruct (unify [(t1, t2)]) eqn:Heq.
    {
        apply unify_no_Variabl_out_of_thin_air in Heq as Hnoota.
        destruct Hsound as [Hsound1 [Hsound2 Hnorm]].
        simpl in Hsound1.
        destruct Hsound1 as [Hsound1 _].
        rewrite fmap_Some in H.
        destruct H as [u' [H1u' H2u']].
        ltac1:(simplify_eq/=).
        assert (l = u').
        {
            ltac1:(rewrite Heq in H1u').
            ltac1:(simplify_eq/=).
            reflexivity.
        }
        subst l.
        unfold compose.
        split.
        {
            rewrite make_parallel_correct.
            rewrite make_parallel_correct.
            rewrite reverse_involutive.
            apply Hsound1.
        }
        intros s Hnormal Hsubseteq Hdoms Hs.
        remember (make_serial1 s (vars_of t1 ∪ vars_of t2)) as ser.
        assert (Hser: subs_app ser t1 = subs_app ser t2).
        {
            subst ser.
            rewrite make_serial1_correct.
            {
                rewrite make_serial1_correct.
                {
                    exact Hs.
                }
                {
                    assumption.
                }
                {
                    ltac1:(set_solver).
                }
            }
            {
                assumption.
            }
            {
                ltac1:(set_solver).
            }
        }
        unfold least_of in Hsound2.

        ltac1:(ospecialize (Hsound2 ser _)).
        {
            (repeat split).
            { exact Hser. }
            {
                subst ser.
                apply subs_is_normal_make_serial1.
                {
                    exact Hnormal.
                }
                {
                    exact Hdoms.
                }
            }
        }

        destruct Hsound2 as [s' [H0s' Hs']].
        subst ser.

        (* exists (make_parallel s'). *)


        (* rewrite fst_make_serial1 in H0s'. *)
        (* rewrite list_fmap_compose in H0s'. *)
        assert (Hsms := snd_make_serial1 s (vars_of t1 ∪ vars_of t2)).
        remember (map_img (renaming_for (vars_of t1 ∪ vars_of t2) s)) as X1.
        remember (⋃ (vars_of <$> (make_serial1 s (vars_of t1 ∪ vars_of t2)).*2)) as X2.
        (* When I obtain [s'] and [Hs'], I do not  *)
        assert(H2: forall x, subs_app ((make_serial1 s (vars_of t1 ∪ vars_of t2))) (t_over (bov_Variabl x)) = subp_app (make_parallel (reverse (u' ++ s'))) (t_over (bov_Variabl x))).
        {
            intros x.
            specialize (Hs' x).
            rewrite make_parallel_correct.
            rewrite reverse_involutive.
            exact Hs'.
        }
        clear Hs'.
        remember (vars_of t1 ∪ vars_of t2 ∪ dom (make_parallel (reverse (u' ++ s')))) as d.
        (* the guard is unfortunate, but in principle I could choose arbitrarily big guard that would make it always true *)
        assert(H3: forall x, x ∈ vars_of t1 ∪ vars_of t2 -> subp_app s (t_over (bov_Variabl x)) = subp_app (make_parallel (reverse (u' ++ s'))) (t_over (bov_Variabl x))).
        {
            intros x Hx.
            specialize (H2 x).
            rewrite make_serial1_correct in H2.
            {
                exact H2.
            }
            {
                exact Hdoms.
            }
            {
                clear - Hx.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                ltac1:(set_solver).
            }
        }

        (*I can't add [s'.*1] to the restriction in Hr?
        *)
        assert (Hr := subp_app_restrict_eq (vars_of t1 ∪ vars_of t2  (* ∪ (list_to_set s'.*1) *)) s (make_parallel (reverse (u' ++ s')))).
        specialize (Hr Hnormal).
        ltac1:(ospecialize (Hr _)).
        {
            apply make_parallel_normal. 
        }
        ltac1:(ospecialize (Hr _)).
        {
            exact H3.
        }
        
        unfold eqns_vars,eqn_vars in Hnoota.
        simpl in Hnoota.
        assert (Htmp1: list_to_set u'.*1 ⊆ vars_of t1 ∪ vars_of t2).
        {
            clear - Hnoota H0s'.
            ltac1:(set_solver).
        }
        (*  *)
        
        rewrite reverse_app in Hr.
        rewrite (restrict_id s) in Hr.
        {
            rewrite make_parallel_app in Hr.
            {
                subst s.
                exists (make_parallel (reverse s')).
                reflexivity.            
            }
            {
                unfold subs_is_normal in *.
                assert (s' ≡ₚ reverse s').
                {
                    symmetry.
                    apply reverse_Permutation.
                }
                rewrite <- H.
                apply H0s'.
            }
        }
        {
            clear - Hsubseteq.
            ltac1:(set_solver).
        }
    }
    {
        ltac1:(rewrite Heq in H).
        simpl in H.
        inversion H.
    }
Qed.
Next Obligation.
    assert(Hsound := unify_sound2 [(t1,t2)]).
    ltac1:(ospecialize (Hsound _)).
    {
        rewrite fmap_None in H.
        exact H.
    }
    apply unify_failure_is_severe in Hsound.
    apply Hsound.
    clear Hsound.
    exists (make_serial1 s (vars_of t1 ∪ vars_of t2)).
    repeat split.
    rewrite make_serial1_correct.
    {
        rewrite make_serial1_correct.
        {
            assumption.
        }
        {
            assumption.
        }
        {
            ltac1:(set_solver).
        }
    }
    {
        assumption.
    }
    {
        ltac1:(set_solver).
    }
Qed.

