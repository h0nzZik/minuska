From Minuska Require Import
    prelude
    spec
    termoverbov_subst (* TermOverBoV_subst *)
.

Definition SubS {Σ : StaticModel} : Type
:=
    list (variable*(TermOver BuiltinOrVar))%type
.

Definition subt_closed {Σ : StaticModel} (s : SubS) :=
    forall k v, s !! k = Some v -> vars_of v.2 = ∅
.

(* TODO use fold *)
Fixpoint subs_app {Σ : StaticModel} (s : SubS) (t : TermOver BuiltinOrVar) : TermOver BuiltinOrVar :=
match s with
| [] => t
| (x,t')::s' => subs_app s' (TermOverBoV_subst t x t')
end
.

Lemma subs_app_app
    {Σ : StaticModel}
    (s1 s2 : SubS)
    (t : TermOver BuiltinOrVar)
:
    subs_app (s1 ++ s2) t = subs_app s2 (subs_app s1 t)
.
Proof.
    revert t.
    induction s1; intros t; simpl.
    { reflexivity. }
    {
        destruct a; simpl in *.
        rewrite IHs1. reflexivity.
    }
Qed.

Lemma subs_app_builtin
    {Σ : StaticModel}
    (ss : SubS)
    (b : builtin_value)
:
    subs_app ss (t_over (bov_builtin b)) = t_over (bov_builtin b)
.
Proof.
    induction ss; simpl.
    { reflexivity. }
    {
        destruct a; simpl in *.
        apply IHss.
    }
Qed.

(* WAIT *)
(* Lemma subs_app_nodup
    {Σ : StaticModel}
    (sub : SubS)
    (x y : variable)
    :
    NoDup (fst <$> sub) ->
    (x, t_over (bov_variable y)) ∈ sub ->
    (forall x' p', (x', p') ∈ sub -> ∃ y', p' = t_over (bov_variable y')) ->
    subs_app sub (t_over (bov_variable x)) = t_over (bov_variable y)
.
Proof.
    induction sub; intros HH1 HH2 HH3; simpl in *.
    {
        rewrite elem_of_nil in HH2.
        destruct HH2.
    }
    {
        destruct a as [x' p'].
        simpl in *.
        destruct (decide (x' = x)).
        {
            subst.
            simpl in *.
            fold (@fmap list list_fmap) in *.
            rewrite NoDup_cons in HH1.
            destruct HH1 as [HH4 HH5].
            (* clear IHsub HH3. *)
            rewrite elem_of_cons in HH2.
            destruct HH2 as [HH2|HH2].
            {
                ltac1:(simplify_eq/=).
                (* Need a lemma saying that subs_app does nothing because ... wait... y should not be in sub *)
                rewrite IHsub.
                reflexivity.
            }
        }
    }
Qed. *)
