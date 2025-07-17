From Minuska Require Import
    prelude
    spec
    (* basic_properties *)
    substitution_sequential
    termoverbov_subst
    termoverbov_subst_properties
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

Lemma subs_app_cons
    {Σ : StaticModel}
    x p
    (s2 : SubS)
    (t : TermOver BuiltinOrVar)
:
    subs_app ((x,p)::s2) t = subs_app s2 (subs_app [(x,p)] t)
.
Proof.
    ltac1:(replace ((x,p)::s2) with (([(x,p)])++s2) by reflexivity).
    apply subs_app_app.
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



Lemma subs_app_term
{Σ : StaticModel}
(ss : SubS)
(sym : symbol)
(l : list (TermOver BuiltinOrVar))
:
subs_app ss (t_term sym l) = t_term sym ((subs_app ss) <$> l)
.
Proof.
revert l sym.
induction ss; intros l sym; simpl.
{ f_equal. induction l; simpl; try reflexivity. unfold fmap in IHl. rewrite <- IHl. reflexivity. }
{
    destruct a; simpl.
    rewrite IHss.
    f_equal.
    ltac1:(replace (map) with (@fmap _ list_fmap) by reflexivity).
    rewrite <- list_fmap_compose. reflexivity.
}
Qed.




Lemma helper_lemma_1
{Σ : StaticModel}
(s : SubS)
(x : variable)
(t t' : TermOver BuiltinOrVar)
:
subs_app s (t_over (bov_variable x)) = subs_app s t' ->
subs_app s t = subs_app s  (TermOverBoV_subst t x t')
.
Proof.
revert s.
induction t; simpl; intros ss HH.
{
    revert HH.
    induction ss; intros HH; simpl in *.
    {
    subst t'.
    destruct a; simpl.
    { reflexivity. }
    {
        destruct (decide (x = x0)); simpl; subst; reflexivity.
    }
    }
    {
    destruct a0; simpl in *.
    destruct a; simpl in *.
    { reflexivity. }
    destruct (decide (v = x0)); simpl in *.
    {
        subst.
        destruct (decide (x = x0)); simpl in *.
        {
        subst.
        destruct (decide (x0 = x0))>[|ltac1:(contradiction)].
        inversion HH; subst; clear HH.
        reflexivity.
        }
        {
        destruct (decide (x0 = x))>[ltac1:(subst;contradiction)|].
        destruct (decide (x0 = x0))>[|ltac1:(contradiction)].
        reflexivity.
        }
    }
    {
        destruct (decide (x = x0)); simpl in *.
        {
        subst.
        destruct (decide (v = x0)); simpl in *.
        { subst.
            ltac1:(contradiction n). reflexivity.
        }
        {
            assumption.
        }
        }
        {
        destruct (decide (v = x0))>[subst; ltac1:(contradiction)|].
        reflexivity.
        }
    }
    }
}
{

    rewrite subs_app_term.
    rewrite subs_app_term.
    apply f_equal.
    revert ss HH H.
    induction l; intros ss HH1 HH2.
    { reflexivity. }
    {
    rewrite Forall_cons in HH2.
    destruct HH2 as [HH2 HH3].
    specialize (IHl ss HH1 HH3).
    rewrite fmap_cons.
    rewrite fmap_cons.
    rewrite fmap_cons.
    rewrite IHl.
    specialize (HH2 ss HH1).
    rewrite HH2.
    ltac1:(replace (map) with (@fmap _ list_fmap) by reflexivity).
    reflexivity.
    }
}
Qed.



Lemma helper_lemma_3 {Σ : StaticModel}:
∀ l s1,
(
    ∀ x : variable,
    subs_app l (t_over (bov_variable x)) =
    subs_app (s1) (t_over (bov_variable x))
) ->
∀ t,
    subs_app l t = subs_app (s1) t
.
Proof.
intros l s1 HNice t.
revert l s1 HNice.
induction t; intros ll s1 HNice.
{
    destruct a.
    {
    rewrite subs_app_builtin.
    rewrite subs_app_builtin.
    reflexivity.
    }
    {
    rewrite HNice.
    reflexivity.
    }
}
{
    rewrite subs_app_term.
    rewrite subs_app_term.
    apply f_equal.
    rewrite Forall_forall in H.
    apply list_eq.
    intros i.
    rewrite list_lookup_fmap.
    rewrite list_lookup_fmap.
    destruct (l !! i) eqn:Hli.
    {
    ltac1:(rewrite Hli).
    simpl.
    apply f_equal.
    erewrite H.
    reflexivity.
    rewrite elem_of_list_lookup.
    exists i. exact Hli.
    apply HNice.
    }
    {
    ltac1:(rewrite Hli).
    simpl.
    reflexivity.
    }
}
Qed.

Definition subs_no_twice_approx
    {Σ : StaticModel}
    (subs : SubS)
    : Prop
    :=
    forall x,
        x ∈ (⋃ (vars_of <$> (subs.*2))) ->
        x ∉ (subs.*1)
.


Lemma subs_app_nodup_1
    {Σ : StaticModel}
    (sub : SubS)
    (x : variable)
    :
    NoDup (fst <$> sub) ->
    x ∉ sub.*1 ->
    subs_app sub (t_over (bov_variable x)) = t_over (bov_variable x)
.
Proof.
    induction sub; intros H1 H2; simpl in *.
    {
        reflexivity.
    }
    {
        destruct  a; simpl in *.
        rewrite NoDup_cons in H1.
        destruct H1 as [H3 H4].
        specialize (IHsub H4).
        rewrite elem_of_cons in H2.
        apply Decidable.not_or in H2.
        destruct H2 as [H5 H6].
        rewrite decide_False.
        {
            specialize (IHsub H6).
            apply IHsub.
        }
        {
            ltac1:(congruence).
        }
    }
Qed.

Lemma subs_app_nodup_2
    {Σ : StaticModel}
    (sub : SubS)
    (x y : variable)
    :
    NoDup (fst <$> sub) ->
    subs_no_twice_approx sub ->
    (x, t_over (bov_variable y)) ∈ sub ->
    (forall x' p', (x', p') ∈ sub -> ∃ y', p' = t_over (bov_variable y')) ->
    subs_app sub (t_over (bov_variable x)) = t_over (bov_variable y)
.
Proof.
    intros H1 H2 H3 H4.
    specialize (H4 x (t_over (bov_variable y)) H3).
    destruct H4 as [y' Hy'].
    inversion Hy'; subst; clear Hy'.
    rewrite elem_of_list_lookup in H3.
    destruct H3 as [y Hi].
    apply take_drop_middle in Hi.
    rewrite <- Hi.
    rewrite <- Hi in H1.
    rewrite fmap_app in H1.
    rewrite NoDup_app in H1.
    rewrite fmap_cons in H1.
    rewrite NoDup_cons in H1.
    ltac1:(rewrite subs_app_app).
    simpl.
    destruct H1 as [H3 [H4 [H5 H6]]].
    rewrite subs_app_nodup_1.
    {
        simpl.
        rewrite decide_True.
        {
            rewrite subs_app_nodup_1.
            {
                reflexivity.
            }
            {
                apply H6.
            }
            {
                intros HContra.
                specialize (H2 y').
                rewrite <- Hi in H2.
                ltac1:(ospecialize (H2 _)).
                {
                    rewrite elem_of_union_list.
                    exists ({[y']}).
                    rewrite elem_of_list_fmap.
                    split.
                    {
                        exists (t_over (bov_variable y')).
                        split.
                        {
                            unfold vars_of; simpl.
                            unfold vars_of; simpl.
                            reflexivity.
                        }
                        {
                            rewrite elem_of_list_fmap.
                            exists (x, (t_over (bov_variable y'))).
                            rewrite elem_of_app.
                            split>[reflexivity|].
                            right.
                            rewrite elem_of_cons.
                            left.
                            reflexivity.
                        }
                    }
                    {
                        ltac1:(set_solver).
                    }
                }
                {
                    ltac1:(set_solver).
                }
            }
            
        }
        {
            reflexivity.
        }
    }
    {
        apply H3.
    }
    {
        simpl in *.
        intros HContra.
        specialize (H4 _ HContra).
        ltac1:(set_solver).
    }
Qed.


Lemma subs_app_untouched
    {Σ : StaticModel}
    (s : SubS)
    (φ : TermOver BuiltinOrVar)
    :
    vars_of φ ## (list_to_set s.*1) ->
    subs_app s φ = φ
.
Proof.
    revert φ; induction s; intros φ HH; simpl in *.
    {
        reflexivity.
    }
    {
        destruct a as [y t].
        simpl in *.
        fold (@fmap list list_fmap) in *.
        rewrite subst_notin2.
        {
            apply IHs.
            ltac1:(set_solver).
        }
        {
            ltac1:(set_solver).
        }
    }
Qed.


(* Compute SubS. *)
Definition subt_dom {Σ : StaticModel} (s : list (variable * @TermOver' symbol BuiltinOrVar)) : gset variable :=
    list_to_set (s.*1)
.

Definition subt_codom {Σ : StaticModel} (s : list (variable * @TermOver' symbol BuiltinOrVar)) : gset variable :=
    union_list (vars_of <$> s.*2)
.


Lemma vars_of_subs_app
    {Σ : StaticModel}
    a
    (q : TermOver BuiltinOrVar)
    :
    vars_of (subs_app a q) ⊆ subt_codom a ∪ vars_of q
.
Proof.
    revert q.
    induction a; intros q.
    {
        simpl.
        ltac1:(set_solver).
    }
    {
        simpl.
        destruct a.
        rewrite IHa.
        unfold subt_codom.
        rewrite fmap_cons.
        rewrite fmap_cons.
        simpl.
        destruct (decide (v ∈ vars_of q)) as [Hin|Hnotin].
        {
            assert (Htmp := vars_of_TermOverBoV_subst q t v Hin).
            rewrite Htmp.
            ltac1:(set_solver).
        }
        {
            rewrite subst_notin2.
            {
                ltac1:(set_solver).
            }
            {
                exact Hnotin.
            }
        }
    }
Qed.

