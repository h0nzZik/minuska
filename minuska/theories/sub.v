From Minuska Require Import
    prelude
    spec
    basic_properties
    minusl_syntax
    syntax_properties
    unification_interface
.


  Lemma vars_of_sub_app_sub
    {Σ : StaticModel} (sub : @SubT Σ) x:
    vars_of (sub_app sub x) ⊆ union_list ((@vars_of (TermOver BuiltinOrVar) variable _ _ (VarsOf_TermOver_BuiltinOrVar)) <$> (fmap snd sub)) ∪ (vars_of x)
  .
  Proof.
    revert x;
    induction sub; simpl; intros x.
    {
      ltac1:(set_solver).
    }
    {
      destruct a as [x' t']; simpl in *.
      eapply transitivity. apply IHsub. clear IHsub.
      assert (Htmp2 := vars_of_TermOverBoV_subst__approx).
      unfold fmap; simpl.
      ltac1:(set_solver).
    }
  Qed.

  Lemma vars_of_sub_app_e_sub
    {Σ : StaticModel} (sub : @SubT Σ) x:
    vars_of (sub_app_e sub x) ⊆ union_list ((@vars_of (TermOver BuiltinOrVar) variable _ _ (VarsOf_TermOver_BuiltinOrVar)) <$> (fmap snd sub)) ∪ (vars_of x)
  .
  Proof.
    revert x;
    induction sub; simpl; intros x.
    {
      ltac1:(set_solver).
    }
    {
      destruct a as [x' t']; simpl in *.
      eapply transitivity. apply IHsub. clear IHsub.
      assert (Htmp2 := vars_of_TermOverBoV_subst_e2__approx).
      unfold fmap; simpl.
      ltac1:(set_solver).
    }
  Qed.

  Lemma vars_of_sub_app_sub_3
      {Σ : StaticModel} (sub : @SubT Σ) x y:
      y ∈ vars_of (sub_app sub x) ->
      y ∉ union_list ((@vars_of (TermOver BuiltinOrVar) variable _ _ (VarsOf_TermOver_BuiltinOrVar)) <$> (fmap snd sub)) ->
      y ∉ vars_of_sub sub ->
      y ∈ (vars_of x)
    .
    Proof.
      revert x y.
      induction sub; intros x y H1 H1' H2; simpl in *.
      {
        assumption.
      }
      {
        destruct a as [y' t'].
        apply not_elem_of_union in H2.
        destruct H2 as [H2 H3].
        rewrite elem_of_singleton in H2.
        apply not_elem_of_union in H1'.
        destruct H1' as [H4 H5].
        specialize (IHsub _ _ H1 H5 H3).
        simpl in *.
        destruct (decide (y' ∈ vars_of x)) as [Hin|Hnotin].
        {
          assert (Htmp := vars_of_TermOverBoV_subst x t' y' Hin).
          rewrite Htmp in IHsub. clear Htmp.
          ltac1:(set_solver).
        }
        {
          rewrite subst_notin2 in IHsub>[|assumption].
          exact IHsub.
        }
      }
  Qed.


Lemma sub_app_term
{Σ : StaticModel}
(ss : SubT)
(sym : symbol)
(l : list (TermOver BuiltinOrVar))
:
sub_app ss (t_term sym l) = t_term sym ((sub_app ss) <$> l)
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
(s : SubT)
(x : variable)
(t t' : TermOver BuiltinOrVar)
:
sub_app s (t_over (bov_variable x)) = sub_app s t' ->
sub_app s t = sub_app s  (TermOverBoV_subst t x t')
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

    rewrite sub_app_term.
    rewrite sub_app_term.
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

Lemma sub_app_identity
    {Σ : StaticModel}
    (sub : SubT)
    (φ : TermOver BuiltinOrVar)
    :
    vars_of_sub sub ## vars_of φ ->
    sub_app sub φ = φ
.
Proof.
    induction sub; intros HH; simpl in *.
    { reflexivity. }
    {
        destruct a as [x t].
        rewrite subst_notin2.
        apply IHsub.
        ltac1:(set_solver).
        ltac1:(set_solver).
    }
Qed.

Definition wft {Σ : StaticModel} (V : gset variable) (t : TermOver BuiltinOrVar)
: Prop
:= vars_of t ⊆ V
.

Fixpoint wfsub {Σ : StaticModel} (V : gset variable) (s : SubT)
: Prop
:=
match s with
| [] => True
| (x,t)::s' =>
    x ∈ V /\ wft (V ∖ {[x]}) t  /\ wfsub (V ∖ {[x]}) (s')
end
.

Lemma wf_concat {Σ : StaticModel} (V : gset variable) (s1 s2 : SubT)
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



Lemma sub_app_builtin
{Σ : StaticModel}
(ss : SubT)
(b : builtin_value)
:
sub_app ss (t_over (bov_builtin b)) = t_over (bov_builtin b)
.
Proof.
induction ss; simpl.
{ reflexivity. }
{
    destruct a; simpl in *.
    apply IHss.
}
Qed.



Lemma helper_lemma_3 {Σ : StaticModel}:
∀ l s1,
(
    ∀ x : variable,
    sub_app l (t_over (bov_variable x)) =
    sub_app (s1) (t_over (bov_variable x))
) ->
∀ t,
    sub_app l t = sub_app (s1) t
.
Proof.
intros l s1 HNice t.
revert l s1 HNice.
induction t; intros ll s1 HNice.
{
    destruct a.
    {
    rewrite sub_app_builtin.
    rewrite sub_app_builtin.
    reflexivity.
    }
    {
    rewrite HNice.
    reflexivity.
    }
}
{
    rewrite sub_app_term.
    rewrite sub_app_term.
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
