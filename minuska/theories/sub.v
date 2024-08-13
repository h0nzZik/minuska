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