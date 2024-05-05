From Minuska Require Import
    prelude
    spec
    properties
    syntax_properties
.


Require Import Wellfounded.
From stdpp Require Import lexico well_founded.

Require Import Program.
From Coq Require Import Logic.Eqdep_dec.

From Equations Require Export Equations.

(*
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Sample (choose(0, 10)).*)

(*
From CoLoR Require
    Term.WithArity.ASignature
    Term.WithArity.AUnif
    Term.WithArity.ATerm
.

From CoLoR Require Import
    Util.Vector.VecUtil
.
*)
Definition Satisfies_variable_GroundTerm'
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (x : variable)
    := ρ !! x = Some t
.

#[export]
Instance Satisfies_variable_GroundTerm
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        variable
        variable
:= {|
    satisfies :=
        fun
            (ρ : Valuation2)
            (t : TermOver builtin_value)
            (x : variable) => Satisfies_variable_GroundTerm' ρ t x
|}.


Equations? sat2v
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver variable)
    : Prop
    by wf (TermOver_size φ) lt
:=
    sat2v ρ t (t_over x) := Satisfies_variable_GroundTerm' ρ t x ;
    sat2v ρ (t_over _) (t_term s l) := False ;
    sat2v ρ (t_term s' l') (t_term s l) :=
        ((s' = s) /\
        (length l' = length l) /\
        forall i t' φ' (pf1 : l !! i = Some φ') (pf2 : l' !! i = Some t'),
            sat2v ρ t' φ'
        )
    ;
.
Proof.
    abstract(
    unfold satisfies in *; simpl in *;
    simpl;
    apply take_drop_middle in pf1;
    rewrite <- pf1;
    rewrite sum_list_with_app; simpl;
    ltac1:(lia)).
Defined.

#[export]
Instance Satisfies_TOV_GroundTerm
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        (TermOver variable)
        variable
:= {|
    satisfies := fun ρ g φ => sat2v ρ g φ
|}.

Record SymCfg {Σ : StaticModel} := {
    scfg_pattern : TermOver variable ;
    scfg_side_conditions : list SideCondition2 ;
}.

Definition Satisfies_SymCfg_GroundTerm'
    {Σ : StaticModel}
    (ρ : Valuation2)
    (g : TermOver builtin_value)
    (scfg : SymCfg)
:=
    ((satisfies ρ g scfg.(scfg_pattern))
    * (satisfies ρ tt scfg.(scfg_side_conditions)))%type
.

#[export]
Instance Satisfies_SymCfg_GroundTerm
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        (SymCfg)
        variable
:= {|
    satisfies := fun ρ g φ => Satisfies_SymCfg_GroundTerm' ρ g φ
|}.

Definition Satisfies_listSymCfg_GroundTerm'
    {Σ : StaticModel}
    (ρ : Valuation2)
    (g : TermOver builtin_value)
    (lφ : list SymCfg)
:=
    forall φ, φ ∈ lφ -> satisfies ρ g φ
.

#[export]
Instance Satisfies_listSymCfg_GroundTerm
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        (list SymCfg)
        variable
:= {|
    satisfies := Satisfies_listSymCfg_GroundTerm'
|}.

Definition SymexStep {Σ : StaticModel}
:=
    list SymCfg -> list SymCfg
.

Definition refines {Σ : StaticModel} (g : TermOver builtin_value) (φ : list SymCfg)
:= { ρ : Valuation2 & satisfies ρ g φ}.

Definition SymexStep_sound
    {Σ : StaticModel}
    (Act : Set)
    (Γ : RewritingTheory2 Act)
    (step : SymexStep)
:=
    ∀ (φ : list SymCfg) (g g' : TermOver builtin_value),
        refines g φ ->
        refines  g' (step φ) ->
        rewriting_relation Γ g g'
.

Definition SymexStep_complete
    {Σ : StaticModel}
    (Act : Set)
    (Γ : RewritingTheory2 Act)
    (step : SymexStep)
:=
    ∀ (φ : list SymCfg) (g g' : TermOver builtin_value),
        rewriting_relation Γ g g' ->
        refines g φ ->
        refines  g' (step φ)
.



Definition eqn {Σ : StaticModel} : Type := ((TermOver BuiltinOrVar)*(TermOver BuiltinOrVar))%type.

Definition eqn_size {Σ : StaticModel} (e : eqn) : nat := TermOver_size (e.1) + TermOver_size (e.2).

Definition eqns_size {Σ : StaticModel} (es : list eqn) := sum_list_with eqn_size es.


Definition eqn_vars {Σ : StaticModel} (e : eqn) := ((vars_of (e.1)) ∪ (vars_of (e.2))).
Definition eqns_vars {Σ : StaticModel} (es : list eqn) := union_list (eqn_vars <$> es)
.


Definition deg {Σ : StaticModel} (es : list eqn) : (nat*nat)%type :=
  (size (eqns_vars es), eqns_size es)
.


#[local]
Obligation Tactic := idtac.


Definition sub
  {Σ : StaticModel}
  (t' : TermOver BuiltinOrVar)
  (x : variable)
  (es : list eqn)
:= (fun e => (TermOverBoV_subst e.1 x t', TermOverBoV_subst e.2 x t')) <$> es
.


Lemma vars_of_TermOverBoV_subst
  {Σ : StaticModel}
  (t t' : TermOver BuiltinOrVar)
  (x : variable)
:
  x ∈ vars_of t ->
  vars_of (TermOverBoV_subst t x t') =
  vars_of t' ∪ (vars_of t ∖ {[x]})
.
Proof.
  induction t; intros HH1; simpl in *.
  {
    unfold vars_of in HH1; simpl in HH1.
    unfold vars_of in HH1; simpl in HH1.
    unfold vars_of_BoV in HH1; simpl in HH1.
    destruct a; simpl in *.
    {
      rewrite elem_of_empty in HH1. inversion HH1.
    }
    {
      rewrite elem_of_singleton in HH1.
      subst x0.
      destruct (decide (x = x))>[|ltac1:(contradiction)].
      unfold vars_of at 3; simpl.
      unfold vars_of at 3; simpl.
      ltac1:(set_solver).
    }
  }
  {
    revert HH1 H.
    unfold vars_of at 1; simpl.
    induction l; intros HH1 HH2.
    {
      simpl. unfold vars_of; simpl. ltac1:(set_solver).
    }
    {
      rewrite Forall_cons in HH2. destruct HH2 as [HH2 HH3].
      simpl in HH1. rewrite elem_of_union in HH1.
      destruct (decide (x ∈ vars_of a)) as [Hin|Hnotin].
      {
        specialize (HH2 Hin). simpl.
        unfold vars_of at 1; simpl.
        unfold vars_of at 1 in HH2; simpl in HH2.
        rewrite HH2. clear HH2.
        destruct (decide (x ∈ (⋃ (vars_of <$> l)))) as [Hin2 |Hnotin2].
        {
          specialize (IHl Hin2 HH3).
          unfold vars_of at 1 in IHl; simpl in IHl.
          unfold fmap in IHl.
          unfold fmap.
          rewrite IHl.
          unfold vars_of at 6; simpl.
          unfold vars_of at 4; simpl.
          ltac1:(set_solver).
        }
        {
          assert(Htmp: ((fun t'' => TermOverBoV_subst t'' x t')<$> l = l)).
          {
            clear -Hnotin2. revert Hnotin2.
            induction l; simpl; intros Hnotin2.
            { reflexivity. }
            {
              rewrite elem_of_union in Hnotin2.
              apply Decidable.not_or in Hnotin2.
              destruct Hnotin2 as [HH1 HH2].
              specialize (IHl HH2).
              unfold fmap in IHl.
              rewrite IHl.
              rewrite subst_notin2.
              { reflexivity. }
              { exact HH1. }
            }
          }
          unfold fmap in Htmp.
          ltac1:(replace (list_fmap) with (map)  in Htmp by reflexivity).
          rewrite Htmp.
          unfold vars_of at 5. simpl.
          ltac1:(set_solver).
        }
      }
      {
        clear HH2.
        destruct HH1 as [HH1|HH1].
        {
          ltac1:(exfalso; apply Hnotin; apply HH1).
        }
        {
          specialize (IHl HH1 HH3).        
          unfold vars_of at 1; simpl.
          unfold vars_of at 1 in IHl; simpl in IHl.
          rewrite subst_notin2.
          {
            unfold fmap in IHl; simpl in IHl.
            unfold vars_of at 4; simpl.
            unfold fmap.
            rewrite IHl.
            ltac1:(set_solver).  
          }
          {
            exact Hnotin.
          }
        }
      }
    }
  }
Qed.

Lemma eqns_vars_cons
  {Σ : StaticModel}
  (e : eqn)
  (es : list eqn)
: eqns_vars (e::es) = vars_of e.1 ∪ vars_of e.2 ∪ eqns_vars es
.
Proof.
  unfold eqns_vars. simpl.
  reflexivity.
Qed.

Lemma eqns_vars_hd_comm
  {Σ : StaticModel}
  (e1 e2 : eqn)
  (es : list eqn)
: eqns_vars (e1::e2::es) = eqns_vars (e2::e1::es)
.
Proof.
  unfold eqns_vars. simpl. ltac1:(set_solver).
Qed.

Definition wft {Σ : StaticModel} (V : gset variable) (t : TermOver BuiltinOrVar)
: Prop
  := vars_of t ⊆ V
.

Definition wfeqn {Σ : StaticModel} (V : gset variable) (e : eqn)
  : Prop
:=
  wft V (e.1) /\ wft V (e.2)
.

Definition wfeqns {Σ : StaticModel} (V : gset variable) (es : list eqn) : Prop :=
  Forall (wfeqn V) es
.

Definition SubT {Σ : StaticModel} : Type := list (variable*(TermOver BuiltinOrVar))%type.

Fixpoint wfsub {Σ : StaticModel} (V : gset variable) (s : SubT)
: Prop
:=
  match s with
  | [] => True
  | (x,t)::s' =>
    x ∈ V /\ wft (V ∖ {[x]}) t  /\ wfsub (V ∖ {[x]}) (s')
  end
.

Fixpoint vars_of_sub {Σ : StaticModel} (s : SubT) : gset variable
:=
  match s with
  | [] => ∅
  | (x,_)::s' => {[x]} ∪ vars_of_sub s'
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

Definition sub_lt {Σ : StaticModel} (s1 s2 : SubT) :=
  ∃ s3, s1 = s2 ++ s3
.

Fixpoint occurs {Σ : StaticModel} (x : variable) (t : TermOver BuiltinOrVar) :=
  match t with
  | t_over (bov_variable y) => x = y
  | t_over (bov_builtin _) => False
  | t_term _ l => (fix go' (l' : list (TermOver BuiltinOrVar)) : Prop :=
    match l' with
    | [] => False
    | t'::ts' => occurs x t' \/ go' ts'
    end
  ) l
  end
.

#[local]
Instance occurs_dec {Σ : StaticModel} (x : variable) (t : TermOver BuiltinOrVar)
  : Decision (occurs x t)
.
Proof.
  unfold Decision.
  ltac1:(induction t using TermOver_rect).
  {
    destruct a.
    {
      simpl. right. ltac1:(tauto).
    }
    {
      simpl. apply variable_eqdec.
    }
  }
  {
    revert X.
    induction l; intros IHouter.
    {
      simpl. right. ltac1:(tauto).
    }
    {
      simpl. assert (IH := IHouter a ltac:(set_solver)).
      destruct IH as [IH|IH].
      {
        left. left. exact IH.
      }
      {
        ltac1:(ospecialize (IHl _)).
        {
          intros x0 Hx0. apply IHouter.
          right. exact Hx0.
        }
        destruct IHl as [IHl|IHl].
        {
          left. right. exact IHl.
        }
        {
          right.
          intros HContra. ltac1:(tauto).
        }
      }
    }
  }
Defined.

Lemma on_distinct_vars {Σ : StaticModel} (a1 a2 : variable) (V : gset variable):
  a1 ∈ V ->
  a1 <> a2 ->
  a1 ∈ (V ∖ {[a2]})
.
Proof.
  intros HH1 HH2.
  ltac1:(set_solver).
Qed.

Lemma wft_minus {Σ : StaticModel} (V : gset variable) (t : TermOver BuiltinOrVar) (a : variable) :
  wft V t ->
  ~ occurs a t ->
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

Lemma deg_cons_lt {Σ : StaticModel} (e : eqn) (es : list eqn)
  :
  lexprod nat nat lt lt (deg es) (deg (e::es))
.
Proof.
  unfold deg at 2; simpl.
  destruct (decide (eqn_vars e ⊆ eqns_vars es)).
  {
    assert (Htmp: size (eqns_vars (e :: es)) = size (eqns_vars es)).
    {
      rewrite eqns_vars_cons.
      apply f_equal.
      unfold eqn_vars in s.
      ltac1:(set_solver).
    }
    rewrite Htmp. clear Htmp.
    apply right_lex.
    destruct e; simpl.
    destruct t,t0; simpl in *; ltac1:(lia).
  }
  {
    apply left_lex.
    rewrite eqns_vars_cons.
    apply subset_size.
    unfold eqn_vars in *; simpl in *.
    destruct e. destruct t,t0; simpl in *; ltac1:(set_solver).
  }
Qed.

Lemma sub_notin
  {Σ : StaticModel}
  t x es:
  x ∉ eqns_vars es ->
  (sub t x es) = es
.
Proof.
  induction es; simpl; intros Hnotin.
  { reflexivity. }
  {
    rewrite eqns_vars_cons in Hnotin.
    rewrite elem_of_union in Hnotin.
    apply Decidable.not_or in Hnotin.
    rewrite elem_of_union in Hnotin.
    destruct Hnotin as [Hnotin HH3].
    apply Decidable.not_or in Hnotin.
    destruct Hnotin as [HH1 HH2].
    rewrite subst_notin2>[|assumption].
    rewrite subst_notin2>[|assumption].
    destruct a; simpl.
    rewrite (IHes HH3).
    reflexivity.
  }
Qed.
 
Lemma eqns_vars_sub {Σ : StaticModel} (t : TermOver BuiltinOrVar) (x : variable)
    (es : list eqn):
    x ∈ eqns_vars es ->
    eqns_vars (sub t x es) = vars_of t ∪ (eqns_vars es ∖ {[x]})
.
Proof.
  induction es; intros HH1; simpl in *.
  {
    unfold eqns_vars in HH1. simpl in HH1. ltac1:(set_solver).
  }
  {
    rewrite eqns_vars_cons in HH1.
    rewrite elem_of_union in HH1.
    destruct HH1 as [HH|HH].
    {
      rewrite elem_of_union in HH.
      destruct HH as [HH|HH].
      {
        rewrite eqns_vars_cons. simpl.
        ltac1:(rewrite eqns_vars_cons; simpl).
        ltac1:(rewrite vars_of_TermOverBoV_subst)>[assumption|].
        destruct (decide (x ∈ vars_of a.2)).
        {
          ltac1:(rewrite vars_of_TermOverBoV_subst)>[assumption|].
          destruct (decide (x ∈ eqns_vars es)).
          {
            specialize(IHes ltac:(assumption)).
            rewrite IHes.
            ltac1:(set_solver).
          }
          {
            rewrite sub_notin>[|assumption].
            ltac1:(set_solver).
          }
        }
        {
          rewrite subst_notin2>[|assumption].
          destruct (decide (x ∈ eqns_vars es)).
          {
            specialize(IHes ltac:(assumption)).
            rewrite IHes.
            ltac1:(set_solver).
          }
          {
            rewrite sub_notin>[|assumption].
            ltac1:(set_solver).
          }
        }
      }
      {
        ltac1:(repeat rewrite eqns_vars_cons). simpl.
        unfold TermOver in *.
        destruct (decide (x ∈ vars_of a.1)).
        {
          ltac1:(rewrite -> vars_of_TermOverBoV_subst)>[|assumption].
          ltac1:(rewrite -> vars_of_TermOverBoV_subst)>[|assumption].
          destruct (decide (x ∈ eqns_vars es)).
          {
            specialize(IHes ltac:(assumption)).
            rewrite IHes.
            ltac1:(set_solver).
          }
          {
            rewrite sub_notin>[|assumption].
            ltac1:(set_solver).
          }
        }
        {
          rewrite subst_notin2>[|assumption].
          ltac1:(rewrite -> vars_of_TermOverBoV_subst)>[|assumption].
          destruct (decide (x ∈ eqns_vars es)).
          {
            specialize(IHes ltac:(assumption)).
            rewrite IHes.
            ltac1:(set_solver).
          }
          {
            rewrite sub_notin>[|assumption].
            ltac1:(set_solver).
          }
        }
      }
    }
    {
      specialize (IHes HH).
      rewrite eqns_vars_cons.
      ltac1:(rewrite eqns_vars_cons).
      simpl.
      rewrite IHes. clear IHes.
      destruct (decide (x ∈ vars_of a.1)), (decide (x ∈ vars_of a.2)).
      {
        ltac1:(rewrite vars_of_TermOverBoV_subst)>[assumption|].
        ltac1:(rewrite vars_of_TermOverBoV_subst)>[assumption|].
        ltac1:(set_solver).
      }
      {
        ltac1:(rewrite vars_of_TermOverBoV_subst)>[assumption|].
        ltac1:(rewrite subst_notin2)>[assumption|].
        ltac1:(set_solver).
      }
      {
        ltac1:(rewrite subst_notin2)>[assumption|].
        ltac1:(rewrite vars_of_TermOverBoV_subst)>[assumption|].
        ltac1:(set_solver).
      }
      {
        ltac1:(rewrite subst_notin2)>[assumption|].
        ltac1:(rewrite subst_notin2)>[assumption|].
        ltac1:(set_solver).
      }
    }
  }
Qed.
 

Lemma sub_decreases_degree
  {Σ : StaticModel}
  x t es
  :
  x ∉ vars_of t ->
  (lexprod nat nat lt lt) (deg (sub t x es)) (deg ((t_over (bov_variable x), t)::es))
.
Proof.

  intros Hxt.
  destruct (decide (x ∈ eqns_vars es)) as [Hxes | Hxes].
  {
    apply left_lex.
    apply subset_size.
    ltac1:(rewrite eqns_vars_cons).
    simpl.
    unfold vars_of at 1; simpl.
    unfold vars_of at 1; simpl.
    rewrite strict_spec.
    split.
    {
      ltac1:(cut (eqns_vars (sub t x es) ⊆ vars_of t ∪ eqns_vars es)).
      {
        intros HH. ltac1:(set_solver).
      }
      clear.
      induction es; simpl.
      {
        unfold eqns_vars; simpl. ltac1:(set_solver).
      }
      {
        rewrite eqns_vars_cons. simpl.
        ltac1:(rewrite eqns_vars_cons). simpl.
        destruct (decide (x ∈ vars_of a.1)).
        {
          ltac1:(rewrite vars_of_TermOverBoV_subst).
          { assumption. }
          destruct (decide (x ∈ vars_of a.2)).
          {
            ltac1:(rewrite vars_of_TermOverBoV_subst).
            { assumption. }
            ltac1:(set_solver).
          }
          {
            rewrite subst_notin2.
            ltac1:(set_solver).
            { assumption. }
          }
        }
        {
          rewrite subst_notin2.
          {
            destruct (decide (x ∈ vars_of a.2)).
            {
              ltac1:(rewrite vars_of_TermOverBoV_subst).
              { assumption. }
              ltac1:(set_solver).
            }
            {
              rewrite subst_notin2.
              { ltac1:(set_solver). }
              { assumption. }
            }
          }
          {
            assumption.
          }
        }
      }
    }
    {
      clear Hx Ht Hes.
      intros HContra. apply Hxt. clear Hxt.
      revert HContra Hxes.
      induction es; simpl; intros HContra Hxes.
      {
        unfold eqns_vars in Hxes. simpl in Hxes. ltac1:(set_solver).
      }
      {
        
        rewrite eqns_vars_cons in Hxes.
        rewrite eqns_vars_cons in HContra.
        ltac1:(rewrite eqns_vars_cons in HContra). simpl in *.
        destruct (decide ({[x]} ∪ vars_of t ∪ eqns_vars es ⊆ eqns_vars (sub t x es) )) as [Hyes|Hno].
        {
          specialize (IHes Hyes).
          destruct (decide (x ∈ eqns_vars es)).
          {
            auto with nocore.
          }
          {
            clear IHes.
            rewrite sub_notin in Hyes>[|assumption].
            ltac1:(set_solver).
          }
        }
        {
          clear IHes.
          destruct (decide (x ∈ eqns_vars es)) as [Hin|Hnotin].
          {
            rewrite eqns_vars_sub in Hno>[|assumption].
            rewrite eqns_vars_sub in HContra>[|assumption].
            destruct (decide (x ∈ vars_of a.1)), (decide (x ∈ vars_of a.2)).
            {
              ltac1:(rewrite vars_of_TermOverBoV_subst in HContra).
              { assumption. }
              ltac1:(rewrite vars_of_TermOverBoV_subst in HContra).
              { assumption. }
              ltac1:(set_solver).
            }
            {
              ltac1:(rewrite vars_of_TermOverBoV_subst in HContra).
              { assumption. }
              rewrite subst_notin2 in HContra>[|assumption].
              ltac1:(set_solver).
            }
            {
              rewrite subst_notin2 in HContra>[|assumption].
              ltac1:(rewrite vars_of_TermOverBoV_subst in HContra).
              { assumption. }
              ltac1:(set_solver).
            }
            {
              rewrite subst_notin2 in HContra>[|assumption].
              rewrite subst_notin2 in HContra>[|assumption].
              ltac1:(set_solver).
            }
          }
          {
            rewrite sub_notin in Hno>[|assumption].
            destruct (decide (x ∈ vars_of a.1)).
            {
              ltac1:(rewrite vars_of_TermOverBoV_subst in HContra).
              { assumption. }
              destruct (decide (x ∈ vars_of a.2)).
              {
                ltac1:(rewrite vars_of_TermOverBoV_subst in HContra).
                { assumption. }
                rewrite sub_notin in HContra>[|assumption].
                ltac1:(set_solver).
              }
              {
                rewrite sub_notin in HContra>[|assumption].
                rewrite subst_notin2 in HContra>[|assumption].
                ltac1:(set_solver).
              }
            }
            {
              ltac1:(rewrite subst_notin2 in HContra).
              { assumption. }
              destruct (decide (x ∈ vars_of a.2)).
              {
                ltac1:(rewrite vars_of_TermOverBoV_subst in HContra)>[assumption|].
                rewrite sub_notin in HContra>[|assumption].
                ltac1:(set_solver).
              }
              {
                ltac1:(set_solver).
              }
            }
          }
        }
      }
    }
  }
  {
    unfold deg; simpl.
    ltac1:(rewrite eqns_vars_cons). simpl.
    rewrite sub_notin>[|assumption].
    unfold vars_of at 1; simpl.
    unfold vars_of at 1; simpl.
    apply left_lex.
    apply subset_size.
    ltac1:(set_solver).
  }
Qed.

Lemma eqns_vars_app
  {Σ : StaticModel}
  (es1 es2 : list eqn)
  :
  eqns_vars (es1 ++ es2) = eqns_vars es1 ∪ eqns_vars es2
.
Proof.
  unfold eqns_vars.
  rewrite fmap_app.
  ltac1:(rewrite union_list_app_L).
  reflexivity.
Qed.

Lemma eqns_vars_zip
  {Σ : StaticModel}
  (l1 l2 : list (TermOver BuiltinOrVar))
:
  length l1 = length l2 ->
  eqns_vars (zip l1 l2) = union_list (vars_of <$> l1) ∪ union_list (vars_of <$> l2)
.
Proof.
  revert l2.
  induction l1; intros l2 Hlen; destruct l2; simpl.
  {
    unfold eqns_vars. simpl. ltac1:(set_solver).
  }
  {
    simpl in *. ltac1:(lia).
  }
  {
    simpl in *. ltac1:(lia).
  }
  {
    simpl in Hlen.
    specialize (IHl1 l2 ltac:(lia)).
    ltac1:(rewrite eqns_vars_cons). simpl.
    rewrite IHl1.
    ltac1:(set_solver).
  }
Qed.

Lemma fewer_arrows_lower_degree
  {Σ : StaticModel}
  (s : symbol)
  (l1 l2 : list (TermOver BuiltinOrVar))
  (es : list eqn)
:
  length l1 = length l2 ->
  (lexprod nat nat lt lt) (deg ((zip l1 l2)++es)) (deg ((t_term s l1, t_term s l2)::es))
.
Proof.
  intros Hlens.
  unfold deg.
  ltac1:(rewrite eqns_vars_app).
  ltac1:(rewrite eqns_vars_cons).
  simpl.
  unfold eqns_size.
  rewrite sum_list_with_app.
  rewrite eqns_vars_zip>[|assumption]. simpl.
  repeat (unfold vars_of; simpl).
  apply right_lex.
  unfold eqn_size. simpl.
  ltac1:(cut(sum_list_with (λ e : eqn, TermOver_size e.1 + TermOver_size e.2) (zip l1 l2) = sum_list_with TermOver_size l1 + sum_list_with TermOver_size l2)).
  {
    intros HH. rewrite HH.
    rewrite sum_list_with_compose.
    unfold compose.
    repeat (rewrite sum_list_with_S).
    repeat (rewrite fmap_length).
    repeat (rewrite sum_list_fmap).
    ltac1:(lia).
  }
  revert l2 Hlens.
  induction l1; intros l2 Hlens; destruct l2; simpl in *.
  { reflexivity. }
  { ltac1:(lia). }
  { ltac1:(lia). }
  specialize (IHl1 l2 ltac:(lia)).
  rewrite IHl1.
  ltac1:(lia).
Qed.

Lemma deg_swap_head
  {Σ : StaticModel}
  (es : list eqn)
  (t1 t2 : TermOver BuiltinOrVar)
:
  deg ((t1,t2)::es) = deg ((t2,t1)::es)
.
Proof.
   unfold deg; simpl.
   ltac1:(repeat rewrite eqns_vars_cons). simpl.
   f_equal.
   {
      f_equal.
      ltac1:(set_solver).
   }
   {
      unfold eqn_size. simpl.
      ltac1:(lia).
   }
Qed.

Equations? unify {Σ : StaticModel} (l : list eqn) : option (list (variable * (TermOver BuiltinOrVar)))
  by wf (deg l) (lexprod nat nat lt lt) :=

unify []
  := Some [] ;
  
unify ((t_over (bov_variable x),t_over (bov_variable y))::es) with (decide (x = y)) => {
| left _ := unify es ;
| right _ := None
};
unify ((t_over (bov_variable x), t)::es) with (decide (x ∈ vars_of t)) => {
  | left _ => None
  | right _ =>
    tmp ← unify (sub t x es);
    Some ((x,t)::tmp)
  };
unify ((t, t_over (bov_variable x))::es) with (decide (x ∈ vars_of t)) => {
  | left _ => None
  | right _ =>
    tmp ← unify (sub t x es);
    Some ((x,t)::tmp)
  };
unify ((t_term s1 l1, t_term s2 l2)::es) with (decide ((s1 = s2) /\ (length l1 = length l2) )) => {
  | left _ =>
      unify ((zip l1 l2) ++ es)
  | right _ => None
  } ;

unify ((t1,t2)::es) with (decide (t1 = t2)) => {
  | left _ => unify es
  | right _ => None
  };
.
Proof.
  {
    unfold deg. simpl.
    rewrite eqns_vars_cons. simpl.
    do 4 (unfold vars_of at 1; simpl).
    rewrite union_empty_l_L.
    rewrite union_empty_l_L.
    apply right_lex.
    ltac1:(lia).
  }
  {
    ltac1:(unfold t). clear t.
    ltac1:(rewrite deg_swap_head).
    apply sub_decreases_degree.
    unfold vars_of; simpl.
    unfold vars_of; simpl.
    ltac1:(set_solver).
  }
  {
    ltac1:(unfold t1; unfold t2). clear t1 t2.
    apply deg_cons_lt.
  }
  {
    ltac1:(unfold t). clear t.
    apply sub_decreases_degree.
    unfold vars_of; simpl.
    unfold vars_of; simpl.
    ltac1:(set_solver).
  }
  {
    apply deg_cons_lt.
  }
  {
    ltac1:(unfold t). clear t.
    apply sub_decreases_degree.
    assumption.
  }
  {
    ltac1:(unfold t1; unfold t2; clear t1; clear t2).
    apply deg_cons_lt.
  }
  {
    ltac1:(unfold t); clear t.
    ltac1:(rewrite deg_swap_head).
    apply sub_decreases_degree.
    assumption.
  }
  {
    destruct a as [H1 H2].
    subst s2.
    apply fewer_arrows_lower_degree.
    assumption.
  }
Qed.

Fixpoint sub_app {Σ : StaticModel} (s : SubT) (t : TermOver BuiltinOrVar) : TermOver BuiltinOrVar :=
match s with
| [] => t
| (x,t')::s' => sub_app s' (TermOverBoV_subst t x t')
end
.


Fixpoint is_unifier_of
  {Σ : StaticModel}
  (s : SubT)
  (es : list eqn)
:=
  match es with
  | [] => True
  | (t1,t2)::es' => (sub_app s t1 = sub_app s t2) /\ is_unifier_of s es'
  end
.

Definition least_of
  {Σ : StaticModel}
  (s : SubT)
  (es : list eqn)
:=
  ∀ s', is_unifier_of s' es ->
  ∃ s1, ∀ x, sub_app s' (t_over (bov_variable x)) = sub_app (s ++ s1) (t_over (bov_variable x))
.

Lemma subst_id
  {Σ : StaticModel}
  a x:
  TermOverBoV_subst a x (t_over (bov_variable x)) = a
.
Proof.
  induction a; simpl.
  {
    ltac1:(repeat case_match); subst; reflexivity.
  }
  {
    f_equal.
    revert H.
    induction l; intros HH.
    {
      simpl. reflexivity.
    }
    {
      rewrite Forall_cons in HH. destruct HH as [HH1 HH2].
      specialize (IHl HH2). clear HH2.
      simpl. rewrite IHl. rewrite HH1. reflexivity.
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

(* This does not work as x can occur in t' *)
(*
Lemma subst_twice
  {Σ : StaticModel}
  (x : variable)
  (t t' t'' : TermOver BuiltinOrVar)
:
  TermOverBoV_subst (TermOverBoV_subst t x t') x t'' = TermOverBoV_subst t x t'
.
Proof.
  destruct (decide (x ∈ vars_of t)).
  {
    rewrite subst_notin2 with (ψ := t'').
    { reflexivity. }
    Search vars_of TermOverBoV_subst.
    ltac1:(rewrite vars_of_TermOverBoV_subst).
    assumption.
    ltac1:(set_solver).
Qed.
*)

(* This does not hold either *) (*
Lemma subst_comm
  {Σ : StaticModel}
  (x y : variable)
  (t t' t'' : TermOver BuiltinOrVar)
:
  x <> y ->
  TermOverBoV_subst (TermOverBoV_subst t x t') y t''
  =
  TermOverBoV_subst (TermOverBoV_subst t y t'') x t'
.
Proof.
  induction t; intros Hne; simpl in *.
  {
    ltac1:(repeat (case_match; subst; simpl in *; try congruence)).
  }
Qed.
*)

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
Qed.


  
  
  
  