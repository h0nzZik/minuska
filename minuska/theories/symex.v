From Minuska Require Import
    prelude
    spec
    properties
    minusl_syntax
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

(*
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
*)
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

Equations? unify {Σ : StaticModel} (l : list eqn)
  : option (list (variable * (TermOver BuiltinOrVar)))
  by wf (deg l) (lexprod nat nat lt lt) :=

unify []
  := Some [] ;
  
unify ((t_over (bov_variable x),t_over (bov_variable y))::es) with (decide (x = y)) => {
| left _ := unify es ;
| right _ := 
  tmp ← unify (sub (t_over (bov_variable y)) x es);
  Some ((x, (t_over (bov_variable y)))::tmp)
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
    apply sub_decreases_degree.
    unfold vars_of; simpl.
    unfold vars_of; simpl.
    ltac1:(set_solver).
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

Lemma helper_lemma_2
  {Σ : StaticModel}
  (x : variable)
  (t : TermOver BuiltinOrVar)
  (es : list eqn)
  (s : SubT)
:
  sub_app s (t_over (bov_variable x)) = sub_app s t ->
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
  {Σ : StaticModel}
  (ss : SubT)
  (es : list eqn)
:=
  (fun e => (sub_app ss e.1, sub_app ss e.2)) <$> es
.


Lemma sub_ext_nil
  {Σ : StaticModel }
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
  {Σ : StaticModel}
  (ss : SubT)
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
  {Σ : StaticModel}
  :
  least_of [] []
.
Proof.
  unfold least_of.
  intros s' Hs'.
  exists s'. simpl.
  intros x. reflexivity.
Qed.
(* Maybe I can make the relation is_unifier_of such that
the unifier may map only variables that occur somewhere in the relation?
*)
Lemma is_unifier_of_cons
  {Σ : StaticModel}
  (ss : SubT)
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
  
  
Lemma sub_app_app
  {Σ : StaticModel}
  (s1 s2 : SubT)
  (t : TermOver BuiltinOrVar)
:
  sub_app (s1 ++ s2) t = sub_app s2 (sub_app s1 t)
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

Lemma vars_of_builtin
  {Σ : StaticModel}
  b
:
  vars_of (t_over (bov_builtin b)) = ∅
.
Proof.
  unfold vars_of; simpl.
  unfold vars_of; simpl.
  reflexivity.
Qed.



Lemma vars_of_variable
  {Σ : StaticModel}
  x
:
  vars_of (t_over (bov_variable x)) = {[x]}
.
Proof.
  unfold vars_of; simpl.
  unfold vars_of; simpl.
  reflexivity.
Qed.

Lemma unify_no_variable_out_of_thin_air
  {Σ : StaticModel}
  (es : list eqn)
  (ss : SubT)
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
    rewrite HH in Heqcall.
    rewrite bind_Some in Heqcall.
    destruct Heqcall as [x0 [H1x0 H2x0]].
    inversion H2x0; subst; clear H2x0.
    clear Heq.
    repeat (rewrite fmap_cons).
    rewrite list_to_set_cons.
    rewrite eqns_vars_cons.
    ltac1:(rewrite ![((_).*1)]/=).
    ltac1:(rewrite ![((_).1)]/=).
    ltac1:(rewrite ![((_).2)]/=).
    ltac1:(rewrite !vars_of_builtin).
    ltac1:(rewrite !vars_of_variable).
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
    rewrite Heq in HH.
    inversion HH.
  }
  {
    ltac1:(congruence).
  }
  {
    rewrite HH in Heqcall.
    rewrite bind_Some in Heqcall.
    destruct Heqcall as [x0 [H1x0 H2x0]].

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
    ltac1:(rewrite !vars_of_variable).
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
    rewrite HH in Heqcall.
    rewrite bind_Some in Heqcall.
    destruct Heqcall as [x0 [H1x0 H2x0]].

    inversion H2x0; subst; clear H2x0.
    clear Heq.
    ltac1:(rewrite !fmap_cons).
    rewrite list_to_set_cons.
    rewrite eqns_vars_cons.
    unfold compose at 1.
    ltac1:(rewrite ![((_).*1)]/=).
    ltac1:(rewrite ![((_).1)]/=).
    ltac1:(rewrite ![((_).2)]/=).
    ltac1:(rewrite !vars_of_variable).
    rewrite union_list_cons.
    specialize (H _ H1x0).
    destruct (decide (x ∈ eqns_vars es)).
    {
      rewrite eqns_vars_sub in H>[|assumption].
      ltac1:(rewrite vars_of_variable in H).
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
    rewrite HH in Heqcall.
    rewrite bind_Some in Heqcall.
    destruct Heqcall as [x0 [H1x0 H2x0]].
    inversion H2x0; subst; clear H2x0.
    rewrite fmap_cons.
    rewrite list_to_set_cons.
    rewrite eqns_vars_cons.
    simpl.
    ltac1:(rewrite vars_of_variable).
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
    ltac1:(simp unify in HH). rewrite Heq in HH.
    simpl in HH.
    inversion HH.
  }
  {
    ltac1:(congruence).
  }
  {
    rewrite HH in Heqcall.
    rewrite bind_Some in Heqcall.
    destruct Heqcall as [x0 [H1x0 H2x0]].
    inversion H2x0; subst; clear H2x0.
    specialize (H _ H1x0).
    rewrite fmap_cons.
    rewrite list_to_set_cons.
    rewrite eqns_vars_cons.
    simpl.
    ltac1:(rewrite vars_of_variable).
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
    rewrite HH in Heqcall.
    specialize (H _ Heqcall).
    ltac1:(rewrite eqns_vars_app in H).
    ltac1:(rewrite eqns_vars_zip in H)>[assumption|].
    ltac1:(rewrite 2!vars_of_t_term).
    exact H.
  }
  {
    ltac1:(congruence).
  }
Qed.

Lemma sub_app_unbound_var_1
  {Σ : StaticModel}
  (ss : SubT)
  (x : variable)
  :
  x ∉ ss.*1 ->
  sub_app ss (t_over (bov_variable x)) = (t_over (bov_variable x))
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

Lemma sub_app_unbound_var_2
  {Σ : StaticModel}
  (ss : SubT)
  (x : variable)
  :
  x ∉ ⋃ (vars_of <$> ss.*2) ->
  forall (t : TermOver BuiltinOrVar),
  x ∉ vars_of t ->
  x ∉ vars_of (sub_app ss t)
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
  {Σ : StaticModel}
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


Inductive unify_failure {Σ : StaticModel} : list eqn -> Prop :=
| uf_varin_fail_1  : forall x t es,
  x ∈ vars_of t ->
  t <> (t_over (bov_variable x)) ->
  unify_failure (((t_over (bov_variable x)), t) :: es)

| uf_varin_fail_2  : forall x t es,
  x ∈ vars_of t ->
  t <> (t_over (bov_variable x)) ->
  unify_failure ((t, (t_over (bov_variable x))) :: es)

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
| uf_subterm : forall es (s : symbol) (l1 l2 : list (TermOver BuiltinOrVar)) (idx : nat) (t1 t2 : TermOver BuiltinOrVar),
  l1 !! idx = Some t1 ->
  l2 !! idx = Some t2 ->
  unify_failure ((t1,t2)::(drop (S idx) (zip l1 l2))++es) ->
  unify_failure (((t_term s l1),(t_term s l2))::es)
  *)

| uf_subterm : forall es (s : symbol) (l1 l2 : list (TermOver BuiltinOrVar)) (idx : nat),
  unify_failure ((take idx (zip l1 l2))++es) ->
  unify_failure (((t_term s l1),(t_term s l2))::es)

| uf_rec : forall es t1 t2,
  unify_failure es ->
  unify_failure ((t1,t2)::es)

| uf_rec_sub2_l : forall es x t,
  unify_failure (sub t x es) ->
  unify_failure ((t_over (bov_variable x),t)::es)

| uf_rec_sub2_r : forall es x t,
  unify_failure (sub t x es) ->
  unify_failure ((t, t_over (bov_variable x))::es)
(*
| uf_rec_sub : forall es t1 t2 ss,
  unify_failure (sub_ext ss es) ->
  unify_failure ((t1,t2)::es)
  *)
.

(*
Lemma unify_some_not_failure
  {Σ : StaticModel}
  (es : list eqn)
  (u : SubT)
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
  {Σ : StaticModel}
  (es : list eqn)
:
  ~ unify_failure es ->
  match unify es with
  | None => False
  | Some ss =>
    (is_unifier_of ss es /\ least_of ss es )
  end
.
Proof.
  ltac1:(funelim(unify es)); intros HH.
  {
    simpl in *.
    ltac1:(simp unify). repeat split.
    apply least_of_nil_nil.
  }
  {
    rewrite <- Heqcall.
    (destruct (unify es) as [ss|]).
    {
      clear Heq. ltac1:(simplify_eq/=).
      ltac1:(ospecialize (H _)).
      {
        intros HContra. apply HH. clear HH.
        apply uf_rec. exact HContra.
      }
      repeat split.
      {
        
        apply H.
      }
      {
        unfold least_of.
        intros s' Hs'.
        simpl in Hs'.
        destruct Hs' as [Hs'1 Hs'2].
        destruct H as [H1 H2].
        unfold least_of in H2.
        specialize (H2 _ Hs'2).
        destruct H2 as [s1 Hs1].
        exists s1.
        intros x.
        specialize (Hs1 x).
        rewrite Hs1.
        reflexivity.
      }
    }
    {
      apply H. clear H. intros HContra. apply HH. clear HH.
      apply uf_rec. exact HContra.
    }
  }
  {
    rewrite <- Heqcall.
    apply HH. clear HH.
    apply uf_diff_builtin.
    intros HContra. subst. apply n. reflexivity.
  }
  {
    rewrite <- Heqcall. clear Heqcall.
    apply HH. clear HH.
    apply uf_varin_fail_2.
    assumption.
    ltac1:(discriminate).
  }
  {
    rewrite <- Heqcall. clear Heqcall.
    simpl.
    ltac1:( repeat (case_match; simpl in *; simplify_eq/=)).
    {
      repeat split.
      {
        ltac1:(ospecialize (H _)).
        {
          intros HContra.
          apply HH. clear HH.
          apply uf_rec_sub2_r.
          exact HContra.
        }
        destruct H as [H2 H3]. clear H1 e.
        apply is_unifier_of_cons. exact H2.
      }
      {
        
        ltac1:(ospecialize (H _)).
        {
          intros HContra. apply HH. clear HH.
          apply uf_rec_sub2_r.
          exact HContra.
        }
        destruct H as [H2 H3].
        clear H1 e.
        intros sss Hsss.
        specialize (H3 sss).
        ltac1:(ospecialize (H3 _)).
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
        destruct H3 as [s1 Hs1]. simpl in *.
        destruct Hsss as [Hsss1 Hsss2].
        exists s1. intros x0.
        specialize (Hs1 x0).
        rewrite sub_app_app in Hs1.
        rewrite sub_app_app.
        destruct (decide (x = x0))>[|auto].
        subst.
        rewrite sub_app_builtin.
        rewrite sub_app_builtin in Hsss1.
        rewrite sub_app_builtin.
        ltac1:(congruence).
      }
    }
    {
      apply H. intros HContra. apply HH. clear HH H.
      apply uf_rec_sub2_r.
      exact HContra.
    }
  }
  {
    ltac1:(simplify_eq/=).
  }
  {
    ltac1:(case_match).
    {
        clear Heq.
        ltac1:(exfalso; apply HH; clear HH).
        apply uf_over_term.
    } 
    {
      ltac1:(simp unify in H).
      unfold unify_unfold_clause_6_1 in H.
      ltac1:(case_match).
      {
        ltac1:(simplify_eq/=).
      }
      {
          clear H Heq.
          apply HH. clear HH.
          apply uf_over_term.
      }
    }
  }
  {
    ltac1:(case_match).
    { ltac1:(simplify_eq/=). 
    }
    {
      inversion e.
    }
  }
  {
    rewrite <- Heqcall. clear Heqcall. simpl.
    ltac1:(ospecialize (H _)).
    {
      intros HContra. apply HH. clear HH.
      apply uf_rec_sub2_l.
      exact HContra.
    }
    ltac1:(repeat (case_match; simplify_eq/=)).
    {
      clear e H1.
      destruct H as [H1 H2].
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
          destruct Hss as [Hss1 Hss2].
          eapply helper_lemma_2; assumption.
        }
        {
          destruct H2 as [s1 Hs1].
          exists s1.
          intros x0. rewrite Hs1. simpl.
          destruct (decide (x = x0))>[|reflexivity].
          subst. simpl in Hss.
          destruct Hss as [Hss1 Hss2].
          do 2 (rewrite sub_app_app).
          assert (Hs1x0 := Hs1 x0).
          (rewrite sub_app_app in Hs1x0).
          rewrite <- Hs1x0.
          rewrite sub_app_builtin.
          rewrite sub_app_builtin.
          rewrite sub_app_builtin in Hss1.
          apply Hss1.
        }
      }
    }
    {
      exact H.
    }
  }
  {
    rewrite <- Heqcall. clear Heqcall.
    ltac1:(ospecialize (H _)).
    {
      intros HContra. apply HH. clear HH.
      apply uf_rec. exact HContra.
    }
    ltac1:(repeat (case_match; simplify_eq/=; try assumption)).
    destruct H as [H1 H2].
    repeat split.
    { assumption. }
    intros ss Hss.
    specialize (H2 ss).
    ltac1:(ospecialize (H2 _)).
    {
      simpl in Hss. apply Hss.
    }
    destruct H2 as [s1 Hs1].
    exists s1.
    intros x.
    rewrite Hs1.
    reflexivity.
  }
  {
    rewrite <- Heqcall. ltac1:(simp unify in Heqcall).
    unfold unify_unfold_clause_2 in Heqcall.
    clear Heqcall.
    ltac1:(ospecialize (H _)).
    {
      intros HContra. apply HH. clear HH.
      apply uf_rec_sub2_l.
      exact HContra.
    }
    clear HH.
    ltac1:(repeat (case_match; simpl in *; simplify_eq/=)).
    clear e H1 Heq n0 H2.
    destruct H as [HH1 HH2].
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
        destruct Hss as [Hss1 Hss2].
        eapply helper_lemma_2.
        { apply Hss1. }
        exact Hss2.
      }
      destruct HH2 as [s1 Hs1].
      exists s1.
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
    rewrite <- Heqcall. clear Heqcall. simpl.
    apply HH. clear HH. clear Heq.
    apply uf_varin_fail_1.
    assumption.
    ltac1:(discriminate).
  }
  {
    rewrite <- Heqcall. clear Heqcall. simpl.
    clear Heq.
    ltac1:(ospecialize (H _)).
    {
      intros HContra. apply HH. clear HH.
      apply uf_rec_sub2_l.
      exact HContra.
    }
    clear HH.
    ltac1:(repeat (case_match; simpl in *; simplify_eq/=)).
    {
      clear e H1.
      destruct H as [HH1 HH2].
      rewrite sub_app_term.
      rewrite sub_app_term.
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
          ltac1:(rewrite Hl0i).
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
          ltac1:(rewrite Hl0i).
          simpl.
          reflexivity.
        }
      }
      {
        apply is_unifier_of_cons.
        apply HH1.
      }
      {
        assert (Hnoota := unify_no_variable_out_of_thin_air _ _ H0).
        intros u Hu.
        unfold least_of in HH2.

        
        assert (HH21 := HH2 _ HH1).
        simpl in Hu.
        destruct Hu as [Hu1 Hu2].
        (*
        destruct HH21 as [s1 Hs1].
        *)

        assert(HH2u := HH2 u).
        ltac1:(ospecialize (HH2u _)).
        {
          apply helper_lemma_2.
          apply Hu1.
          exact Hu2.
        }
        destruct HH2u as [s1 Hs1].
        
        exists (s1).
        intros x0.
        ltac1:(rename s1 into r).
        (*rewrite sub_app_app.*)

        assert (Hunb := sub_app_unbound_var_2 l x).
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
          apply sub_app_unbound_var_1 in Hnlx as Hnlx'.
          eapply helper_lemma_3 in Hs1 as Hs1'.
          rewrite <- Hs1'. clear Hs1'.
          exact Hu1.
        }
        {
          apply Hs1.
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
    rewrite Heq.
    apply HH. clear HH.
    constructor.
  }
  {
    ltac1:(exfalso).
    apply HH. constructor. assumption.
    ltac1:(discriminate).
  }
  {
    rewrite <- Heqcall. clear Heqcall.
    ltac1:(ospecialize (H _)).
    {
      intros HContra. apply HH. clear HH.
      apply uf_rec_sub2_r.
      exact HContra.
    }
    clear HH.
    destruct (unify (sub (t_term s l0) x es)) as [Hr |].
    {
      simpl.
      destruct H as [HH1 HH2].
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
          ltac1:(rewrite Heqt).
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
          ltac1:(rewrite Heqt).
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
        destruct Hu as [Hu1 Hu2].
        specialize (HH2 u).
        ltac1:(ospecialize (HH2 _)).
        {
          apply helper_lemma_2.
          symmetry. apply Hu1. apply Hu2.
        }
        destruct HH2 as [rest Hrest].
        exists rest.
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
      simpl. exact H.
    }
  }
  {
    destruct a as [HH1 HH2].
    clear Heq.
    rewrite <- Heqcall.
    ltac1:(ospecialize (H _)).
    {
      intros HContra. apply HH. clear HH.
      subst.
      apply uf_subterm with (idx := (length (zip l1 l2))).
      rewrite firstn_all.
      exact HContra.
    }
    destruct (unify (zip l1 l2 ++ es)) eqn:Heq2.
    {
      subst.
      destruct H as [HH3 HH4].
      simpl.
      repeat split.
      {
        rewrite is_unifier_of_app in HH3.
        destruct HH3 as [HH31 HH32].
        rewrite sub_app_term.
        rewrite sub_app_term.
        f_equal.
        apply list_eq.
        intros i.
        rewrite list_lookup_fmap.
        rewrite list_lookup_fmap.
        destruct (l1!!i) eqn:Hl1i.
        {
          ltac1:(rewrite Hl1i).
          destruct (l2!!i) eqn:Hl2i.
          {
            ltac1:(rewrite Hl2i).
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
          apply lookup_lt_Some in Hl1i.
          apply lookup_ge_None in Hl2i.
          ltac1:(lia).
        }
        {
          ltac1:(rewrite Hl1i).
          simpl.
          destruct (l2 !! i) eqn:Hl2i.
          {
            apply lookup_lt_Some in Hl2i.
            apply lookup_ge_None in Hl1i.
            ltac1:(lia).
          }
          {
            ltac1:(rewrite Hl2i).
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
        destruct Hu as [H1u H2u].
        specialize (HH4 u).
        rewrite is_unifier_of_app in HH4.
        rewrite sub_app_term in H1u.
        rewrite sub_app_term in H1u.
        inversion H1u; subst; clear H1u.
        ltac1:(ospecialize (HH4 _)).
        {
          split; try assumption.
          clear -HH2 H0.
          revert l2 HH2 H0.
          induction l1; intros l2 HH2 H0.
          {
            destruct l2; simpl in *.
            { exact I. }
            { ltac1:(lia). }
          }
          {
            simpl in *.
            destruct l2; simpl in *.
            {
              exact I.
            }
            {
              inversion H0; subst; clear H0.
              repeat split; try assumption.
              apply IHl1.
              { ltac1:(lia). }
              { apply H2. }
            }
          }
        }
        destruct HH4 as [rest Hrest].
        exists rest.
        intros x.
        specialize (Hrest x).
        apply Hrest.
      }
    }
    {
      exact H.
    }
  }
  {
    rewrite <- Heqcall.
    apply HH. clear HH.
    clear Heq.
    apply Decidable.not_and in n.
    destruct n.
    {
      constructor. assumption.
    }
    {
      apply uf_term_len. assumption.
    }
    destruct (decide (s1 = s2)).
    {
      subst. constructor. reflexivity.
    }
    {
      right. assumption.
    }
  }
Qed.

Lemma subst_preserves_subterm
  {Σ : StaticModel}
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

Lemma sub_app_preserves_subterm
  {Σ : StaticModel}
  (t1 t2 : TermOver BuiltinOrVar)
  :
  is_subterm_b t1 t2 ->
  forall s,
    is_subterm_b (sub_app s t1) (sub_app s t2)
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
  {Σ : StaticModel}
  x t
:
  x ∈ vars_of t ->
  is_subterm_b (t_over (bov_variable x)) t = true
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
      ltac1:(rewrite vars_of_variable in H2X).
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
  {Σ : StaticModel}
  (t1 t2 : TermOver BuiltinOrVar)
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
  {Σ : StaticModel}
  (t1 t2 : TermOver BuiltinOrVar)
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
  {Σ : StaticModel}
  (u : SubT)
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
    rewrite sub_app_app in IHrest.
    rewrite sub_app_app in IHrest.
    rewrite sub_app_app.
    rewrite sub_app_app.
    simpl.
    destruct a as [x t].
    ltac1:(congruence).
  }
Qed.

Lemma unify_failure_is_severe
  {Σ : StaticModel}
  (es : list eqn)
:
  unify_failure es ->
  ~ exists s : SubT,
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
        rewrite vars_of_variable in H.
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
      apply sub_app_preserves_subterm with (s := s) in H2X'.
      apply is_subterm_size in H2X'.
      rewrite H1s in H2X'.
      clear H1s H2s.
      rewrite sub_app_term in H2X'.
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
        rewrite vars_of_variable in H.
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
      apply sub_app_preserves_subterm with (s := s) in H2X'.
      apply is_subterm_size in H2X'.
      rewrite <- H1s in H2X'.
      clear H1s H2s.
      rewrite sub_app_term in H2X'.
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
    rewrite sub_app_builtin in Hs1.
    rewrite sub_app_builtin in Hs1.
    ltac1:(simplify_eq/=).
  }
  {
    intros HContra.
    destruct HContra as [s0 [H1s0 H2s0]].
    rewrite sub_app_term in H1s0.
    rewrite sub_app_builtin in H1s0.
    inversion H1s0.
  }
  {
    intros [s0 [H1s0 H2s0]].
    rewrite sub_app_term in H1s0.
    rewrite sub_app_builtin in H1s0.
    inversion H1s0.
  }
  {
    intros [s0 [H1s0 H2s0]].
    rewrite sub_app_term in H1s0.
    rewrite sub_app_term in H1s0.
    ltac1:(simplify_eq/=).
  }
  {
    intros [s0 [H1s0 H2s0]].
    rewrite sub_app_term in H1s0.
    rewrite sub_app_term in H1s0.
    ltac1:(simplify_eq/=).
    apply (f_equal length) in H0.
    rewrite fmap_length in H0.
    rewrite fmap_length in H0.
    ltac1:(simplify_eq/=).
  }
  {
    intros [s0 [H1s0 H2s0]].
    rewrite sub_app_term in H1s0.
    rewrite sub_app_term in H1s0.
    ltac1:(simplify_eq/=).
    apply (f_equal length) in H1s0 as H1s0'.
    rewrite fmap_length in H1s0'.
    rewrite fmap_length in H1s0'.
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