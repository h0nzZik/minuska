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


From CoLoR Require
    Term.WithArity.ASignature
    Term.WithArity.AUnif
    Term.WithArity.ATerm
.

From CoLoR Require Import
    Util.Vector.VecUtil
.

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


Program Definition ColorSignatureOf (Σ : StaticModel)
    : Term.WithArity.ASignature.Signature
:= {|
    Term.WithArity.ASignature.symbol := (nat*(@spec.symbol Σ)) ;
    Term.WithArity.ASignature.arity := fun ns => ns.1 ;
    Term.WithArity.ASignature.beq_symb :=
        fun s1 s2 => bool_decide (s1 = s2) ;
|}.
Next Obligation.
    abstract(
        assert (H := bool_decide_spec ((n0,s0)=(n,s)));
        unfold Is_true in H;
        ltac1:(case_match; naive_solver)
    ).
Defined.
Fail Next Obligation.


Lemma wf_iter_step_constructive
    {Σ' : Term.WithArity.ASignature.Signature}
    (p : @Term.WithArity.AUnif.problem Σ')
 :
    { k : nat & @Term.WithArity.AUnif.solved Σ' (Term.WithArity.AUnif.iter_step k p) = true }.
Proof. 
    assert (HH := (Term.WithArity.AUnif.wf_Lt' p)).
    induction HH.
    {
        destruct x.
        {
            destruct p.
            destruct e; simpl in *.
            { exists 0. reflexivity. }
            {
                remember (Some (s, e::e0)) as p.
                destruct (Term.WithArity.AUnif.solved (Term.WithArity.AUnif.step p)) eqn:Heqsolved.
                {
                    exists 1. simpl.
                    ltac1:(repeat (case_match; simpl in *; simplify_eq/=; try reflexivity)).
                }
                {
                    specialize (X (Term.WithArity.AUnif.step p)).
                    
                    ltac1:(ospecialize (X _)).
                    {
                        assert(Htmp := (Term.WithArity.AUnif.Lt_step _ (Term.WithArity.AUnif.solved_inv _ Heqsolved))).
                        subst p. exact Htmp.
                    }
                    destruct X as [k Hk].
                    exists (S k). simpl.
                    rewrite <- Term.WithArity.AUnif.iter_step_commut.
                    subst p.
                    exact Hk.
                }
            }
        }
        {
            exists 0. reflexivity.
        }
    }
Defined.

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

Print TermOverBoV_subst.
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

Fixpoint wfsub {Σ : StaticModel} (V : gset variable) (s : list (variable*(TermOver BuiltinOrVar))%type)
: Prop
:=
  match s with
  | [] => True
  | (x,t)::s' =>
    x ∈ V /\ wft (V ∖ {[x]}) t  /\ wfsub (V ∖ {[x]}) (s')
  end
.

Fixpoint vars_of_sub {Σ : StaticModel} (s : list (variable * (TermOver BuiltinOrVar))%type) : gset variable
:=
  match s with
  | [] => ∅
  | (x,_)::s' => {[x]} ∪ vars_of_sub s'
  end
.

Lemma wf_concat {Σ : StaticModel} (V : gset variable) (s1 s2 : list (variable*(TermOver BuiltinOrVar))%type)
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

Definition sub_lt {Σ : StaticModel} (s1 s2 : list (variable*(TermOver BuiltinOrVar))%type) :=
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
  (V : gset variable)
  x t es
  :
  x ∈ V ->
  wft V t ->
  wfeqns V es ->
  x ∉ vars_of t ->
  (lexprod nat nat lt lt) (deg (sub t x es)) (deg ((t_over (bov_variable x), t)::es))
.
Proof.

  intros Hx Ht Hes Hxt.
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
            Search vars_of TermOverBoV_subst.
            Search eqns_vars sub.
            admit.
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
    ltac1:(cut (x ∉ eqns_vars (sub t x es))).
    {
      intros HH. ltac1:(set_solver).
    }
   
    Print deg.
  }
  {
  }
  apply left_lex.
  apply subset_size.
  rewrite strict_spec.
  split.
  {
    admit.
  }
  {
    ltac1:(rewrite eqns_vars_cons).
    simpl.
    intros HContra.
    unfold vars_of at 1 in HContra; simpl in HContra.
    unfold vars_of at 1 in HContra; simpl in HContra.
    rewrite elem_of_subseteq in HContra.
    ltac1:(cut(x ∉ eqns_vars (sub t x es))).
    {
      intros HH. ltac1:(set_solver).
    }
    clear.
    induction es; simpl.
    {
      unfold eqns_vars. simpl. ltac1:(set_solver).
    }
    {
      intros HContra. apply IHes. clear IHes.
      ltac1:(rewrite eqns_vars_cons in HContra). simpl in HContra.
      Search TermOverBoV_subst vars_of.
    }
  }
  revert x t Hx Ht Hes.
  induction es; intros x t Hx Ht Hes.
  {
    unfold eqns_vars. simpl. unfold eqn_vars. simpl. unfold vars_of; simpl.
    unfold vars_of; simpl. ltac1:(set_solver).
  }
  {
    simpl. ltac1:(rewrite eqns_vars_cons). 
    ltac1:(rewrite eqns_vars_hd_comm).
    ltac1:(rewrite eqns_vars_cons).
    unfold wfeqns in Hes. rewrite Forall_cons in Hes.
    destruct Hes as [Hes1 Hes2]. simpl.
    destruct (decide (x ∈ vars_of a.1)).
    {
      destruct (decide (x ∈ vars_of a.2)).
      {
        ltac1:(rewrite vars_of_TermOverBoV_subst).
        { assumption. }
        ltac1:(rewrite vars_of_TermOverBoV_subst).
        { assumption. }
        specialize (IHes x t Hx Ht Hes2).
        rewrite eqns_vars_cons.
        ltac1:(rewrite eqns_vars_cons in IHes).
        simpl in *.
        Search strict.
        rewrite strict_spec in IHes.
        rewrite strict_spec.
        destruct IHes as [IHes1 IHes2].
        split.
        {
          ltac1:(set_solver).
        }
        intros HContra.
        apply IHes2. clear IHes2.
        unfold vars_of at 1; simpl.
        unfold vars_of at 1; simpl.
        unfold vars_of at 3 in HContra; simpl in HContra.
        unfold vars_of at 3 in HContra; simpl in HContra.
        unfold vars_of at 1 in IHes1; simpl in IHes1.
        unfold vars_of at 1 in IHes1; simpl in IHes1.
        Print sub.
        destruct (decide (x ∈ vars_of t)).
        {
          
        }
        {
          ltac1:(set_solver).
        }
        
        ltac1:(set_solver).
        Search "⊂".
        ltac1:(
          cut(vars_of t ∪ vars_of a.1 ∖ {[x]} ∪ (vars_of t ∪ vars_of a.2 ∖ {[x]}) ⊂ vars_of a.1 ∪ vars_of a.2 ∪ (vars_of (t_over (bov_variable x)) ∪ vars_of t ∪ eqns_vars es))
        ).
        {
          intros HH. ltac1:(set_solver).
        }
        ltac1:(set_solver). 
        ltac1:(replace ((vars_of t ∪ vars_of a.1 ∖ {[x]} ∪ (vars_of t ∪ vars_of a.2 ∖ {[x]}) ∪ eqns_vars (sub t x es)) )
        with (eqns_vars (sub t x es) ∪ ((vars_of t ∪ vars_of a.1 ∖ {[x]} ∪ (vars_of t ∪ vars_of a.2 ∖ {[x]}))) )
        by set_solver
        ).
        rewrite size_union_alt.
        ltac1:(
          replace ((vars_of a.1 ∪ vars_of a.2 ∪ eqns_vars ((t_over (bov_variable x), t) :: es)))
          with (eqns_vars ((t_over (bov_variable x), t) :: es) ∪(vars_of a.1 ∪ vars_of a.2))
          by set_solver
        ).
        ltac1:(rewrite size_union_alt).
        ltac1:(
          cut (size ((vars_of t ∪ vars_of a.1 ∖ {[x]} ∪ (vars_of t ∪ vars_of a.2 ∖ {[x]})) ∖ eqns_vars (sub t x es)) <= size ((vars_of a.1 ∪ vars_of a.2) ∖ eqns_vars ((t_over (bov_variable x), t) :: es)))
        ).
        {
          intros HH. ltac1:(lia).
        }
        Search size "∖".
        apply subseteq_size.
        ltac1:(set_solver).
        Search lt le "trans".
        eapply Nat.lt_le_trans.
      }
      {
      
      }
    }
    Check vars_of_TermOverBoV_subst.
  }
  

  (*
  intros Hx Ht Hes.
  
  eapply transitivity>[|eapply deg_cons_lt].
  unfold deg.
  induction es; simpl.
  { apply reflexivity. 
  
  assert (HL1: (lexprod nat nat lt lt) (deg (sub t x es)) (deg (es))).
  {
    unfold deg; simpl.
    apply right_lex.
  }
  
  
  ltac1:(cut((lexprod nat nat lt lt) (deg (sub t x es)) (deg (es)))).
  {
    intros HH.
    unfold deg; simpl.
    apply left_lex.
    inversion HH; subst; clear HH.
    {
      eapply transitivity. apply H0. clear H0.
      ltac1:(rewrite eqns_vars_cons). simpl.
      apply subset_size.
      unfold vars_of at 1; simpl.
      unfold vars_of at 1; simpl..
      ltac1:(set_solver).
      unfold eqns_vars at 2. simpl.
    }
    {
    
    }
    
    simpl.
  }

  *)
  unfold deg.
  
  induction es; intros Hwf0 Hwf1 Hwf2.
  {
    unfold eqns_vars. unfold eqn_vars.
    unfold vars_of at 1; simpl.
    unfold vars_of at 1; simpl.
    rewrite union_empty_r_L.
    rewrite size_union_alt.
    apply left_lex.
    unfold set_size. simpl. unfold elements,gset_elements,mapset.mapset_elements.
    rewrite map_to_list_empty. simpl. rewrite map_to_list_singleton. simpl. ltac1:(lia).
  }
  {
    simpl.
    unfold wfeqns in Hwf2. rewrite Forall_cons in Hwf2.
    destruct Hwf2 as [Hwf2 Hwf3].
    specialize (IHes Hwf0 Hwf1 Hwf3). clear Hwf3.
    
    inversion IHes; subst; clear IHes.
    {
      ltac1:(rewrite eqns_vars_cons). simpl.
      ltac1:(rewrite eqns_vars_cons). simpl.
      ltac1:(rewrite eqns_vars_cons). simpl.    
      ltac1:(rewrite eqns_vars_cons in H0). simpl in H0.
      apply left_lex.
      rewrite union_comm_L.
      rewrite size_union_alt.
      unfold TermOver in *.
      ltac1:(replace (vars_of (t_over (bov_variable x)) ∪ vars_of t ∪ (vars_of a.1 ∪ vars_of a.2 ∪ eqns_vars es))
      with (vars_of (t_over (bov_variable x)) ∪ vars_of t ∪ eqns_vars es ∪ (vars_of a.1 ∪ vars_of a.2))
      by set_solver).
      ltac1:(rewrite size_union_alt).
      
      ltac1:(
        cut(size ((vars_of (TermOverBoV_subst a.1 x t) ∪ vars_of (TermOverBoV_subst a.2 x t)) ∖ eqns_vars (sub t x es)) <= size ((vars_of a.1 ∪ vars_of a.2) ∖ (vars_of (t_over (bov_variable x)) ∪ vars_of t ∪ eqns_vars es)))
      ).
      {
        intros HH. unfold TermOver in *. ltac1:(lia).
      }
      apply subseteq_size. clear H0.
      Search TermOverBoV_subst.
    }
    {
    
    }
    
    destruct (decide (x ∈ (vars_of a.1 ∪ vars_of a.2))) as [Hin|Hnotin].
    {
      admit.
    }
    {
      rewrite subst_notin2.
      {
        rewrite subst_notin2.
        {
          (*
          apply left_lex.
          ltac1:(repeat rewrite eqns_vars_cons).
          simpl.
          *)

          inversion IHes; subst; clear IHes.
          {
            ltac1:(rewrite eqns_vars_cons in H0). simpl in H0.
            (* We probably need the equations to be well-formed, whatever it means,
               to prevent the substitution to grow the number of variables *)
            ltac1:(replace ((vars_of a.1 ∪ vars_of a.2 ∪ eqns_vars (sub t x es)) )
              with ((eqns_vars (sub t x es) ∪ (vars_of a.1 ∪ vars_of a.2)) ) by set_solver).
            rewrite size_union_alt.
            
            ltac1:(
              assert (Htmp: (size (vars_of (t_over (bov_variable x)) ∪ vars_of t ∪ (vars_of a.1 ∪ vars_of a.2 ∪ eqns_vars es))
)
              = (size ((vars_of (t_over (bov_variable x)) ∪ (vars_of t)  ∪ (eqns_vars es)) ∪ (vars_of a.1 ∪ vars_of a.2))))
              by (f_equal; set_solver)
            ).
            ltac1:(rewrite Htmp). clear Htmp.
            
            ltac1:(rewrite size_union_alt).
            ltac1:(
              cut (size ((vars_of a.1 ∪ vars_of a.2) ∖ eqns_vars (sub t x es)) <= size ((vars_of a.1 ∪ vars_of a.2) ∖ (vars_of (t_over (bov_variable x)) ∪ vars_of t ∪ eqns_vars es)))
            ).
            {
              intros HHH.
              clear Htmp.
              unfold TermOver in *.
              ltac1:(lia).
            }
            
            ltac1:(lia).
          }
          {
          
          }
                    apply subset_size.
          Search size subseteq.
          ltac1:(repeat (rewrite size_union_alt)).
          unfold eqns_vars.
          simpl.
           admit.
        }
        {
          ltac1:(set_solver).
        }

      }
      {
        ltac1:(set_solver).
      }
    }
    unfold eqns_vars. simpl.
    inversion IHes; subst; clear IHes.
    {
      
    }
    {
    
    }
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
unify ((t_over (bov_variable x), t)::es) := if (decide (x ∈ vars_of t)) then None
  else (
    tmp ← unify (sub t x es);
    Some ((x,t)::tmp)
  ) ;
unify ((t, t_over (bov_variable x))::es) := if (decide (x ∈ vars_of t)) then None
  else (
    tmp ← unify (sub t x es);
    Some ((x,t)::tmp)
  ) ;
unify ((t_term s1 l1, t_term s2 l2)::es) := if (decide ((s1 = s2) /\ (length l1 = length l2) )) then (
    unify ((zip l1 l2) ++ es)
  ) else None ;

unify ((t1,t2)::es) := if (decide (t1 = t2)) then unify es else None
.
Proof.
  {
    unfold deg. simpl.
    Check right_lex.
    unfold eqns_vars. simpl.
    do 4 (unfold vars_of at 3; simpl).
    rewrite union_empty_l_L.
    rewrite union_empty_l_L.
    apply right_lex.
    ltac1:(lia).
  }
  {
    unfold deg. simpl.
  }
Defined.




Program Definition term_to_color
    (Σ : StaticModel)
    (t : TermOver variable)
    : Term.WithArity.ATerm.term (ColorSignatureOf Σ)
:=
    let sz := TermOver_size t in
    (fix term_to_color' (sz : nat) (t : TermOver variable) (pf : sz >= TermOver_size t) :=
        match sz with
        | 0 => _
        | (S sz') =>
            match t with
            | t_over x => Term.WithArity.ATerm.Var (Pos.to_nat (encode x))
            | t_term s l =>
            let term_to_color'_sz' := term_to_color' sz' in
            let helper := fix helper
              (lt : list (TermOver variable))
              (pf: sum_list_with (S ∘ TermOver_size) lt <= sz')
              { struct lt }
              : {r : list (Term.WithArity.ATerm.term (ColorSignatureOf Σ)) & length r = length lt } := (
                match lt with
                | [] => @existT _ _ [] _
                | t'::ts' => @existT _ _ ((term_to_color'_sz' t' _)::(projT1 (helper ts' _))) _
                end
            ) in
            let l'pf := helper l _ in
            let l' := projT1 l'pf in
            let pf := projT2 l'pf in
            @Term.WithArity.ATerm.Fun
                (ColorSignatureOf Σ)
                ((length l),s)
                (@Vcast (Term.WithArity.ATerm.term (ColorSignatureOf Σ))
                _
                (Vector.of_list l')
                (length l)
                _
                )
            
            end
        end
    ) sz t _
.
Next Obligation.
    (*abstract*)(intros; subst; destruct t; simpl in *; ltac1:(lia)).
Defined.
Next Obligation.
    abstract(intros; subst; simpl in *; ltac1:(lia)).
Defined.
Next Obligation.
    abstract(intros; subst; simpl in *; ltac1:(lia)).
Defined.
Next Obligation.
    abstract(intros; subst; simpl in *; ltac1:(lia)).
Defined.
Next Obligation.
  simpl. intros. rewrite (projT2 (helper ts' _)). reflexivity.
Defined.
Next Obligation.
  simpl. intros. subst. simpl in *. ltac1:(lia).
Defined.
Next Obligation.
  intros. subst. simpl in *.
  ltac1:(unfold l'). exact pf.
Defined.
Next Obligation.
  simpl. intros. apply reflexivity.
Defined.
Fail Next Obligation.



Program Definition term_from_color
    (Σ : StaticModel)
    (ct : Term.WithArity.ATerm.term (ColorSignatureOf Σ))
    : option (TermOver variable)
:=
  let sz := ATerm.size ct in
  ( fix term_from_color' (sz : nat) (ct : ATerm.term (ColorSignatureOf Σ)) (pf : ATerm.size ct <= sz) : option (TermOver variable) :=
    match sz with
    | 0 => None
    | S sz' => 
      match ct with
      | ATerm.Var n => s ← @decode variable _ _ (Pos.of_nat n); Some (t_over s)
      | ATerm.Fun s v => 
        let l := Vector.to_list v in
        let term_from_color'_sz' := term_from_color' sz' in
        let helper := (
          fix helper
            (lct : list (ATerm.term (ColorSignatureOf Σ)))
            (pf : sum_list_with (@ATerm.size (ColorSignatureOf Σ)) lct <= sum_list_with (@ATerm.size (ColorSignatureOf Σ)) l)
            (pf2 : sum_list_with (@ATerm.size (ColorSignatureOf Σ)) l <= sz')
            { struct lct }
            : option (list (TermOver variable))
          :=
            match lct with
            | [] => Some []
            | x::xs =>
              y ← term_from_color'_sz' x _;
              ys ← helper xs _ pf2;
              Some (y::ys)
            end
        ) in
        ts ← helper l _ _;
        Some (t_term (s.2) ts)
      end
    end
  ) sz ct _
.
Next Obligation.
  intros. subst. simpl in *. ltac1:(lia).
Defined.
Next Obligation.
  abstract(intros; subst; simpl in *; ltac1:(lia)).
Defined.
Next Obligation.
  intros. subst. simpl in *.
  apply reflexivity.
Defined.
Next Obligation.
  intros. subst. simpl in *.
  
  ltac1:(cut (sum_list_with (@ATerm.size (ColorSignatureOf Σ)) l 
    = ((fix size_terms (n : nat) (ts : vector (ATerm.term (ColorSignatureOf Σ)) n) {struct ts} : nat :=
      match ts with
      | Vnil => 0
      | @Vector.cons _ u n0 us => ATerm.size u + size_terms n0 us
      end
    ) s.1 v))).
  {
    intros HH. rewrite HH. clear HH. ltac1:(lia).
  }
  destruct s; simpl in *.
  ltac1:(unfold l). clear.
  induction v; simpl.
  { reflexivity. }
  {
    unfold Vector.to_list in IHv.
    ltac1:(lia).
  }
Defined.
Next Obligation.
  intros.
  simpl in *.
  apply reflexivity.
Defined.
Fail Next Obligation.

Lemma term_to_from_color
    (Σ : StaticModel)
    (t : TermOver variable)
    :
    term_from_color Σ (term_to_color Σ t) = Some t
.
Proof.
  unfold term_to_color, term_from_color.
  remember (TermOver_size t) as sz in |-.
  assert (Hsz: TermOver_size t <= sz) by ltac1:(lia).
  clear Heqsz.
  revert t Hsz.
  induction sz; intros t Hsz.
  {
    destruct t; simpl in Hsz; ltac1:(lia).
  }
  destruct t; simpl in *.
  {
    
  }

Qed.

Definition color_unify
  (Sig : ASignature.Signature)
  (x y : ATerm.term Sig)
  :
  option (AUnif.solved_eqns Sig)
.
Proof.
  remember (AUnif.mk_problem x y) as p.
  remember (wf_iter_step_constructive p) as Hwf.
  destruct Hwf as [k Hsolved]. clear HeqHwf.
  unfold AUnif.solved in Hsolved.
  destruct (AUnif.iter_step k p) eqn:Heqiskp; simpl in *.
  {
    destruct p0; simpl in *.
    destruct e; simpl in *.
    {
      exact (Some s).
    }
    {
      inversion Hsolved.
    }
  }
  {
    exact None.
  }
Defined.

Print color_unify.
Term.WithArity.AUnif.iter_step

Check Term.WithArity.AUnif.iter_step.

Print AUnif.problem.
Print AUnif.eqn. (* a pair of terms *)
Print AUnif.solved_eqn. (* a pair of a variable and a term *)

Check AUnif.sub_eq_is_sol.
Print AUnif.unifiable.

Check AUnif.iter_step.
Print AUnif.solved.
Print AUnif.successfull.
Check AUnif.iter_step_complete.
Check AUnif.iter_step_most_general.
Check ASubstitution.sub.
Check AUnif.subst_of_solved_eqns.
Check AUnif.is_sol_eqn.



(*
Check @map_length.
Print sigT.
Equations? eq_term_to_color
    (Σ : StaticModel)
    (t : TermOver variable)
    : Term.WithArity.ATerm.term (ColorSignatureOf Σ)
    by wf (TermOver_size t) lt :=
eq_term_to_color Σ (t_over x) := Term.WithArity.ATerm.Var (Pos.to_nat (encode x)) ;
eq_term_to_color Σ (t_term s l) with (aux Σ l l [] _) => {
  | @existT _ _ r pf =>
            @Term.WithArity.ATerm.Fun
                (ColorSignatureOf Σ)
                ((length l),s)
                (@Vcast (Term.WithArity.ATerm.term (ColorSignatureOf Σ))
                _
                (Vector.of_list r)
                (length l)
                _
                )
  }
  where aux (Σ : StaticModel) (l l' l'' : list (TermOver variable)) (pf : l = l'' ++ l') : {nl : list (ATerm.term (ColorSignatureOf Σ)) & length nl = length l' } :=
    aux Σ _ nil _ pf := @existT _ _ nil _ ;
    aux Σ _ (x::xs) r pf := @existT _ _ ( (eq_term_to_color Σ x) :: (projT1 (aux xs (r ++ [x]) _)) ) _
.
Proof.
  { reflexivity. }
  {
    subst l.
    simpl. rewrite sum_list_with_app. simpl. ltac1:(lia).
  }
  {
    subst. rewrite <- app_assoc. reflexivity.
  }
  {
    simpl. subst. simpl.
    remember (aux xs (r ++ [x]) _).
    rewrite (projT2 s0). reflexivity.
  }
  {
    simpl. reflexivity.
  }
  {
    simpl. subst. simpl.
    rewrite (projT2 (aux l [] erefl)).
    reflexivity.
  }
Defined.
*)

