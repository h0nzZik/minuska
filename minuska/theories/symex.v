From Minuska Require Import
    prelude
    spec
.

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


#[local]
Obligation Tactic := idtac.
Check @map_length.

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
              : list (Term.WithArity.ATerm.term (ColorSignatureOf Σ)) := (
                match lt with
                | [] => []
                | t'::ts' => (term_to_color'_sz' t' _)::(helper ts' _)
                end
            ) in
            let l' := helper l _ in
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
    intros. ltac1:(unfold l'; clear l'). subst.
    ltac1:(move: (term_to_color_obligation_4 _ _ _ _ _ _ _ _ _ _ _)).
    simpl. intros e0.
    remember (helper) as rhelper. ltac1:(unfold helper in Heqrhelper).
    clear helper.
    revert pf e0 Heqrhelper.
    induction l; intros pf e0 Heqrhelper.
    { subst; reflexivity. }
    {
      assert (Htmp: (S sz' ≥ TermOver_size (t_term s l))).
      {
        simpl in *. ltac1:(lia).
      }
      simpl. specialize (IHl Htmp).
      simpl in e0.
      assert (Htmp2: sum_list_with (S ∘ TermOver_size) l ≤ sz').
      {
        abstract(ltac1:(simpl in *; lia)).
      }
      specialize (IHl Htmp2 Heqrhelper).
      rewrite <- IHl.
      rewrite Heqrhelper. simpl length. rewrite <- Heqrhelper.
      ltac1:(unfold length).
      ltac1:(fold (@length (ATerm.term (ColorSignatureOf Σ)))).
      ltac1:(move: (term_to_color_obligation_3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
      intros ee.
      ltac1:(      replace ee with Htmp2).
      {
        reflexivity.
      }
      apply proof_irrelevance.
    }
Defined.
Next Obligation.
    intros. ltac1:(unfold sz). reflexivity.
Defined.
Fail Next Obligation.

Print AUnif.problem.
Check AUnif.mk_problem.
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




