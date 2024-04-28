From Minuska Require Import
    prelude
    spec
.

From CoLoR Require
    Term.WithArity.ASignature
    Term.WithArity.AUnif
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
    SymCfg -> list SymCfg
.

Definition SymexStep_correct
    {Σ : StaticModel}
    (Act : Set)
    (Γ : RewritingTheory2 Act)
    (step : SymexStep)
:=
    ∀ (φ : SymCfg) (g : TermOver builtin_value),
        ( { ρ : Valuation2 & satisfies ρ g φ} ) ->
        ∀ (g' : TermOver builtin_value),
        ((
            ({ ρ : Valuation2 & satisfies ρ g' (step φ)} )
            ->
            (rewriting_relation Γ g g')
        )
        *
        (
            (rewriting_relation Γ g g') ->
            ({ ρ : Valuation2 & satisfies ρ g' (step φ)} )
        ))%type

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
 Qed.


