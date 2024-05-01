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

Definition eqns_vars {Σ : StaticModel} (es : list eqn) := union_list ((fun e => ((vars_of (e.1)) ∪ (vars_of (e.2))))<$> es)
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
:= (fun e => (TermOverBoV_subst t' x e.1, TermOverBoV_subst t' x e.2)) <$> es
.

Equations? unify {Σ : StaticModel} (l : list eqn) : option (list (variable * (TermOver BuiltinOrVar)))
  by wf (deg l) (@lexico (nat*nat)%type prod_lexico ) :=

unify [] := Some [] ;
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
    simpl in *. ltac1:(lia).
  }
  {
    ltac1:(unfold t). simpl in *. Search TermOverBoV_subst TermOver_size. ltac1:(lia).
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

