From Minuska Require Import
    prelude
    spec
.

Require Import Coq.Logic.ProofIrrelevance.

Lemma elem_of_next
    {A : Type}
    (x y : A)
    (l : list A)
    :
    x <> y ->
    x ∈ (y::l) ->
    x ∈ l
.
Proof.
    intros. inversion H0; subst; clear H0.
    { ltac1:(contradiction). }
    { assumption. }
Qed.

Section custom_induction_principle_2.

    Context
        {Σ : StaticModel}
        {B : Type}
        {_edB : EqDecision B}
        {A : Type}
        {_edA : EqDecision A}
    .

    Lemma TermOver_eqdec : EqDecision (@TermOver' B A).
    Proof.
        ltac1:(unshelve(refine (fix go (t1 t2 : (@TermOver' B A)) : {t1 = t2} + {t1 <> t2} :=
            match t1 with
            | t_over a1 =>
                match t2 with
                | t_over a2 =>
                    match (decide (a1 = a2)) with
                    | left _ => left _
                    | right _ => right _
                    end
                | t_term _ _ => right _
                end
            | t_term s1 l1 =>
                match t2 with
                | t_over _ => right _
                | t_term s2 l2 =>
                    match (decide (s1 = s2)) with
                    | left _ =>
                    let tmp := (fix go' (l1' l2' : list (@TermOver' B A)) : {l1' = l2'} + {l1' <> l2'} :=
                        match l1' with
                        | [] =>
                            match l2' with
                            | [] => left _
                            | _::_ => right _
                            end
                        | x1::xs1 =>
                            match l2' with
                            | [] => right _
                            | x2::xs2 =>
                                match (go x1 x2) with
                                | left _ =>
                                    match (go' xs1 xs2) with
                                    | left _ => left _
                                    | right _ => right _
                                    end
                                | right _ => right _
                                end
                            end
                        end
                    ) l1 l2 in
                    match tmp with
                    | left _ => left _
                    | right _ => right _
                    end
                    | right _ => right _
                    end
                end
            end
        )); abstract(congruence)).
    Defined.

    Fixpoint TermOver_rect
        (P : (@TermOver' B A) -> Type)
        (true_for_over : forall a, P (t_over a) )
        (preserved_by_term :
            forall
                (b : B)
                (l : list (@TermOver' B A)),
                (forall x, x ∈ l -> P x) ->
                P (t_term b l)
        )
        (p : (@TermOver' B A))
    :
        P p :=
    match p with
    | t_over a => true_for_over a
    | t_term s l =>  preserved_by_term s l
        (fun x pf => 
            (fix go (l' : list (@TermOver' B A)) : x ∈ l' -> P x :=
            match l' as l'0 return x ∈ l'0 -> P x with
            | nil => fun pf' => match not_elem_of_nil _ pf' with end
            | y::ys => 
                match (TermOver_eqdec x y) return x ∈ (y::ys) -> P x with
                | left e => fun pf' => (@eq_rect (@TermOver' B A) y P (TermOver_rect P true_for_over preserved_by_term y) x (eq_sym e)) 
                | right n => fun pf' =>
                    let H := @elem_of_next _ _ _ _ n pf' in
                    go ys H
                end
            end
            ) l pf
        )
    end
    .
End custom_induction_principle_2.

#[export]
Existing Instance TermOver_eqdec.


Fixpoint TermOverBuiltin_subst
    {Σ : StaticModel}
    (t m v : TermOver builtin_value)
    : TermOver builtin_value
:=
    if (decide (t = m)) then v else
    match t with
    | t_over o => t_over o
    | t_term s l => t_term s (map (fun t'' => TermOverBuiltin_subst t'' m v) l)
    end
.

Fixpoint is_subterm_b
    {Σ : StaticModel}
    {A : Type}
    {_edA : EqDecision A}
    (m t : TermOver A)
    : bool
:=
    if (decide (t = m)) then true else
    match t with
    | t_over _ => false
    | t_term _ l => existsb (is_subterm_b m) l
    end
.

Lemma not_subterm_subst
    {Σ : StaticModel}
    (t m v : TermOver builtin_value)
    :
    is_subterm_b m t = false ->
    TermOverBuiltin_subst t m v = t
.
Proof.
    induction t; simpl; intros; ltac1:(case_match; try congruence).
    f_equal.
    clear H1. revert H0 H.
    induction l; simpl; intros H0 H.
    { reflexivity. }
    rewrite Forall_cons in H.
    destruct H as [H1 H2].
    rewrite orb_false_iff in H0.
    destruct H0 as [H01 H02].
    specialize (IHl H02 H2). clear H0 H2.
    rewrite IHl. rewrite (H1 H01). reflexivity.
Qed.

Lemma is_subterm_sizes
    {Σ : StaticModel}
    {A : Type}
    {_edA : EqDecision A}
    (p q : TermOver A)
    :
    is_subterm_b p q = true ->
    TermOver_size p <= TermOver_size q
.
Proof.
    revert p.
    induction q; simpl; intros p HH.
    {
        unfold is_left in *.
        ltac1:(repeat case_match; subst; simpl in *; lia).
    }
    {
        unfold is_left in *.
        ltac1:(repeat case_match; subst; simpl in *; try lia).
        rewrite existsb_exists in HH.
        destruct HH as [x [H1x H2x]].

        rewrite <- elem_of_list_In in H1x.
        rewrite elem_of_list_lookup in H1x.
        destruct H1x as [i Hi].
        apply take_drop_middle in Hi.
        rewrite <- Hi in H.
        rewrite Forall_app in H.
        rewrite Forall_cons in H.
        destruct H as [IH1 [IH2 IH3]].
        specialize (IH2 p H2x).
        rewrite <- Hi.
        rewrite sum_list_with_app.
        simpl.
        ltac1:(lia).
    }
Qed.


#[export]
Instance BuiltinOrVar_eqdec {Σ : StaticModel}
    : EqDecision BuiltinOrVar
.
Proof.
    ltac1:(solve_decision).
Defined.

#[export]
Instance Expression2_eqdec
    {Σ : StaticModel}
    : EqDecision (Expression2)
.
Proof. ltac1:(solve_decision). Defined.

#[export]
Instance SideCondition2_eqdec
    {Σ : StaticModel}
    : EqDecision (SideCondition2)
.
Proof. ltac1:(solve_decision). Defined.

#[export]
Instance RewritingRule2_eqdec
    {Σ : StaticModel}
    {Act : Set}
    {_EA : EqDecision Act}
    : EqDecision (RewritingRule2 Act)
.
Print RewritingRule2.
Proof. ltac1:(solve_decision). Defined.



Fixpoint TermOverBoV_subst_gen
    {Σ : StaticModel}
    {B : Type}
    (lift_builtin : builtin_value -> B)
    (lift_variable : variable -> B)
    (t : TermOver BuiltinOrVar)
    (x : variable)
    (t' : TermOver B)
    : TermOver B
:=
match t with
| t_over (bov_builtin b) => t_over (lift_builtin b)
| t_over (bov_variable y) =>
    match (decide (x = y)) with
    | left _ => t'
    | right _ => t_over (lift_variable y)
    end
| t_term s l => t_term s (map (fun t'' => TermOverBoV_subst_gen lift_builtin lift_variable t'' x t') l)
end.

Definition TermOverBoV_subst_expr2
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    (x : variable)
    (t' : TermOver Expression2)
    : TermOver Expression2
:=
    TermOverBoV_subst_gen (fun b => e_ground (t_over b)) (fun x => e_variable x) t x t'
.

Fixpoint TermOverBoV_subst
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    (x : variable)
    (t' : TermOver BuiltinOrVar)
:=
match t with
| t_over (bov_builtin b) => t_over (bov_builtin b)
| t_over (bov_variable y) =>
    match (decide (x = y)) with
    | left _ => t'
    | right _ => t_over (bov_variable y)
    end
| t_term s l => t_term s (map (fun t'' => TermOverBoV_subst t'' x t') l)
end.

Fixpoint Expression2_subst
    {Σ : StaticModel}
    (e : Expression2)
    (x : variable)
    (e' : Expression2)
    : Expression2
:=    
match e with
| e_ground g => e_ground g
| e_variable y =>
    if (decide (y = x)) then e' else (e_variable y)
| e_nullary f => e_nullary f
| e_unary f e1 => e_unary f (Expression2_subst e1 x e')
| e_binary f e1 e2 => e_binary f (Expression2_subst e1 x e') (Expression2_subst e2 x e')
| e_ternary f e1 e2 e3 => e_ternary f (Expression2_subst e1 x e') (Expression2_subst e2 x e') (Expression2_subst e3 x e')
end
.


Fixpoint vars_of_to_l2r
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    : list variable
:= 
    match t with
    | t_over (bov_builtin _) => []
    | t_over (bov_variable x) => [x]
    | t_term s l => concat (map vars_of_to_l2r l)
    end
.

Lemma subst_notin
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of_to_l2r φ ->
    TermOverBoV_subst φ h ψ = φ
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        {
            intros _. reflexivity.
        }
        {
            destruct (decide (h = x)); simpl.
            {
                subst. intros HContra. ltac1:(exfalso). apply HContra.
                constructor.
            }
            {
                intros _. reflexivity.
            }
        }
    }
    {
        intros H2.
        f_equal.
        induction l; simpl.
        {
            reflexivity.
        }
        {
            apply Forall_cons in H.
            destruct H as [HH1 HH2].
            simpl in *.
            specialize (IHl HH2).
            rewrite elem_of_app in H2.
            apply Decidable.not_or in H2.
            destruct H2 as [H21 H22].
            specialize (IHl H22). clear H22.
            specialize (HH1 H21).
            rewrite HH1.
            rewrite IHl.
            reflexivity.
        }
    }
Qed.

Lemma subst_notin2 {Σ : StaticModel}
     : ∀ (h : variable) (φ ψ : TermOver BuiltinOrVar),
         h ∉ vars_of φ → TermOverBoV_subst φ h ψ = φ
.
Proof.
  intros h φ ψ. revert h ψ.
  induction φ; intros h ψ HH; simpl in * .
  {
    unfold vars_of in HH; simpl in HH.
    unfold vars_of in HH; simpl in HH.
    unfold vars_of_BoV in HH; simpl in HH.
    destruct a; simpl in *.
    { reflexivity. }
    {
      rewrite elem_of_singleton in HH.
      destruct (decide (h = x)) > [ltac1:(contradiction)|].
      reflexivity.
    }
  }
  {
    unfold vars_of in HH; simpl in HH.
    f_equal.
    revert H HH.
    induction l; intros H HH.
    {
      simpl. reflexivity.
    }
    {
      rewrite Forall_cons in H.
      destruct H as [H1 H2].
      specialize (IHl H2). clear H2.
      simpl in HH.
      simpl.
      rewrite elem_of_union in HH.
      apply Decidable.not_or in HH.
      destruct HH as [HH1 HH2].
      simpl in *.
      rewrite IHl.
      {
        rewrite H1.
        { reflexivity. }
        { exact HH1. }
      }
      {
        exact HH2.
      }
    }
  }
Qed.


Lemma vars_of_t_term
    {Σ : StaticModel}
    (s : symbol)
    (l : list (TermOver BuiltinOrVar))
    :
    vars_of (t_term s l) = union_list ( vars_of <$> l)
.
Proof. reflexivity. Qed.

Lemma vars_of_t_term_e
    {Σ : StaticModel}
    (s : symbol)
    (l : list (TermOver Expression2))
    :
    vars_of (t_term s l) = union_list ( vars_of <$> l)
.
Proof. reflexivity. Qed.


Fixpoint TermOver_size_with
    {T : Type}
    {A : Type}
    (fsz : A -> nat)
    (t : @TermOver' T A)
    : nat
:=
match t with
| t_over a => fsz a
| t_term _ l => S (sum_list_with (S ∘ TermOver_size_with fsz) l)
end.


Fixpoint TO_to_tree
    {T : Type}
    {A : Type}
    (t : @TermOver' T A)
    :
    (gen_tree (T+A)%type)
:=
    match t with
    | t_over a => GenLeaf (inr a)
    | t_term s l =>
        let l' := TO_to_tree <$> l in
        GenNode 0 ((GenLeaf (inl s))::l')
    end
.

Fixpoint TO_of_tree
    {T : Type}
    {A : Type}
    (t : (gen_tree (T+A)%type))
    :
    option (@TermOver' T A)
:=
match t with
| GenLeaf (inr a) =>
    Some (t_over a)

| GenNode 0 (GenLeaf (inl s)::l') =>
    l ← list_collect (TO_of_tree <$> l');
    Some (t_term s l)

| GenLeaf (inl _) => None
| GenNode 0 ((GenNode _ _)::_) => None
| GenNode 0 (GenLeaf (inr _)::_) => None
| GenNode 0 [] => None
| GenNode (S _) _ => None
end
.

Lemma TO_from_to_tree
    {T : Type}
    {A : Type}
    :
    forall t,
        @TO_of_tree T A (TO_to_tree t) = Some t
.
Proof.
    intros t; induction t.
    { reflexivity. }
    {
        simpl.
        rewrite bind_Some.
        exists l.
        (repeat split).
        induction l.
        { reflexivity. }
        {
            rewrite Forall_cons in H.
            destruct H as [IH1 IH2].
            specialize (IHl IH2).
            clear IH2.
            rewrite fmap_cons.
            rewrite fmap_cons.
            rewrite IH1. clear IH1.
            simpl.
            rewrite IHl.
            simpl.
            reflexivity.
        }
    }
Qed.

#[export]
Instance TermOver_countable
    {T : Type}
    {A : Type}
    {_edT : EqDecision T}
    {_edA : EqDecision A}
    {_cT : Countable T}
    {_cA : Countable A}
    :
    Countable (@TermOver' T A)
.
Proof.
    apply inj_countable with (
        f := TO_to_tree
    )(
        g := TO_of_tree
    ).
    {
        intros. apply TO_from_to_tree.
    }
Defined.


Definition BoV_to_Expr2
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : Expression2
:=
    match bov with
    | bov_builtin b => (e_ground ((t_over b)))
    | bov_variable x => e_variable x
    end
.

Definition TermOverBoV_to_TermOverExpr2
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    : TermOver Expression2
:=
    TermOver_map BoV_to_Expr2 t
.



Lemma size_subst_1
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    TermOver_size φ <= TermOver_size (TermOverBoV_subst φ h ψ)
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        { ltac1:(lia). }
        {
            destruct (decide (h = x)); simpl.
            {
                destruct ψ; simpl; ltac1:(lia).
            }
            {
                ltac1:(lia).
            }
        }
    }
    {
        revert H.
        induction l; intros H; simpl in *.
        { ltac1:(lia). }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            ltac1:(lia).
        }
    }
Qed.

Lemma size_subst_2
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∈ vars_of_to_l2r φ ->
    TermOver_size ψ <= TermOver_size (TermOverBoV_subst φ h ψ)
.
Proof.
    revert h ψ.
    induction φ; intros h ψ Hin; simpl in *.
    {
        destruct a.
        {
            inversion Hin.
        }
        {
            inversion Hin; subst; clear Hin.
            {
                destruct (decide (x = x))>[|ltac1:(contradiction)].
                ltac1:(lia).
            }
            {
                inversion H1.
            }
        }
    }
    {
        revert H Hin.
        induction l; intros H Hin; simpl in *.
        {
            inversion Hin.
        }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            destruct (decide (h ∈ vars_of_to_l2r a )) as [Hin'|Hnotin'].
            {
                specialize (H1 h ψ Hin'). clear Hin.
                ltac1:(lia).
            }
            {
                specialize (IHl ltac:(set_solver)).
                ltac1:(lia).
            }
        }
    }
Qed.


Equations? TermOverBoV_eval
    {Σ : StaticModel}
    (ρ : Valuation2)
    (φ : TermOver BuiltinOrVar)
    (pf : vars_of φ ⊆ vars_of ρ)
    : TermOver builtin_value
    by wf (TermOver_size φ) lt
:=

    TermOverBoV_eval ρ (t_over (bov_builtin b)) pf := t_over b
    ;

    TermOverBoV_eval ρ (t_over (bov_variable x)) pf with (inspect (ρ !! x)) => {
        | (@exist _ _ (Some t) pf') := t;
        | (@exist _ _ None pf') := _ ;
    }
    ;

    
    TermOverBoV_eval ρ (t_term s l) pf :=
        t_term s (pfmap l (fun φ' pf' => TermOverBoV_eval ρ φ' _))
    ;
.
Proof.
    {
        ltac1:(exfalso).        
        abstract(
            rewrite elem_of_subseteq in pf;
            specialize (pf x);
            unfold vars_of in pf; simpl in pf;
            unfold vars_of in pf; simpl in pf;
            unfold vars_of in pf; simpl in pf;
            rewrite elem_of_singleton in pf;
            specialize (pf eq_refl);
            unfold Valuation2 in *;
            rewrite elem_of_dom in pf;
            ltac1:(rewrite pf' in pf);
            eapply is_Some_None;
            apply pf
        ).
    }
    {
        unfold TermOver in *.
        intros. subst.
        apply elem_of_list_split in pf'.
        destruct pf' as [l1 [l2 Hl1l2]].
        subst l.
        rewrite vars_of_t_term in pf.
        rewrite fmap_app in pf. rewrite fmap_cons in pf.
        rewrite union_list_app_L in pf.
        rewrite union_list_cons in pf.
        ltac1:(set_solver).        
    }
    {
        intros. subst. simpl.
        apply elem_of_list_split in pf'.
        destruct pf' as [l1 [l2 Hl1l2]].
        subst l.
        rewrite sum_list_with_app.
        simpl.
        ltac1:(lia).
    }
Defined.

Lemma TermOverBoV_eval__varsofindependent
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (φ : TermOver BuiltinOrVar)
    pf1 pf2
    :
    (∀ x, x ∈ vars_of φ -> ρ1 !! x = ρ2 !! x) ->
    TermOverBoV_eval ρ1 φ pf1 = TermOverBoV_eval ρ2 φ pf2
.
Proof.
    unfold TermOver in *.
    ltac1:(funelim (TermOverBoV_eval ρ1 φ pf1)).
    {
        unfold TermOver in *.
        intros HH.
        (* rewrite <- Heqcall. *)
        ltac1:(simp TermOverBoV_eval).
        reflexivity.
    }
    {
        intros HH.
        rewrite <- Heqcall.
        ltac1:(simp TermOverBoV_eval).
        apply f_equal.
        apply f_equal.
        simpl.
        ltac1:(move: TermOverBoV_eval_obligation_2).
        intros HHpf.

        eapply functional_extensionality_dep.
        intros x.
        eapply functional_extensionality_dep.
        intros pf3.
        ltac1:(unshelve(eapply H0)).
        { exact x. }
        { exact pf3. }
        { 
            abstract(
                apply f_equal;
                apply f_equal;
                apply f_equal;
                apply proof_irrelevance
            ).
        }
        {
            unfold eq_rect.
            ltac1:(move: (TermOverBoV_eval__varsofindependent_subproof _ _ _ _ _ _ _ _)).
            intros mypf.
            assert(Htmp1:
                TermOverBoV_eval_obligation_2 Σ ρ s l pf
                (λ (x0 : StaticModel) (x1 : Valuation2) (x2 : TermOver
                BuiltinOrVar) (x3 : vars_of
                x2
                ⊆ vars_of
                x1) (_ : TermOver_size
                x2 <
                TermOver_size
                (t_term
                s
                l)),
                TermOverBoV_eval x1 x2 x3)
                x
                pf3
            =
                HHpf Σ ρ s l pf
                (λ (x0 : StaticModel) (x1 : Valuation2) (x2 : TermOver
                BuiltinOrVar) (x3 : vars_of
                x2
                ⊆ vars_of
                x1) (_ : TermOver_size
                x2 <
                S
                (sum_list_with
                (S
                ∘ TermOver_size)
                l)),
                TermOverBoV_eval x1 x2 x3)
                x
                pf3
            ).
            {
                apply proof_irrelevance.
            }
            revert mypf.
            rewrite Htmp1.
            intros mypf.
            assert (Htmp2: mypf = eq_refl).
            {
                apply proof_irrelevance.
            }
            rewrite Htmp2.
            reflexivity.
        }
        unfold TermOver in *.
        intros x0 Hx0.
        apply HH.
        clear -pf3 Hx0.
        rewrite vars_of_t_term.
        rewrite elem_of_union_list.
        exists (vars_of x).
        split>[|assumption].
        rewrite elem_of_list_fmap.
        exists x.
        split>[reflexivity|].
        exact pf3.
    }
    {
        intros HH.
        (*rewrite <- Heqcall.*)
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        simpl.
        unfold TermOverBoV_eval_obligation_1.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ x)).
        simpl in *.
        remember (TermOverBoV_eval ρ (t_over (bov_variable x)) pf) as t.
        assert (pf'2 : ρ2 !! x = Some t).
        {
            rewrite <- HH.
            exact pf'.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            rewrite elem_of_singleton.
            reflexivity.
        }
        ltac1:(rewrite -> pf').
        intros HHH.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ2 x)).
        ltac1:(rewrite -> pf'2).
        intros HHH2.
        reflexivity.
    }
    {
        intros HH.
        rewrite <- Heqcall.
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        simpl.
        unfold TermOverBoV_eval_obligation_1.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ x)).
        rewrite pf'.
        intros ?.
        f_equal.
        assert (pf'2 : ρ2 !! x = None).
        {
            rewrite <- HH.
            exact pf'.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            rewrite elem_of_singleton.
            reflexivity.
        }
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ2 x)).
        rewrite pf'2.
        intros ?.
        f_equal.
        apply proof_irrelevance.
    }
Qed.


Lemma TermOverBoV_eval__varsofindependent_2
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation2)
    (φ : TermOver BuiltinOrVar)
    pf1 pf2
    :
    (ρ1 ⊆ ρ2) ->
    TermOverBoV_eval ρ1 φ pf1 = TermOverBoV_eval ρ2 φ pf2
.
Proof.
    unfold TermOver in *.
    ltac1:(funelim (TermOverBoV_eval ρ1 φ pf1)).
    {
        unfold TermOver in *.
        intros HH.
        (* rewrite <- Heqcall. *)
        ltac1:(simp TermOverBoV_eval).
        reflexivity.
    }
    {
        intros HH.
        rewrite <- Heqcall.
        ltac1:(simp TermOverBoV_eval).
        apply f_equal.
        apply f_equal.
        simpl.
        ltac1:(move: TermOverBoV_eval_obligation_2).
        intros HHpf.

        eapply functional_extensionality_dep.
        intros x.
        eapply functional_extensionality_dep.
        intros pf3.
        ltac1:(unshelve(eapply H0)).
        { exact x. }
        { exact pf3. }
        { 
            abstract(
                apply f_equal;
                apply f_equal;
                apply f_equal;
                apply proof_irrelevance
            ).
        }
        {
            unfold eq_rect.
            ltac1:(move: (TermOverBoV_eval__varsofindependent_2_subproof _ _ _ _ _ _ _ _)).
            intros mypf.
            assert(Htmp1:
                TermOverBoV_eval_obligation_2 Σ ρ s l pf
                (λ (x0 : StaticModel) (x1 : Valuation2) (x2 : TermOver
                BuiltinOrVar) (x3 : vars_of
                x2
                ⊆ vars_of
                x1) (_ : TermOver_size
                x2 <
                TermOver_size
                (t_term
                s
                l)),
                TermOverBoV_eval x1 x2 x3)
                x
                pf3
            =
                HHpf Σ ρ s l pf
                (λ (x0 : StaticModel) (x1 : Valuation2) (x2 : TermOver
                BuiltinOrVar) (x3 : vars_of
                x2
                ⊆ vars_of
                x1) (_ : TermOver_size
                x2 <
                S
                (sum_list_with
                (S
                ∘ TermOver_size)
                l)),
                TermOverBoV_eval x1 x2 x3)
                x
                pf3
            ).
            {
                apply proof_irrelevance.
            }
            revert mypf.
            rewrite Htmp1.
            intros mypf.
            assert (Htmp2: mypf = eq_refl).
            {
                apply proof_irrelevance.
            }
            rewrite Htmp2.
            reflexivity.
        }
        exact HH.
    }
    {
        intros HH.
        (*rewrite <- Heqcall.*)
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        simpl.
        unfold TermOverBoV_eval_obligation_1.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ x)).
        simpl in *.
        remember (TermOverBoV_eval ρ (t_over (bov_variable x)) pf) as t.
        assert (pf'2 : ρ2 !! x = Some t).
        {
            unfold Valuation2 in *.
            eapply lookup_weaken.
            { apply pf'. }
            { apply HH. }
        }
        ltac1:(rewrite -> pf').
        intros HHH.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ2 x)).
        ltac1:(rewrite -> pf'2).
        intros HHH2.
        reflexivity.
    }
    {
        intros HH.
        rewrite <- Heqcall.
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        simpl.
        unfold TermOverBoV_eval_obligation_1.
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ x)).
        rewrite pf'.
        intros ?.
        f_equal.
        
        ltac1:(move: (TermOverBoV_eval_subproof Σ ρ2 x)).
        destruct (ρ2 !! x); simpl in *.
        {
            intros ?.
            destruct ((TermOverBoV_eval_subproof0 erefl pf)).
        }
        {
            intros ?.
            destruct (TermOverBoV_eval_subproof0 erefl pf).
        }
    }
Qed.

Lemma satisfies_TermOverBoV_eval
    {Σ : StaticModel}
    (ρ : Valuation2)
    (φ : TermOver BuiltinOrVar)
    pf
    :
    satisfies ρ (TermOverBoV_eval ρ φ pf) φ
.
Proof.
    ltac1:(funelim (TermOverBoV_eval ρ φ pf)).
    {
        ltac1:(simp TermOverBoV_eval).
        unfold satisfies; simpl.
        ltac1:(simp sat2B).
        simpl. reflexivity.
    }
    {
        rewrite <- Heqcall. clear Heqcall.
        simpl.
        unfold satisfies; simpl.
        ltac1:(simp sat2B). simpl.
        split>[reflexivity|].
        rewrite length_pfmap.
        split>[reflexivity|].
        intros i t' φ' Ht'φ' HH.
        pose (Helper := @pfmap_lookup_Some_1).
        lazy_match! Constr.type &HH with
        | (pfmap _ ?f) !! _ = _ => specialize (Helper _ _ _ $f)
        end.
        specialize (Helper i t' HH).
        simpl in Helper.
        rewrite Helper.
        specialize (X φ' ).
        ltac1:(ospecialize (X _)).
        {
            rewrite elem_of_list_lookup.
            exists i. assumption.
        }
        specialize (X Σ ρ φ').
        assert (Hmypf: vars_of φ' ⊆ vars_of ρ).
        {
            clear -pf Ht'φ'.
            rewrite vars_of_t_term in pf.
            rewrite elem_of_subseteq in pf.
            rewrite elem_of_subseteq.
            intros x.
            specialize (pf x).
            rewrite elem_of_union_list in pf.
            intros HH.
            ltac1:(ospecialize (pf _)).
            {
                ltac1:(setoid_rewrite elem_of_list_fmap).
                exists (vars_of φ').
                split.
                {
                    exists φ'.
                    split>[reflexivity|].
                    rewrite elem_of_list_lookup.
                    exists i. assumption.
                }
                {
                    exact HH.
                }
            }
            exact pf.
        }
        specialize (X Hmypf).
        simpl in X.
        ltac1:(ospecialize (X _)).
        {
            clear - Ht'φ'.
            apply take_drop_middle in Ht'φ'.
            rewrite <- Ht'φ'.
            rewrite sum_list_with_app.
            simpl.
            ltac1:(lia).
        }
        specialize (X Σ ρ φ' Hmypf erefl erefl).
        unfold satisfies in X; simpl in X.

        clear Helper.
        lazy_match! goal with
        | [ |- sat2B _ (TermOverBoV_eval _ _ ?x) _] => remember $x as mypf
        end.
        remember ((pflookup l i (pfmap_lookup_Some_lt HH))) as pfl.
        (*
        assert(Hil: i < length l).
        {
            apply lookup_lt_Some in Ht'φ'.
            exact Ht'φ'.
        }
        *)
        assert (Hφ': φ' = `pfl).
        {
            subst pfl.
            assert(Htmp := @pflookup_spec _ l i (pfmap_lookup_Some_lt HH)).
            ltac1:(rewrite Ht'φ' in Htmp).
            injection Htmp as Htmp'.
            symmetry in Htmp'.
            exact Htmp'.
        }
        subst φ'.
        ltac1:(replace mypf with Hmypf).
        {
            apply X.
        }
        {
            apply proof_irrelevance.
        }        
    }
    {
        inversion H; subst; clear H.
        unfold satisfies; simpl.
        ltac1:(simp sat2B).
        unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar.
        exact pf'.
    }
    {
        inversion H; subst; clear H.
        ltac1:(exfalso). clear Heqcall.
        unfold vars_of in pf; simpl in pf.
        unfold vars_of in pf; simpl in pf.
        rewrite singleton_subseteq_l in pf.
        ltac1:(rewrite elem_of_dom in pf).
        ltac1:(rewrite pf' in pf).
        unfold is_Some in pf.
        destruct pf as [x0 HContra].
        inversion HContra.
    }
Qed.

Lemma TermOverBoV_eval__insert
    {Σ : StaticModel}
    (ρ : Valuation2)
    (x : variable)
    (g : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    pf
    :
    TermOverBoV_eval (<[x := g]>ρ) (t_over (bov_variable x)) pf = g
.
Proof.
    ltac1:(funelim (TermOverBoV_eval _ _ _)).
    {
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        clear Heqcall.
        ltac1:(repeat case_match); subst.
        {
            clear H. ltac1:(rename e0 into H1).
            unfold Valuation2 in *.
            rewrite lookup_insert in H1.
            ltac1:(simplify_eq/=).
        }
        {
            clear H. ltac1:(rename e0 into H1).
            unfold Valuation2 in *.
            ltac1:(exfalso).
            rewrite lookup_insert in H1.
            inversion H1.
        }
    }
    {
        clear Heqcall.
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        ltac1:(repeat case_match; subst).
        {
            clear H1. ltac1:(rename e0 into H1).
            unfold Valuation2 in *.
            rewrite lookup_insert in H1.
            ltac1:(simplify_eq/=).
        }
        {
            clear H1. ltac1:(rename e0 into H1).
            ltac1:(exfalso).
            unfold Valuation2 in *.
            rewrite lookup_insert in H1.
            ltac1:(simplify_eq/=).
        }
    }
    {
        clear Heqcall.
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        ltac1:(repeat case_match; subst).
        {
            clear H0. ltac1:(rename e0 into H1).
            unfold Valuation2 in *.
            rewrite lookup_insert in H1.
            ltac1:(simplify_eq/=).
            reflexivity.
        }
        {
            clear H0. ltac1:(rename e0 into H1).
            unfold Valuation2 in *.
            ltac1:(exfalso).
            rewrite lookup_insert in H1.
            ltac1:(simplify_eq/=).
        }
    }
    {
        clear Heqcall.
        ltac1:(simp TermOverBoV_eval).
        unfold TermOverBoV_eval_unfold_clause_2.
        ltac1:(repeat case_match; subst).
        {
            clear H0. ltac1:(rename e0 into H1).
            unfold Valuation2 in *.
            rewrite lookup_insert in H1.
            ltac1:(simplify_eq/=).
            reflexivity.
        }
        {
            clear H0. ltac1:(rename e0 into H1).
            unfold Valuation2 in *.
            ltac1:(exfalso).
            rewrite lookup_insert in H1.
            ltac1:(simplify_eq/=).
        }
    }
Qed.


Lemma vars_of_sat_tobov
    {Σ : StaticModel}
    (φ : TermOver BuiltinOrVar)
    (ρ : Valuation2)
    (g : TermOver builtin_value)
    :
    satisfies ρ g φ ->
    vars_of φ ⊆ vars_of ρ
.
Proof.
    unfold satisfies; simpl.
    revert g.
    induction φ; intros g HH; simpl in *.
    {
        ltac1:(simp sat2B in HH).
        destruct a; simpl in HH; simpl in *; subst.
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold Valuation2 in *.
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            rewrite elem_of_singleton in Hx0.
            subst.
            rewrite elem_of_dom.
            exists g.
            exact HH.
        }
    }
    {
        unfold Valuation2 in *.
        ltac1:(rewrite vars_of_t_term).
        rewrite elem_of_subseteq.
        intros x Hx.
        rewrite elem_of_union_list in Hx.
        destruct Hx as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst.
        rewrite Forall_forall in H.
        specialize (H _ H2y).
        destruct g;
            ltac1:(simp sat2B in HH).
        { destruct HH. }
        destruct HH as [HH1 [HH2 HH3]].
        subst.
        rewrite elem_of_list_lookup in H2y.
        destruct H2y as [i Hi].
        specialize (HH3 i).
        destruct (l0 !! i) eqn:Heq.
        {
            specialize (HH3 t y ltac:(assumption) erefl).
            specialize (H _ HH3).
            ltac1:(set_solver).
        }
        {
            apply lookup_ge_None in Heq.
            apply lookup_lt_Some in Hi.
            ltac1:(exfalso).
            unfold TermOver in *.
            ltac1:(lia).
        }
    }
Qed.    


Lemma vars_of__TermOverBoV_subst__varless
    {Σ : StaticModel} c x v
    :
    vars_of v = ∅ ->
    vars_of (TermOverBoV_subst c x v) = vars_of c ∖ {[x]}
.
Proof.
    induction c; simpl in *; intros HH.
    {
        destruct a.
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            unfold vars_of; simpl.
            unfold vars_of; simpl.
            destruct (decide (x = x0)).
            {
                subst.
                ltac1:(set_solver).
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                ltac1:(set_solver).
            }
        }
    }
    {
        unfold TermOver in *.
        rewrite vars_of_t_term.
        rewrite vars_of_t_term.
        apply set_eq.
        revert HH H.
        induction l; intros HH H.
        {
            intros x0. simpl. ltac1:(set_solver).
        }
        {
            intros x0.
            specialize (IHl HH).
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            specialize (H1 HH).
            ltac1:(set_solver).
        }
    }
Qed.


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
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        ltac1:(set_solver).
        }
    }
    {
        revert HH1 H.
        unfold vars_of; simpl.
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
            unfold vars_of; simpl.
            unfold vars_of in HH2; simpl in HH2.
            rewrite HH2. clear HH2.
            destruct (decide (x ∈ (⋃ (vars_of <$> l)))) as [Hin2 |Hnotin2].
            {
            specialize (IHl Hin2 HH3).
            unfold vars_of in IHl; simpl in IHl.
            unfold fmap in IHl.
            unfold fmap.
            rewrite IHl.
            unfold vars_of ; simpl.
            unfold vars_of ; simpl.
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
            unfold vars_of . simpl.
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
            unfold vars_of ; simpl.
            unfold vars_of  in IHl; simpl in IHl.
            rewrite subst_notin2.
            {
                unfold fmap in IHl; simpl in IHl.
                unfold vars_of ; simpl.
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


Lemma vars_of_TermOverBoV_subst__approx
    {Σ : StaticModel}
    (t t' : TermOver BuiltinOrVar)
    (x : variable)
:
    vars_of (TermOverBoV_subst t x t') ⊆
    vars_of t' ∪ (vars_of t ∖ {[x]})
.
Proof.
    induction t; simpl in *.
    {
        destruct a; simpl in *.
        {
            ltac1:(set_solver).
        }
        {
            destruct (decide (x = x0)).
            {
                subst. ltac1:(set_solver).
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                ltac1:(set_solver).
            }
        }
    }
    {
        rewrite vars_of_t_term.
        rewrite Forall_forall in H.
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        rewrite elem_of_union_list in Hx0.
        destruct Hx0 as [X [H1X H2X]].
        ltac1:(replace map with (@fmap _ list_fmap) in H1X by reflexivity).
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst X.
        rewrite elem_of_list_fmap in H2y.
        destruct H2y as [y0 [H1y0 H2y0]].
        subst y.
        specialize (H y0 H2y0).
        ltac1:(rewrite elem_of_subseteq in H).
        specialize (H x0 H2X).
        rewrite vars_of_t_term.
        rewrite (elem_of_union) in H.
        destruct H as [H|H].
        {
            ltac1:(set_solver).
        }
        {
            rewrite elem_of_union. right.
            rewrite elem_of_difference in H.
            destruct H as [H1 H2].
            rewrite elem_of_difference.
            split>[|assumption].
            rewrite elem_of_union_list.
            exists (vars_of y0).
            rewrite elem_of_list_fmap.
            split>[|assumption].
            exists y0.
            split>[reflexivity|].
            assumption.
        }
    }
Qed.


Lemma vars_of_TermOverBoV_subst_e2__approx
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    (t' : TermOver Expression2)
    (x : variable)
:
    vars_of (TermOverBoV_subst_expr2 t x t') ⊆
    vars_of t' ∪ (vars_of t ∖ {[x]})
.
Proof.
    induction t; simpl in *.
    {
        destruct a; simpl in *.
        {
            ltac1:(set_solver).
        }
        {
            unfold TermOverBoV_subst_expr2. simpl.
            destruct (decide (x = x0)).
            {
                subst. ltac1:(set_solver).
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                ltac1:(set_solver).
            }
        }
    }
    {
        rewrite vars_of_t_term.
        rewrite Forall_forall in H.
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        unfold TermOverBoV_subst_expr2 in Hx0.
        simpl in Hx0.
        rewrite vars_of_t_term_e in Hx0.
        rewrite elem_of_union_list in Hx0.
        destruct Hx0 as [X [H1X H2X]].
        ltac1:(replace map with (@fmap _ list_fmap) in H1X by reflexivity).
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst X.
        rewrite elem_of_list_fmap in H2y.
        destruct H2y as [y0 [H1y0 H2y0]].
        subst y.
        specialize (H y0 H2y0).
        ltac1:(rewrite elem_of_subseteq in H).
        specialize (H x0 H2X).
        rewrite (elem_of_union) in H.
        destruct H as [H|H].
        {
            ltac1:(set_solver).
        }
        {
            rewrite elem_of_union. right.
            rewrite elem_of_difference in H.
            destruct H as [H1 H2].
            rewrite elem_of_difference.
            split>[|assumption].
            rewrite elem_of_union_list.
            exists (vars_of y0).
            rewrite elem_of_list_fmap.
            split>[|assumption].
            exists y0.
            split>[reflexivity|].
            assumption.
        }
    }
Qed.

