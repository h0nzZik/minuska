From Minuska Require Import
    prelude
    spec
.


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
