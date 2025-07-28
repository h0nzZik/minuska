From Minuska Require Import
    prelude
    spec
.



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



Section custom_induction_principle_2.

    Context
        {Σ : StaticModel}
    .

    Lemma Expression2_eqdec : EqDecision Expression2.
    Proof.
        ltac1:(unshelve(refine (fix go (e1 e2 : Expression2) : {e1 = e2} + {e1 <> e2} :=
            match e1 with
            | e_ground g1 =>
                match e2 with
                | e_ground g2 =>
                    match (decide (g1 = g2)) with
                    | left _ => left _
                    | right _ => right _
                    end
                | _ => right _
                end
            | e_variable x1 =>
                match e2 with
                | e_variable x2 =>
                    match (decide (x1 = x2)) with
                    | left _ => left _
                    | right _ => right _
                    end
                | _ => right _
                end
            | e_query q1 l1 => (
                match e2 with
                | e_query q2 l2 => (
                    match (decide (q1 = q2)) with
                    | right _ => right _
                    | left _ => (
                        let tmp := (
                            fix go' (l1' l2' : list Expression2) : {l1' = l2'} + {l1' <> l2'} :=
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
                    )
                    end
                )
                | _ => right _
                end
            )
            | e_fun f1 l1 => (
                match e2 with
                | e_fun f2 l2 => (
                    match (decide (f1 = f2)) with
                    | left _ => (
                        let tmp := (
                            fix go' (l1' l2' : list Expression2) : {l1' = l2'} + {l1' <> l2'} :=
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
                        )
                    | right _ => right _
                    end
                    )
                | _ => right _
                end
                )
            | e_attr a1 l1 => (
                match e2 with
                | e_attr a2 l2 => (
                    match (decide (a1 = a2)) with
                    | left _ => (
                        let tmp := (
                            fix go' (l1' l2' : list Expression2) : {l1' = l2'} + {l1' <> l2'} :=
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
                    )
                    | right _ => right _
                    end
                )
                | _ => right _
                end
            )
            end
        )); abstract(congruence)).
    Defined.

    Fixpoint Expression2_rect
        (P : Expression2 -> Type)
        (true_for_ground : forall e, P (e_ground e))
        (true_for_var : forall x, P (e_variable x))
        (preserved_by_fun :
            forall
                (f : builtin_function_symbol)
                (l : list Expression2),
                (forall x, x ∈ l -> P x) ->
                P (e_fun f l)
        )
        (preserved_by_query :
            forall
                (q : QuerySymbol)
                (l : list Expression2),
                (forall x, x ∈ l -> P x) ->
                P (e_query q l)
        )
        (preserved_by_attribute :
            forall
                (q : AttributeSymbol)
                (l : list Expression2),
                (forall x, x ∈ l -> P x) ->
                P (e_attr q l)
        )
        (e : Expression2)
    :
        P e :=
    match e with
    | e_ground g => true_for_ground g
    | e_variable x => true_for_var x
    | e_fun f l =>  preserved_by_fun f l
        (fun x pf => 
            (fix go (l' : list Expression2) : x ∈ l' -> P x :=
            match l' as l'0 return x ∈ l'0 -> P x with
            | nil => fun pf' => match not_elem_of_nil _ pf' with end
            | y::ys => 
                match (Expression2_eqdec x y) return x ∈ (y::ys) -> P x with
                | left e => fun pf' => (@eq_rect Expression2 y P (Expression2_rect P true_for_ground true_for_var preserved_by_fun preserved_by_query preserved_by_attribute y) x (eq_sym e)) 
                | right n => fun pf' =>
                    let H := @elem_of_next _ _ _ _ n pf' in
                    go ys H
                end
            end
            ) l pf
        )
    | e_query q l => preserved_by_query q l
        (fun x pf => 
            (fix go (l' : list Expression2) : x ∈ l' -> P x :=
            match l' as l'0 return x ∈ l'0 -> P x with
            | nil => fun pf' => match not_elem_of_nil _ pf' with end
            | y::ys => 
                match (Expression2_eqdec x y) return x ∈ (y::ys) -> P x with
                | left e => fun pf' => (@eq_rect Expression2 y P (Expression2_rect P true_for_ground true_for_var preserved_by_fun preserved_by_query preserved_by_attribute y) x (eq_sym e)) 
                | right n => fun pf' =>
                    let H := @elem_of_next _ _ _ _ n pf' in
                    go ys H
                end
            end
            ) l pf
        )
    | e_attr a l => preserved_by_attribute a l
        (fun x pf => 
            (fix go (l' : list Expression2) : x ∈ l' -> P x :=
            match l' as l'0 return x ∈ l'0 -> P x with
            | nil => fun pf' => match not_elem_of_nil _ pf' with end
            | y::ys => 
                match (Expression2_eqdec x y) return x ∈ (y::ys) -> P x with
                | left e => fun pf' => (@eq_rect Expression2 y P (Expression2_rect P true_for_ground true_for_var preserved_by_fun preserved_by_query preserved_by_attribute y) x (eq_sym e)) 
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
Existing Instance Expression2_eqdec.

#[export]
Instance SideCondition_eqdec
    {Σ : StaticModel}
    : EqDecision (SideCondition)
.
Proof. ltac1:(solve_decision). Defined.

#[export]
Instance BasicEffect0_eqdec
    {Σ : StaticModel}
    :
    EqDecision BasicEffect0
.
Proof.
    ltac1:(solve_decision).
Defined.


#[export]
Instance RewritingRule2_eqdec
    {Σ : StaticModel}
    {Label : Set}
    {_EA : EqDecision Label}
    : EqDecision (RewritingRule2 Label)
.
Proof. ltac1:(solve_decision). Defined.


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
| e_fun f l => e_fun f ((fun e1 => Expression2_subst e1 x e') <$> l)
| e_query q l => e_query q ((fun e1 => Expression2_subst e1 x e') <$> l)
| e_attr a l => e_attr a ((fun e1 => Expression2_subst e1 x e') <$> l)
end
.

Fixpoint SideCondition_subst
    {Σ : StaticModel}
    (c : SideCondition)
    (x : variable)
    (e' : Expression2)
    : SideCondition
:=
    match c with
    | sc_true => sc_true
    | sc_false => sc_false
    | sc_pred p es => sc_pred p ((fun e1 => Expression2_subst e1 x e') <$> es)
    | sc_npred p es => sc_npred p ((fun e1 => Expression2_subst e1 x e') <$> es)
    | sc_hpred p es => sc_hpred p ((fun e1 => Expression2_subst e1 x e') <$> es)
    | sc_and l r => sc_and (SideCondition_subst l x e') (SideCondition_subst r x e')
    | sc_or l r => sc_or (SideCondition_subst l x e') (SideCondition_subst r x e')
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





Lemma TermOver_size_not_zero
    {Σ : StaticModel}
    {A : Type}
    (t : TermOver A)
    : TermOver_size t <> 0
.
Proof.
    destruct t; simpl; ltac1:(lia).
Qed.



Fixpoint E_to_tree
    {Σ : StaticModel}
    (e : Expression2)
    :
    (gen_tree ((TermOver' builtin_value)+(variable)+(builtin_function_symbol)+(QuerySymbol)+(AttributeSymbol))%type)
:=
    match e with
    | e_ground a => GenLeaf (inl (inl (inl (inl a))))
    | e_variable x => GenLeaf (inl (inl (inl (inr x))))
    | e_fun f l =>
        let l' := E_to_tree <$> l in
        GenNode 0 ((GenLeaf (inl (inl (inr f))))::l')
    | e_query q l =>
        let l' := E_to_tree <$> l in
        GenNode 1 ((GenLeaf (inl (inr q)))::l')
    | e_attr a l =>
        let l' := E_to_tree <$> l in
        GenNode 2 ((GenLeaf (inr a))::l')
    end
.

Fixpoint E_of_tree
    {Σ : StaticModel}
    (t : gen_tree ((TermOver' builtin_value)+(variable)+(builtin_function_symbol)+(QuerySymbol)+(AttributeSymbol))%type)
    : option Expression2
:=
    match t with
    | GenLeaf (inl (inl (inl (inl a)))) => Some (e_ground a)
    | GenLeaf (inl (inl (inl (inr x)))) => Some (e_variable x)
    | GenNode 0 ((GenLeaf (inl (inl (inr f))))::l') =>
        l ← list_collect (E_of_tree <$> l');
        Some (e_fun f l)
    | GenNode 1 ((GenLeaf (inl (inr q)))::l') =>
        l ← list_collect (E_of_tree <$> l');
        Some (e_query q l)
    | GenNode 2 ((GenLeaf (inr a))::l') =>
        l ← list_collect (E_of_tree <$> l');
        Some (e_attr a l)
    | _ => None
    end
.


Lemma E_from_to_tree
    {Σ : StaticModel}
    :
    forall e,
        E_of_tree (E_to_tree e) = Some e
.
Proof.
    intros e; induction e.
    { reflexivity. }
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
Instance Expression2_countable
    {Σ : StaticModel}
    :
    Countable Expression2
.
Proof.
    apply inj_countable with (
        f := E_to_tree
    )(
        g := E_of_tree
    ).
    {
        intros. apply E_from_to_tree.
    }
Defined.

(* 
Definition BoV_to_Expr2
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : Expression2
:=
    match bov with
    | bov_builtin b => (e_ground (t_over b))
    | bov_variable x => e_variable x
    end
. *)