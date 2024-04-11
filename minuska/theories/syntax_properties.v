From Minuska Require Import
    prelude
    spec_syntax
.

Require Import Coq.Logic.FunctionalExtensionality.

Require Export Minuska.varsof.

Section eqdec.

    #[export]
    Instance PreTerm'_eqdec
        {T0 : Type}
        {_T0ED : EqDecision T0}
        (builtin : Type)
        {builtin_dec : EqDecision builtin}
        : EqDecision (PreTerm' T0 builtin)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance Term'_eqdec
        {A : Type}
        {A_dec : EqDecision A}
        (T : Type)
        {T_dec : EqDecision T}
        : EqDecision (Term' A T)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance Expression_eqdec {Σ : StaticModel}
        : EqDecision (Expression)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance LeftRight_eqdec
        : EqDecision LeftRight
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Program Instance LeftRight_fin
        : Finite LeftRight
    := {|
        enum := [LR_Left;LR_Right];
    |}.
    Next Obligation.
        ltac1:(compute_done).
    Qed.
    Next Obligation.
        destruct x;
        ltac1:(compute_done).
    Qed.
    Fail Next Obligation.

    #[export]
    Instance atomicProposition_eqdec {Σ : StaticModel}
        : EqDecision AtomicProposition
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance BuiltinOrVar_eqdec {Σ : StaticModel}
        : EqDecision BuiltinOrVar
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance GroundTerm_eqdec {Σ : StaticModel}
        : EqDecision GroundTerm
    .
    Proof.
        intros e1 e2.
        apply Term'_eqdec.
        apply builtin_value_eqdec.
    Defined.

    #[export]
    Instance  SymbolicTerm_eqdec {Σ : StaticModel}
        : EqDecision SymbolicTerm
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance  SideCondition_eqdec {Σ : StaticModel}
        : EqDecision SideCondition
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance ExpressionTerm_eqdec {Σ : StaticModel}
        : EqDecision ExpressionTerm
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance RewritingRule_eqdec
        {Σ : StaticModel}
        (Act : Set)
        {_aD : EqDecision Act}
        : EqDecision (RewritingRule Act)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

End eqdec.


Section countable.

    Fixpoint PreTerm'_to_gen_tree
        (symbol : Type)
        {symbol_eqdec : EqDecision symbol}
        {symbol_countable : Countable symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : PreTerm' symbol builtin)
        : gen_tree symbol
    :=
    match a with
    | (pt_operator s) => GenLeaf s
    | (pt_app_operand aps b) =>
        (
            let x := (encode (0, encode b)) in
            GenNode (Pos.to_nat x) ([PreTerm'_to_gen_tree symbol builtin aps;PreTerm'_to_gen_tree symbol builtin aps(* we duplicate it to make the reverse simpler*)])
        )
    | (pt_app_ao aps1 aps2)
        => (
            let xd := (1, encode 0) in
            let x := (encode xd) in
            GenNode (Pos.to_nat x) ([PreTerm'_to_gen_tree _ _ aps1; PreTerm'_to_gen_tree _ _ aps2])
        )
    end.

    Fixpoint PreTerm'_of_gen_tree
        (symbol : Type)
        {symbol_eqdec : EqDecision symbol}
        {symbol_countable : Countable symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (t : gen_tree symbol)
        : option (PreTerm' symbol builtin)
    :=
    match t with
    | (GenLeaf s)
        => Some (pt_operator s)
    | (GenNode n [gt1;gt2]) =>
        let d := (@decode (nat*positive) _ _ (Pos.of_nat n)) in
        match d with
            | Some (0, pb) =>
                let d' := (@decode builtin _ _ pb) in
                match d' with
                | Some b =>
                    let d'' := (PreTerm'_of_gen_tree symbol builtin gt1) in
                    match d'' with 
                    | Some as1 => Some (pt_app_operand as1 b)
                    | _ => None
                    end
                | _ => None
                end
            | Some (1, _) =>
                let d'1 := PreTerm'_of_gen_tree symbol builtin gt1 in
                let d'2 := PreTerm'_of_gen_tree symbol builtin gt2 in
                match d'1, d'2 with
                | Some aps1, Some aps2 => Some (pt_app_ao aps1 aps2)
                | _, _ => None
                end
            | _ => None
            end
    | _ => None
    end
    .

    Lemma PreTerm'_of_to_gen_tree
        (symbol : Type)
        {symbol_eqdec : EqDecision symbol}
        {symbol_countable : Countable symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : PreTerm' symbol builtin)
        : PreTerm'_of_gen_tree symbol builtin (PreTerm'_to_gen_tree symbol builtin a) = Some a
    .
    Proof.
        induction a; simpl.
        { reflexivity. }
        {
            ltac1:(rewrite ! Pos2Nat.id decode_encode).
            rewrite decode_encode.
            rewrite IHa.
            reflexivity.
        }
        {
            rewrite IHa1.
            rewrite IHa2.
            reflexivity.
        }
    Qed.

    #[export]
    Instance PreTerm'_countable
        (symbol_set : Type)
        {symbols_eqdec : EqDecision symbol_set}
        {symbols_countable : Countable symbol_set}
        (builtin_set : Type)
        {builtin_eqdec : EqDecision builtin_set}
        {builtin_countable : Countable builtin_set}
        : Countable (PreTerm' symbol_set builtin_set)
    .
    Proof.
        apply inj_countable
        with
            (f := PreTerm'_to_gen_tree symbol_set builtin_set)
            (g := PreTerm'_of_gen_tree symbol_set builtin_set)
        .
        intros x.
        apply PreTerm'_of_to_gen_tree.
    Defined.

    Definition Term'_to_gen_tree
        (symbol : Type)
        {symbol_eqd : EqDecision symbol}
        {symbol_cnt : Countable symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (e : Term' symbol builtin)
        : gen_tree (builtin + (PreTerm' symbol builtin))%type
    :=
    match e with
    | (term_operand b) => GenLeaf (inl _ b)
    | (term_preterm s) => GenLeaf (inr _ s)
    end
    .

    Definition Term'_from_gen_tree
        (symbol : Type)
        {symbol_eqd : EqDecision symbol}
        {symbol_cnt : Countable symbol}
        (builtin : Type)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (t : gen_tree (builtin+(PreTerm' symbol builtin))%type)
        :  option (Term' symbol builtin)
    :=
    match t with
    | (GenLeaf (inl _ b)) => Some (term_operand b)
    | (GenLeaf (inr _ s)) => Some (term_preterm s)
    | _ => None
    end
    .

    Lemma Term'_to_from_gen_tree
        (symbol : Type)
        {symbol_eqd : EqDecision symbol}
        {symbol_cnt : Countable symbol}
        (builtin : Type)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (e : Term' symbol builtin)
        : Term'_from_gen_tree symbol builtin (Term'_to_gen_tree symbol builtin e) = Some e
    .
    Proof.
        destruct e; reflexivity.
    Qed.

    #[export]
    Instance Term'_countable
        (symbol_set : Type)
        {symbol_eqd : EqDecision symbol_set}
        {symbol_cnt : Countable symbol_set}
        (builtin_set : Type)
        {builtin_eqdec : EqDecision builtin_set}
        {builtin_countable : Countable builtin_set}
        : Countable (Term' symbol_set builtin_set)
    .
    Proof.
        apply inj_countable
        with
            (f := Term'_to_gen_tree symbol_set builtin_set)
            (g := Term'_from_gen_tree symbol_set builtin_set)
        .
        intros x.
        apply Term'_to_from_gen_tree.
    Defined.

End countable.


Fixpoint PreTerm'_fmap
    {A B C : Type}
    (f : B -> C)
    (ao : PreTerm' A B)
    : PreTerm' A C
:=
match ao with
| pt_operator o => pt_operator o
| pt_app_operand ao' x => pt_app_operand (PreTerm'_fmap f ao') (f x)
| pt_app_ao ao1 ao2 => pt_app_ao (PreTerm'_fmap f ao1) (PreTerm'_fmap f ao2)
end.

#[export]
Instance PreTerm'_A_B_fmap (A : Type)
    : FMap (PreTerm' A)
    := @PreTerm'_fmap A
.


Definition Term'_fmap
    {A B C : Type}
    (f : B -> C)
    (aoo : Term' A B)
    : Term' A C
:=
match aoo with
| term_preterm ao => term_preterm (f <$> ao)
| term_operand o => term_operand (f o)
end.


#[global]
Instance Term'_A_B_fmap (A : Type)
    : FMap (Term' A)
    := @Term'_fmap A
.

#[global]
Instance Term_symbol_fmap
    {Σ : StaticModel}
    : FMap (Term' symbol)
.
Proof.
    apply Term'_A_B_fmap.
Defined.


Fixpoint PreTerm'_collapse_option
    {A B : Type}
    (ao : PreTerm' A (option B))
    : option (PreTerm' A B)
:=
match ao with
| pt_operator o =>
    Some (pt_operator o)

| pt_app_operand ao' x =>
    ao'' ← PreTerm'_collapse_option ao';
    x'' ← x;
    Some (pt_app_operand ao'' x'')

| pt_app_ao ao1 ao2 =>
    ao1'' ← PreTerm'_collapse_option ao1;
    ao2'' ← PreTerm'_collapse_option ao2;
    Some (pt_app_ao ao1'' ao2'')
end.


Definition Term'_collapse_option
    {A B : Type}
    (aoo : Term' A (option B))
    : option (Term' A B)
:=
match aoo with
| term_preterm ao =>
    tmp ← PreTerm'_collapse_option ao;
    Some (term_preterm tmp)
| term_operand op =>
    tmp ← op;
    Some (term_operand tmp)
end.


Fixpoint PreTerm'_zipWith
    {A B C D : Type}
    (fa : A -> A -> A)
    (fbc : B -> C -> D)
    (f1 : PreTerm' A B -> C -> D)
    (f2 : B -> PreTerm' A C -> D)
    (ao1 : PreTerm' A B)
    (ao2 : PreTerm' A C)
    : PreTerm' A D
:=
match ao1,ao2 with
| pt_operator o1, pt_operator o2 => pt_operator (fa o1 o2)
| pt_operator o1, pt_app_operand app2 op2 =>
    pt_operator o1
| pt_operator o1, pt_app_ao app21 app22 =>
    pt_operator o1
| pt_app_operand app1 op1, pt_app_operand app2 op2 =>
    pt_app_operand
        (PreTerm'_zipWith fa fbc f1 f2 app1 app2)
        (fbc op1 op2)
| pt_app_operand app1 op1, pt_operator o2 =>
    pt_operator o2
| pt_app_operand app1 op1, pt_app_ao app21 app22 =>
    pt_app_operand
        ((PreTerm'_zipWith fa fbc f1 f2 app1 app21))
        (f2 op1 app22)
| pt_app_ao app11 app12, pt_app_ao app21 app22 =>
    pt_app_ao
        (PreTerm'_zipWith fa fbc f1 f2 app11 app21)
        (PreTerm'_zipWith fa fbc f1 f2 app12 app22)
| pt_app_ao app11 app12, pt_operator op2 =>
    pt_operator op2
| pt_app_ao app11 app12, pt_app_operand app21 op22 =>
    pt_app_operand 
        (PreTerm'_zipWith fa fbc f1 f2 app11 app21)
        (f1 app12 op22)
end.

Fixpoint AO'_getOperator {A B : Type}
    (ao : PreTerm' A B)
    : A :=
match ao with
| pt_operator o => o
| pt_app_operand ao' _ => AO'_getOperator ao'
| pt_app_ao ao' _ => AO'_getOperator ao'
end.

#[global]
Instance TermOver_eqdec
    {T : Type}
    {A : Type}
    {_edT : EqDecision T}
    {_edA : EqDecision A}
    :
    EqDecision (@TermOver' T A)
.
Proof.
    intros t1 t2.
    remember (uglify' t1) as ut1.
    remember (uglify' t2) as ut2.
    destruct (decide (ut1 = ut2)) as [Heq|Hneq]; subst.
    {
        apply (f_equal prettify) in Heq.
        rewrite (cancel prettify uglify') in Heq.
        rewrite (cancel prettify uglify') in Heq.
        subst.
        left. reflexivity.
    }
    {
        right. intros HContra. subst. apply Hneq.
        reflexivity.
    }
Defined.


#[global]
Instance TermOver_count
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
    ltac1:(unshelve(eapply inj_countable)).
    { apply (Term' T A). }
    { apply uglify'. }
    {
        intros t. apply prettify in t.
        apply Some. exact t.
    }
    { apply _. }
    {
        intros x. simpl.
        rewrite (cancel prettify uglify').
        reflexivity.
    }
Defined.

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

(* TODO *)
Section custom_induction_principle_2.

    Context
        {Σ : StaticModel}
        {A : Type}
        {_edA : EqDecision A}
        (P : TermOver A -> Type)
        (true_for_over : forall a, P (t_over a) )
        (preserved_by_term :
            forall
                (s : symbol)
                (l : list (TermOver A)),
                (forall x, x ∈ l -> P x) ->
                P (t_term s l)
        )
    .

    Fixpoint TermOver_rect (p : TermOver A) : P p :=
    match p with
    | t_over a => true_for_over a
    | t_term s l =>  preserved_by_term s l
        (fun x pf => 
            (fix go (l' : list (TermOver A)) : x ∈ l' -> P x :=
            match l' as l'0 return x ∈ l'0 -> P x with
            | nil => fun pf' => match not_elem_of_nil _ pf' with end
            | y::ys => 
                match (decide (x = y)) return x ∈ (y::ys) -> P x with
                | left e => fun pf' => (@eq_rect (TermOver A) y P (TermOver_rect y) x (eq_sym e)) 
                | right n => fun pf' =>
                    let H := @elem_of_next _ _ _ _ n pf' in
                    go ys H
                end
            end
            ) l pf
        )
    end.

End custom_induction_principle_2.


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
Proof. ltac1:(solve_decision). Defined.


Lemma compose_prettify_uglify
    {T : Type}
    (A : Type)
    :
    (@prettify T A) ∘ uglify' = id
.
Proof.
    apply functional_extensionality.
    intros x.
    unfold compose.
    rewrite (cancel prettify uglify').
    reflexivity.
Qed.

Lemma compose_uglify_prettify
    (T A : Type)
    :
    uglify' ∘ (@prettify T A) = id
.
Proof.
    apply functional_extensionality.
    intros x.
    unfold compose.
    rewrite (cancel uglify' prettify).
    reflexivity.
Qed.


Lemma fmap_prettify_uglify_list
    {Σ : StaticModel}
    {T : Type}
    (l : list (TermOver T))
    :
    (prettify <$> (uglify' <$> l)) = l
.
Proof.
    rewrite <- list_fmap_compose.
    rewrite compose_prettify_uglify.
    rewrite list_fmap_id.
    reflexivity.
Qed.

Lemma fmap_uglify_prettify_list
    {Σ : StaticModel}
    {T : Type}
    (l : list (Term' symbol T))
    :
    uglify' <$> (prettify <$> l) = l
.
Proof.
    rewrite <- list_fmap_compose.
    rewrite compose_uglify_prettify.
    rewrite list_fmap_id.
    reflexivity.
Qed.


Lemma fmap_prettify_uglify_option
    {Σ : StaticModel}
    {T : Type}
    (o : option (TermOver T))
    :
    (prettify <$> (uglify' <$> o)) = o
.
Proof.
    rewrite <- option_fmap_compose.
    rewrite compose_prettify_uglify.
    rewrite option_fmap_id.
    reflexivity.
Qed.

Lemma fmap_uglify_prettify_option
    {Σ : StaticModel}
    {T : Type}
    (o : option (Term' symbol T))
    :
    uglify' <$> (prettify <$> o) = o
.
Proof.
    rewrite <- option_fmap_compose.
    rewrite compose_uglify_prettify.
    rewrite option_fmap_id.
    reflexivity.
Qed.
