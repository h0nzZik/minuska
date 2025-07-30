From Minuska Require Import
    prelude
    spec
    basic_properties
.




#[universes(polymorphic=yes, cumulative=yes)]
Inductive PreTerm' (operator : Type) (operand : Type)
: Type
:=
| pt_operator (s : operator)
| pt_app_operand
    (aps : PreTerm' operator operand)
    (b : operand) 
| pt_app_ao
    (aps : PreTerm' operator operand)
    (x : PreTerm' operator operand)
.


#[universes(polymorphic=yes, cumulative=yes)]
Variant Term'
    (Operator : Type)
    (Operand : Type)
    : Type :=
| term_preterm (ao : PreTerm' Operator Operand)
| term_operand (operand : Operand)
.


Arguments term_operand {Operator Operand}%_type_scope operand.
Arguments term_preterm {Operator Operand}%_type_scope ao.

Arguments pt_operator {operator operand}%_type_scope s.
Arguments pt_app_operand {operator operand}%_type_scope aps b.
Arguments pt_app_ao {operator operand}%_type_scope aps x.


Definition to_Term'
    {Σ : BackgroundModel}
    {T : Type}
    (x : ((T)+(PreTerm' TermSymbol T)))
    : Term' TermSymbol T
:=
match x with
| inl x' => term_operand x'
| inr x' => term_preterm x'
end
.

Definition helper {Σ : BackgroundModel} {T : Type} a b : PreTerm' TermSymbol T
    :=match b with
            | term_operand b' => pt_app_operand a b'
            | term_preterm b' => pt_app_ao a b'
            end.

Definition to_PreTerm'
    {Σ : BackgroundModel}
    {T : Type}
    (s : TermSymbol)
    (l : list ((Term' TermSymbol T)))
    : PreTerm' TermSymbol T
:=
    fold_left
        helper
        l
        (pt_operator s)
.

Lemma to_PreTerm'_app
    {Σ : BackgroundModel}
    {T : Type}
    (s : TermSymbol)
    (l1 l2 : list ((Term' TermSymbol T)))
    : to_PreTerm' s (l1 ++ l2) = fold_left helper l2 (to_PreTerm' s l1)
.
Proof.
    unfold to_PreTerm'.
    rewrite fold_left_app.
    reflexivity.
Qed.

Definition apply_TermSymbol'
    {Σ : BackgroundModel}
    {T : Type}
    (s : TermSymbol)
: 
    list ((Term' TermSymbol T)) ->
    Term' TermSymbol T
:=
    fun l =>
    (to_Term' (inr (to_PreTerm' ((s):TermSymbol) l)))
.

Definition to_Term''
    {T0 : Type}
    {T : Type}
    (x : ((T)+(PreTerm' T0 T)))
    : Term' T0 T
:=
match x with
| inl x' => term_operand x'
| inr x' => term_preterm x'
end
.

Definition helper'' {T0 : Type} {T : Type} a b : PreTerm' T0 T
    :=match b with
            | term_operand b' => pt_app_operand a b'
            | term_preterm b' => pt_app_ao a b'
            end.


Definition to_PreTerm''
    {T0 : Type}
    {T : Type}
    (s : T0)
    (l : list ((Term' T0 T)))
    : PreTerm' T0 T
:=
    fold_left
        helper''
        l
        (pt_operator s)
.


Definition apply_TermSymbol''
    {T0 : Type}
    {T : Type}
    (s : T0)
: 
    list ((Term' T0 T)) ->
    Term' T0 T
:=
    fun l =>
    (to_Term'' (inr (to_PreTerm'' ((s):T0) l)))
.



Fixpoint uglify'
    {T : Type}
    {A : Type}
    (t : @TermOver' T A)
    {struct t}
    : Term' T A
:=
    match t with
    | t_over a => term_operand a
    | t_term s l => apply_TermSymbol'' s (map uglify' l)
    end
.

Fixpoint PreTerm'_get_TermSymbol
    {T : Type}
    {A : Type}
    (pt : PreTerm' T A)
    : T
:=
    match pt with
    | pt_operator s => s
    | pt_app_operand x y => PreTerm'_get_TermSymbol x
    | pt_app_ao x y => PreTerm'_get_TermSymbol x
    end
.

Fixpoint prettify'
    {T : Type}
    {A : Type}
    (pt : PreTerm' T A)
    : @TermOver' T A
:=
    t_term
        (PreTerm'_get_TermSymbol pt) (
        ((fix go (pt : PreTerm' T A) : list (@TermOver' T A) :=
            match pt with
            | pt_operator _ => []
            | pt_app_operand x y => (go x)++[(t_over y)]
            | pt_app_ao x y => (go x)++[(prettify' y)]
            end
        ) pt))
.

Definition prettify
    {T : Type}
    {A : Type}
    (t : Term' T A)
    : ((@TermOver' T A))
:=
    match t with
    | term_preterm pt => (prettify' pt)
    | term_operand a => t_over a
    end
.

Lemma to_PreTerm''_app
    {T0 : Type}
    {T : Type}
    (s : T0)
    (l1 l2 : list ((Term' T0 T)))
    : to_PreTerm'' s (l1 ++ l2) = fold_left helper'' l2 (to_PreTerm'' s l1)
.
Proof.
    unfold to_PreTerm''.
    rewrite fold_left_app.
    reflexivity.
Qed.


#[global]
Instance cancel_prettify_uglify
    {T : Type}
    {A : Type}
    : Cancel eq (@prettify T A) (@uglify' T A)
.
Proof.
    intros x.
    induction x.
    {
        simpl. reflexivity.
    }
    {
        simpl.

        revert s H.
        induction l using rev_ind; intros s H; simpl.
        {
            reflexivity.
        }
        {
            assert (Hs: (PreTerm'_get_TermSymbol (to_PreTerm'' s (map uglify' l))) = s).
            {
                clear.
                induction l using rev_ind; simpl.
                { reflexivity. }
                {
                    unfold to_PreTerm''. simpl.
                    rewrite map_app. simpl.
                    rewrite fold_left_app. simpl.
                    destruct (uglify' x); apply IHl.
                }
            }

            apply Forall_app in H. destruct H as [H2 H1]. (*
            apply Forall_inv in H as H1.
            apply Forall_inv_tail in H as H2.*)
            specialize (IHl s H2).
            simpl.
            unfold helper.
            rewrite map_app.
            rewrite to_PreTerm''_app.
            simpl.
            unfold helper.
            destruct (uglify' x) eqn:Hux.
            {
                simpl.
                remember ((to_PreTerm'' s (map uglify' l)) ) as tpt.
                destruct tpt; simpl in *.
                {
                    inversion IHl; subst; clear IHl.
                    simpl in *.
                    apply Forall_inv in H1.
                    clear H0.
                    rewrite Hux in H1. simpl in H1.
                    subst x.
                    reflexivity.
                }
                {
                    simpl in *.
                    f_equal.
                    {
                        apply Hs.
                    }
                    {
                        inversion IHl; subst; clear IHl.
                        clear H0.
                        inversion H1; subst; clear H1. clear H4.
                        rewrite Hux in H3. simpl in H3. subst x.
                        reflexivity.
                    }
                }
                {
                    simpl in *.
                    f_equal.
                    {
                        apply Hs.
                    }
                    {
                        inversion IHl; subst; clear IHl.
                        clear H0.
                        inversion H1; subst; clear H1. clear H4.
                        rewrite Hux in H3. simpl in H3. subst x.
                        reflexivity.
                    }
                }
            }
            {
                simpl.
                remember ((to_PreTerm'' s (map uglify' l)) ) as tpt.
                destruct tpt; simpl in *.
                {
                    inversion IHl; subst; clear IHl.
                    simpl in *.
                    apply Forall_inv in H1.
                    clear H0.
                    rewrite Hux in H1. simpl in H1.
                    subst x.
                    reflexivity.
                }
                {
                    simpl in *.
                    f_equal.
                    {
                        apply Hs.
                    }
                    {
                        inversion IHl; subst; clear IHl.
                        clear H0.
                        inversion H1; subst; clear H1. clear H4.
                        rewrite Hux in H3. simpl in H3. subst x.
                        reflexivity.
                    }
                }
                {
                    simpl in *.
                    f_equal.
                    {
                        apply Hs.
                    }
                    {
                        inversion IHl; subst; clear IHl.
                        clear H0.
                        inversion H1; subst; clear H1. clear H4.
                        rewrite Hux in H3. simpl in H3. subst x.
                        reflexivity.
                    }
                }
            }
        }
    }
Qed.



#[global]
Instance cancel_uglify_prettify
    {T : Type}
    {A : Type}
    : Cancel eq (@uglify' T A) (@prettify T A)
.
Proof.
    intros x.
    destruct x; simpl.
    {
        induction ao; simpl.
        {
            reflexivity.
        }
        {
            unfold apply_TermSymbol''. simpl. f_equal.
            unfold to_PreTerm''.
            rewrite map_app.
            rewrite fold_left_app.
            simpl.
            f_equal.
            revert IHao.
            induction ao; intros IHao'.
            {
                simpl. reflexivity.
            }
            {
                simpl in *.
                unfold apply_TermSymbol'' in *. simpl in *.
                inversion IHao'; subst; clear IHao'.
                unfold to_PreTerm'' in *.
                rewrite map_app in H0.
                rewrite fold_left_app in H0.
                simpl in H0.
                inversion H0; subst; clear H0.
                simpl.
                rewrite H1.
                reflexivity.
            }
            {
                simpl in *.
                unfold apply_TermSymbol'' in *. simpl in *.
                inversion IHao'; subst; clear IHao'.
                unfold to_PreTerm'' in *.
                rewrite map_app in H0.
                rewrite fold_left_app in H0.
                simpl in H0.
                inversion H0; subst; clear H0.
                simpl.
                reflexivity.
            }
        }
        {
            unfold apply_TermSymbol''. simpl. f_equal.
            unfold to_PreTerm''.
            rewrite map_app.
            rewrite fold_left_app.
            simpl.
            rewrite IHao2.
            simpl.
            f_equal.


            revert IHao1 IHao2.
            induction ao1; intros IHao1' IHao2'.
            {
                simpl. reflexivity.
            }
            {
                simpl in *.
                unfold apply_TermSymbol'' in *. simpl in *.
                inversion IHao1'; subst; clear IHao1'.
                unfold to_PreTerm'' in *.
                rewrite map_app in H0.
                rewrite fold_left_app in H0.
                simpl in H0.
                inversion H0; subst; clear H0.
                simpl.
                rewrite H1.
                reflexivity.
            }
            {
                simpl in *.
                unfold apply_TermSymbol'' in *. simpl in *.
                inversion IHao1'; subst; clear IHao1'.
                unfold to_PreTerm'' in *.
                rewrite map_app in H0.
                rewrite fold_left_app in H0.
                simpl in H0.
                inversion H0; subst; clear H0.
                simpl.
                reflexivity.
            }
        }
    }
    {
        reflexivity.
    }
Qed.


Lemma uglify'_prettify'
    {Σ : BackgroundModel}
    {T : Type}
    (t : PreTerm' TermSymbol T)
    :
    uglify' (prettify' t) = term_preterm t
.
Proof.
    rewrite <- (cancel uglify' prettify (term_preterm t)).
    apply f_equal.
    simpl. reflexivity.
Qed.

Lemma map_uglify'_inj
    {Σ : BackgroundModel}
    {T : Type}
    (l1 l2 : list (@TermOver' TermSymbol T))
    :
    map uglify' l1 = map uglify' l2 ->
    l1 = l2
.
Proof.
    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
    intros H.
    apply list_fmap_eq_inj in H.
    exact H.
    apply cancel_inj.
Qed.


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

End eqdec.


Section countable.
    Check @encode.
    Fixpoint PreTerm'_to_gen_tree
        (TermSymbol : Type)
        {TermSymbol_eqdec : EqDecision TermSymbol}
        {TermSymbol_countable : Countable TermSymbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : PreTerm' TermSymbol builtin)
        : gen_tree (positive+TermSymbol)
    :=
    match a with
    | (pt_operator s) => GenLeaf (inr s)
    | (pt_app_operand aps b) =>
        (
            GenNode 0 ([GenLeaf (inl (@encode builtin T_eqdec T_countable b)); (PreTerm'_to_gen_tree TermSymbol builtin aps)])
        )
    | (pt_app_ao aps1 aps2)
        => (
            GenNode 1 ([(PreTerm'_to_gen_tree _ _ aps1); (PreTerm'_to_gen_tree _ _ aps2)])
        )
    end.

    Fixpoint PreTerm'_of_gen_tree
        (TermSymbol : Type)
        {TermSymbol_eqdec : EqDecision TermSymbol}
        {TermSymbol_countable : Countable TermSymbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (t : gen_tree (positive+TermSymbol))
        : option (PreTerm' TermSymbol builtin)
    :=
    match t with
    | (GenLeaf (inr s))
        => Some (pt_operator s)
    | (GenNode 0 [(GenLeaf (inl xb));gt]) =>
        b ← @decode builtin T_eqdec T_countable xb;
        aps ← PreTerm'_of_gen_tree TermSymbol builtin gt;
        Some (pt_app_operand aps b)
    | (GenNode 1 [gt1;gt2]) =>
        aps1 ← PreTerm'_of_gen_tree TermSymbol builtin gt1;
        aps2 ← PreTerm'_of_gen_tree TermSymbol builtin gt2;
        Some (pt_app_ao aps1 aps2)
    | _ => None
    end
    .

    Lemma PreTerm'_of_to_gen_tree
        (TermSymbol : Type)
        {TermSymbol_eqdec : EqDecision TermSymbol}
        {TermSymbol_countable : Countable TermSymbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : PreTerm' TermSymbol builtin)
        : PreTerm'_of_gen_tree TermSymbol builtin (PreTerm'_to_gen_tree TermSymbol builtin a) = Some a
    .
    Proof.
        induction a; simpl.
        { reflexivity. }
        {
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
        (TermSymbol_set : Type)
        {TermSymbols_eqdec : EqDecision TermSymbol_set}
        {TermSymbols_countable : Countable TermSymbol_set}
        (builtin_set : Type)
        {builtin_eqdec : EqDecision builtin_set}
        {builtin_countable : Countable builtin_set}
        : Countable (PreTerm' TermSymbol_set builtin_set)
    .
    Proof.
        apply inj_countable
        with
            (f := PreTerm'_to_gen_tree TermSymbol_set builtin_set)
            (g := PreTerm'_of_gen_tree TermSymbol_set builtin_set)
        .
        intros x.
        apply PreTerm'_of_to_gen_tree.
    Defined.

    Definition Term'_to_gen_tree
        (TermSymbol : Type)
        {TermSymbol_eqd : EqDecision TermSymbol}
        {TermSymbol_cnt : Countable TermSymbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (e : Term' TermSymbol builtin)
        : gen_tree (builtin + (PreTerm' TermSymbol builtin))%type
    :=
    match e with
    | (term_operand b) => GenLeaf (inl _ b)
    | (term_preterm s) => GenLeaf (inr _ s)
    end
    .

    Definition Term'_from_gen_tree
        (TermSymbol : Type)
        {TermSymbol_eqd : EqDecision TermSymbol}
        {TermSymbol_cnt : Countable TermSymbol}
        (builtin : Type)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (t : gen_tree (builtin+(PreTerm' TermSymbol builtin))%type)
        :  option (Term' TermSymbol builtin)
    :=
    match t with
    | (GenLeaf (inl _ b)) => Some (term_operand b)
    | (GenLeaf (inr _ s)) => Some (term_preterm s)
    | _ => None
    end
    .

    Lemma Term'_to_from_gen_tree
        (TermSymbol : Type)
        {TermSymbol_eqd : EqDecision TermSymbol}
        {TermSymbol_cnt : Countable TermSymbol}
        (builtin : Type)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (e : Term' TermSymbol builtin)
        : Term'_from_gen_tree TermSymbol builtin (Term'_to_gen_tree TermSymbol builtin e) = Some e
    .
    Proof.
        destruct e; reflexivity.
    Qed.

    #[export]
    Instance Term'_countable
        (TermSymbol_set : Type)
        {TermSymbol_eqd : EqDecision TermSymbol_set}
        {TermSymbol_cnt : Countable TermSymbol_set}
        (builtin_set : Type)
        {builtin_eqdec : EqDecision builtin_set}
        {builtin_countable : Countable builtin_set}
        : Countable (Term' TermSymbol_set builtin_set)
    .
    Proof.
        apply inj_countable
        with
            (f := Term'_to_gen_tree TermSymbol_set builtin_set)
            (g := Term'_from_gen_tree TermSymbol_set builtin_set)
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


#[export]
Instance Term'_A_B_fmap (A : Type)
    : FMap (Term' A)
    := @Term'_fmap A
.

#[export]
Instance Term_TermSymbol_fmap
    {Σ : BackgroundModel}
    : FMap (Term' TermSymbol)
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
    {Σ : BackgroundModel}
    {T : Type}
    (l : list (@TermOver' TermSymbol T))
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
    {Σ : BackgroundModel}
    {T : Type}
    (l : list (Term' TermSymbol T))
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
    {Σ : BackgroundModel}
    {T : Type}
    (o : option (@TermOver' TermSymbol T))
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
    {Σ : BackgroundModel}
    {T : Type}
    (o : option (Term' TermSymbol T))
    :
    uglify' <$> (prettify <$> o) = o
.
Proof.
    rewrite <- option_fmap_compose.
    rewrite compose_uglify_prettify.
    rewrite option_fmap_id.
    reflexivity.
Qed.


Fixpoint vars_of_aosB
    {Σ : BackgroundModel}
    {T0 B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VB: VarsOf B var}
    (o : PreTerm' T0 B)
    : gset var :=
match o with
| pt_operator _ => ∅
| pt_app_operand o' b => vars_of b ∪ vars_of_aosB o'
| pt_app_ao o1 o2 => vars_of_aosB o1 ∪ vars_of_aosB o2
end.

#[export]
Instance VarsOf_aosB
    {Σ : BackgroundModel}
    {T0 B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VB: VarsOf B var}
    : VarsOf (PreTerm' T0 B) var
:= {|
    vars_of := vars_of_aosB ; 
|}.

Definition vars_of_Term'B
    {Σ : BackgroundModel}
    {T0 : Type}
    {B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    (φ : Term' T0 B)
    : gset var :=
match φ with
| term_preterm aop => vars_of aop
| term_operand otwsc => vars_of otwsc
end.

#[export]
Instance VarsOf_Term'
    {Σ : BackgroundModel}
    {T0 B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    : VarsOf (Term' T0 B) var
:= {|
    vars_of := vars_of_Term'B ; 
|}.

Lemma vars_of_uglify'
    {Σ : BackgroundModel}
    {T var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VT : VarsOf T var}
    (t : @TermOver' TermSymbol T)
    :
    vars_of (uglify' t) = vars_of t
.
Proof.
    induction t; simpl.
    { reflexivity. }
    {
        rewrite Forall_forall in H.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        induction l using rev_ind; simpl.
        { reflexivity. }
        {
            specialize (IHl ltac:(set_solver)).
            rewrite map_app.
            rewrite to_PreTerm''_app.
            simpl.
            unfold helper.
            destruct (uglify' x) eqn:Hux.
            {
                simpl.
                apply (f_equal prettify) in Hux.
                rewrite (cancel prettify uglify') in Hux.
                subst x.
                rewrite IHl.
                simpl.
                rewrite fmap_app.
                simpl.
                rewrite union_list_app_L.
                specialize (H (prettify (term_preterm ao)) ltac:(set_solver)).
                simpl in H.
                repeat (unfold vars_of in H; simpl in H).
                rewrite <- H.
                rewrite (uglify'_prettify').
                simpl.
                ltac1:(set_solver).
            }
            {
                apply (f_equal prettify) in Hux.
                rewrite (cancel prettify uglify') in Hux.
                subst x.
                rewrite fmap_app.
                simpl.
                rewrite union_list_app_L.
                ltac1:(set_solver).
            }
        }
    }
Qed.


Lemma vars_of_uglify
    {Σ : BackgroundModel}
    (h : Variabl) a:
    h ∈ vars_of_to_l2r a
    <->
    h ∈ (vars_of (uglify' a))
.
Proof.
    induction a; unfold vars_of; simpl.
    {
        destruct a; unfold vars_of; simpl.
        { ltac1:(set_solver). }
        { ltac1:(set_solver). }
    }
    {
        unfold to_PreTerm''; simpl.
        revert s h H.
        induction l using rev_ind; intros s h H.
        {
            simpl. unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            rewrite map_app.
            rewrite map_app.
            rewrite concat_app.
            rewrite fold_left_app.
            rewrite elem_of_app.
            simpl.

            rewrite Forall_app in H.
            destruct H as [H1 H2].
            specialize (IHl s h H1). clear H1.
            rewrite IHl. clear IHl.
            rewrite Forall_cons in H2.
            destruct H2 as [H2 _].
            unfold helper; simpl.
            destruct (uglify' x) eqn:Hux;
                unfold vars_of; simpl;
                rewrite elem_of_union;
                rewrite app_nil_r;
                rewrite H2; clear H2;
                unfold vars_of; simpl.
            {
                reflexivity.
            }
            {
                destruct operand; unfold vars_of; simpl.
                {
                    ltac1:(tauto).
                }
                {
                    rewrite elem_of_singleton.
                    ltac1:(tauto).
                }
            }
        }
    }
Qed.
