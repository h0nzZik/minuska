From Minuska Require Import
    prelude
    spec
    basic_properties
    termoverbov_subst
    termoverbov_subst_properties
.

From Equations Require Export Equations.


Definition eqn {Σ : BackgroundModel} : Type := ((TermOver BuiltinOrVar)*(TermOver BuiltinOrVar))%type.

Definition eqn_size {Σ : BackgroundModel} (e : eqn) : nat := TermOver_size (e.1) + TermOver_size (e.2).

Definition eqns_size {Σ : BackgroundModel} (es : list eqn) := sum_list_with eqn_size es.


Definition eqn_vars {Σ : BackgroundModel} (e : eqn) := ((vars_of (e.1)) ∪ (vars_of (e.2))).
Definition eqns_vars {Σ : BackgroundModel} (es : list eqn) := union_list (eqn_vars <$> es)
.

Lemma eqns_vars_cons
{Σ : BackgroundModel}
(e : eqn)
(es : list eqn)
:
    eqns_vars (e::es) = vars_of e.1 ∪ vars_of e.2 ∪ eqns_vars es
.
Proof.
    unfold eqns_vars. simpl.
    reflexivity.
Qed.


Definition deg {Σ : BackgroundModel} (es : list eqn) : (nat*nat)%type :=
(size (eqns_vars es), eqns_size es)
.

Lemma deg_swap_head
    {Σ : BackgroundModel}
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

Definition sub
    {Σ : BackgroundModel}
    (t' : TermOver BuiltinOrVar)
    (x : Variabl)
    (es : list eqn)
:=
    (fun e => (TermOverBoV_subst e.1 x t', TermOverBoV_subst e.2 x t')) <$> es
.

Lemma sub_notin
    {Σ : BackgroundModel}
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

Lemma eqns_vars_sub {Σ : BackgroundModel} (t : TermOver BuiltinOrVar) (x : Variabl)
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
    {Σ : BackgroundModel}
    x t es
:
    x ∉ vars_of t ->
    (lexprod nat nat lt lt) (deg (sub t x es)) (deg ((t_over (bov_Variabl x), t)::es))
.
Proof.
    intros Hxt.
    destruct (decide (x ∈ eqns_vars es)) as [Hxes | Hxes].
    {
        apply left_lex.
        apply subset_size.
        ltac1:(rewrite eqns_vars_cons).
        simpl.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
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
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        apply left_lex.
        apply subset_size.
        ltac1:(set_solver).
    }
Qed.

Lemma deg_cons_lt
    {Σ : BackgroundModel}
    (e : eqn)
    (es : list eqn)
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


Lemma eqns_vars_app
    {Σ : BackgroundModel}
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
    {Σ : BackgroundModel}
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
    {Σ : BackgroundModel}
    (s : TermSymbol)
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
        repeat (rewrite length_fmap).
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

Equations? unify
    {Σ : BackgroundModel}
    (l : list eqn)
:
    option (list (Variabl * (TermOver BuiltinOrVar)))
    by wf (deg l) (lexprod nat nat lt lt)
:=

    unify []
    := Some [] ;

    unify ((t_over (bov_Variabl x),t_over (bov_Variabl y))::es) with (decide (x = y)) => {
    | left _ := unify es ;
    | right _ := 
        tmp ← unify (sub (t_over (bov_Variabl y)) x es);
        Some ((x, (t_over (bov_Variabl y)))::tmp)
    };

    unify ((t_over (bov_Variabl x), t)::es) with (decide (x ∈ vars_of t)) => {
    | left _ => None
    | right _ =>
        tmp ← unify (sub t x es);
        Some ((x,t)::tmp)
    };

    unify ((t, t_over (bov_Variabl x))::es) with (decide (x ∈ vars_of t)) => {
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
        do 4 (unfold vars_of; simpl).
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
        ltac1:(unfold t); clear t.
        ltac1:(rewrite deg_swap_head).
        apply sub_decreases_degree.
        assumption.
    }
    {
        apply fewer_arrows_lower_degree.
        assumption.
    }
Qed.
