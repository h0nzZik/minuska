From Minuska Require Import
    prelude
    spec
    basic_properties
.

From Equations Require Export Equations.


Definition eqn {Σ : StaticModel} : Type := ((TermOver BuiltinOrVar)*(TermOver BuiltinOrVar))%type.

Definition eqn_size {Σ : StaticModel} (e : eqn) : nat := TermOver_size (e.1) + TermOver_size (e.2).

Definition eqns_size {Σ : StaticModel} (es : list eqn) := sum_list_with eqn_size es.


Definition eqn_vars {Σ : StaticModel} (e : eqn) := ((vars_of (e.1)) ∪ (vars_of (e.2))).
Definition eqns_vars {Σ : StaticModel} (es : list eqn) := union_list (eqn_vars <$> es)
.


Definition deg {Σ : StaticModel} (es : list eqn) : (nat*nat)%type :=
(size (eqns_vars es), eqns_size es)
.

Definition sub
    {Σ : StaticModel}
    (t' : TermOver BuiltinOrVar)
    (x : variable)
    (es : list eqn)
:=
    (fun e => (TermOverBoV_subst e.1 x t', TermOverBoV_subst e.2 x t')) <$> es
.



Equations? unify {Σ : StaticModel} (l : list eqn)
: option (list (variable * (TermOver BuiltinOrVar)))
by wf (deg l) (lexprod nat nat lt lt) :=

unify []
:= Some [] ;

unify ((t_over (bov_variable x),t_over (bov_variable y))::es) with (decide (x = y)) => {
| left _ := unify es ;
| right _ := 
tmp ← unify (sub (t_over (bov_variable y)) x es);
Some ((x, (t_over (bov_variable y)))::tmp)
};
unify ((t_over (bov_variable x), t)::es) with (decide (x ∈ vars_of t)) => {
| left _ => None
| right _ =>
    tmp ← unify (sub t x es);
    Some ((x,t)::tmp)
};
unify ((t, t_over (bov_variable x))::es) with (decide (x ∈ vars_of t)) => {
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
    do 4 (unfold vars_of at 1; simpl).
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
    ltac1:(unfold t1; unfold t2). clear t1 t2.
    apply deg_cons_lt.
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
    ltac1:(unfold t1; unfold t2; clear t1; clear t2).
    apply deg_cons_lt.
}
{
    ltac1:(unfold t); clear t.
    ltac1:(rewrite deg_swap_head).
    apply sub_decreases_degree.
    assumption.
}
{
    destruct a as [H1 H2].
    subst s2.
    apply fewer_arrows_lower_degree.
    assumption.
}
Qed.