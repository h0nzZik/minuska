From Minuska Require Import
    prelude
    spec
    lowlang
.

Definition vars_of_AP
    {Σ : StaticModel}
    (ap : AtomicProposition)
    : gset variable :=
match ap with
| apeq e1 e2 => vars_of e1 ∪ vars_of e2
end.

#[export]
Instance VarsOf_AP
    {Σ : StaticModel}
    : VarsOf AtomicProposition variable
:= {|
    vars_of := vars_of_AP ; 
|}.

Fixpoint vars_of_aosB
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    {T0 B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VB: VarsOf B var}
    : VarsOf (PreTerm' T0 B) var
:= {|
    vars_of := vars_of_aosB ; 
|}.



Definition vars_of_SideCondition
    {Σ : StaticModel}
    (c : SideCondition)
    : gset variable :=
match c with
| sc_constraint c' => vars_of c'
end.

#[export]
Instance VarsOf_SideCondition
    {Σ : StaticModel}
    : VarsOf SideCondition variable
:= {|
    vars_of := vars_of_SideCondition ; 
|}.

#[export]
Program Instance VarsOf_list_SideCondition
    {Σ : StaticModel}
    : VarsOf (list SideCondition) variable
:= {|
    vars_of := fun scs => ⋃ (vars_of <$> scs)
|}.

Definition vars_of_Term'B
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    {T0 B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    : VarsOf (Term' T0 B) var
:= {|
    vars_of := vars_of_Term'B ; 
|}.


#[export]
Instance VarsOf_TermOver_Expression
    {Σ : StaticModel}
    :
    VarsOf (TermOver Expression) variable
.
Proof.
    apply VarsOf_TermOver.
Defined.

Lemma vars_of_uglify'
    {Σ : StaticModel}
    {T var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VT : VarsOf T var}
    (t : TermOver T)
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
