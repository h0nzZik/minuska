From Minuska Require Import
    prelude
    spec_syntax
.

Fixpoint vars_of_Expression
    {Σ : StaticModel}
    (t : Expression)
    : gset variable :=
match t with
| ft_element _ => ∅
| ft_variable x => {[x]}
| ft_nullary _ => ∅
| ft_unary _ t' => vars_of_Expression t'
| ft_binary _ t1 t2 => vars_of_Expression t1 ∪ vars_of_Expression t2
| ft_ternary _ t1 t2 t3 => vars_of_Expression t1 ∪ vars_of_Expression t2 ∪ vars_of_Expression t3
end.

#[export]
Instance VarsOf_Expression
    {Σ : StaticModel}
    : VarsOf Expression variable
:= {|
    vars_of := vars_of_Expression ; 
|}.


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
    {B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VB: VarsOf B var}
    (o : PreTerm' symbol B)
    : gset var :=
match o with
| pt_operator _ => ∅
| pt_app_operand o' b => vars_of b ∪ vars_of_aosB o'
| pt_app_ao o1 o2 => vars_of_aosB o1 ∪ vars_of_aosB o2
end.

#[export]
Instance VarsOf_aosB
    {Σ : StaticModel}
    {B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VB: VarsOf B var}
    : VarsOf (PreTerm' symbol B) var
:= {|
    vars_of := vars_of_aosB ; 
|}.

Definition vars_of_BoV
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : gset variable
:=
match bov with
| bov_variable x => {[x]}
| bov_builtin _ => ∅
end.

#[export]
Instance VarsOf_BoV
    {Σ : StaticModel}
    : VarsOf BuiltinOrVar variable
:= {|
    vars_of := vars_of_BoV ; 
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
    {B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    (φ : Term' symbol B)
    : gset var :=
match φ with
| term_preterm aop => vars_of aop
| term_operand otwsc => vars_of otwsc
end.

#[export]
Instance VarsOf_Term'
    {Σ : StaticModel}
    {B var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VB : VarsOf B var}
    : VarsOf (Term' symbol B) var
:= {|
    vars_of := vars_of_Term'B ; 
|}.

Fixpoint vars_of_Expression2
    {Σ : StaticModel}
    (t : Expression2)
    : gset variable :=
match t with
| e_ground _ => ∅
| e_variable x => {[x]}
| e_nullary _ => ∅
| e_unary _ t' => vars_of_Expression2 t'
| e_binary _ t1 t2 => vars_of_Expression2 t1 ∪ vars_of_Expression2 t2
| e_ternary _ t1 t2 t3 => vars_of_Expression2 t1 ∪ vars_of_Expression2 t2 ∪ vars_of_Expression2 t3
end.

#[export]
Instance VarsOf_Expression2
    {Σ : StaticModel}
    : VarsOf Expression2 variable
:= {|
    vars_of := vars_of_Expression2 ; 
|}.


#[local]
Instance VarsOf_TermOver
    {T0 : Type}
    {T var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VT : VarsOf T var}
    :
    VarsOf (@TermOver' T0 T) var
:=
{|
    vars_of := (fix go (t : @TermOver' T0 T) := 
        match t with
        | t_over x => vars_of x
        | t_term _ l => ⋃ (go <$> l)
        end
    ) ; 
|}.

#[export]
Instance VarsOf_TermOver_BuiltinOrVar
    {Σ : StaticModel}
    :
    VarsOf (TermOver BuiltinOrVar) variable
.
Proof.
    apply VarsOf_TermOver.
Defined.

#[export]
Instance VarsOf_TermOver_Expression2
    {Σ : StaticModel}
    :
    VarsOf (TermOver Expression2) variable
.
Proof.
    apply VarsOf_TermOver.
Defined.

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

#[export]
Instance VarsOf_SideCondition2
    {Σ : StaticModel}
    : VarsOf SideCondition2 variable
:= {|
    vars_of := fun c => vars_of (sc_left c) ∪ vars_of (sc_right c) ; 
|}.

#[export]
Program Instance VarsOf_list_SideCondition2
    {Σ : StaticModel}
    : VarsOf (list SideCondition2) variable
:= {|
    vars_of := fun scs => ⋃ (vars_of <$> scs)
|}.

