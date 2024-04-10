From stdpp Require Import finite.

From Minuska Require Import
    prelude
.



(*
    Here we define an alternative, more user-friendly term structure.
*)

Unset Elimination Schemes.
#[universes(polymorphic=yes, cumulative=yes)]
Inductive TermOver' {T : Type} (A : Type) : Type :=
| t_over (a : A)
| t_term (s : T) (l : list (@TermOver' T A))
.
Set Elimination Schemes.

Arguments t_over {T} {A}%_type_scope a.
Arguments t_term {T} {A}%_type_scope s l%_list_scope.

Section custom_induction_principle.

    Context
        {T : Type}
        {A : Type}
        (P : @TermOver' T A -> Prop)
        (true_for_over : forall a, P (t_over a) )
        (preserved_by_term :
            forall
                (s : T)
                (l : list (@TermOver' T A)),
                Forall P l ->
                P (t_term s l)
        )
    .

    Fixpoint TermOver'_ind (p : @TermOver' T A) : P p :=
    match p with
    | t_over a => true_for_over a
    | t_term s l => preserved_by_term s l (Forall_true P l TermOver'_ind)
    end.

End custom_induction_principle.

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

Class MVariables (variable : Type) := {
    variable_eqdec :: EqDecision variable ;
    variable_countable :: Countable variable ;
    variable_infinite :: Infinite variable ;
}.

Class Symbols (symbol : Type) := {
    symbol_eqdec :: EqDecision symbol ;
    symbol_countable :: Countable symbol ;
}.

Class Builtin {symbol : Type} {symbols : Symbols symbol} := {
    builtin_value
        : Type ;
    builtin_value_eqdec
        :: EqDecision builtin_value ;
    
    builtin_nullary_function
        : Type ;
    builtin_nullary_function_eqdec
        :: EqDecision builtin_nullary_function ;

    builtin_unary_function
        : Type ;
    builtin_unary_function_eqdec
        :: EqDecision builtin_unary_function ;

    builtin_binary_function
        : Type ;
    builtin_binary_function_eqdec
        :: EqDecision builtin_binary_function ;
    
    builtin_ternary_function
        : Type ;
    builtin_ternary_function_eqdec
        :: EqDecision builtin_ternary_function ;

    builtin_nullary_function_interp
        : builtin_nullary_function
        -> (@TermOver' symbol builtin_value) ;

    builtin_unary_function_interp
        : builtin_unary_function
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value) ;

    builtin_binary_function_interp
        : builtin_binary_function
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value) ;

    builtin_ternary_function_interp
        : builtin_ternary_function
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value) ;
}.

Class StaticModel := {
    symbol : Type ;
    variable : Type ;
    symbols :: Symbols symbol ;
    builtin :: Builtin ;
    variables :: MVariables variable ;
}.

Class VarsOf
    (A : Type)
    (var: Type)
    {_Ev : EqDecision var}
    {_Cv : Countable var}
    :=
{
    vars_of : A -> gset var ;
}.

Arguments vars_of : simpl never.

Definition GroundTerm {Σ : StaticModel}
    := Term' symbol builtin_value
.

Inductive Expression
    {Σ : StaticModel}
    :=
| ft_element (e : GroundTerm)
| ft_variable (x : variable)
| ft_nullary (f : builtin_nullary_function)
| ft_unary (f : builtin_unary_function) (t : Expression)
| ft_binary (f : builtin_binary_function) (t1 : Expression) (t2 : Expression)
| ft_ternary (f : builtin_ternary_function) (t1 : Expression) (t2 : Expression) (t3 : Expression)
.

Inductive Expression2
    {Σ : StaticModel}
    :=
| e_ground (e : @TermOver' (symbol) builtin_value)
| e_variable (x : variable)
| e_nullary (f : builtin_nullary_function)
| e_unary (f : builtin_unary_function) (t : Expression2)
| e_binary (f : builtin_binary_function) (t1 : Expression2) (t2 : Expression2)
| e_ternary (f : builtin_ternary_function) (t1 : Expression2) (t2 : Expression2) (t3 : Expression2)
.

Inductive AtomicProposition {Σ : StaticModel} :=
| apeq (e1 : Expression) (e2 : Expression)
.

Inductive BuiltinOrVar {Σ : StaticModel} :=
| bov_builtin (b : builtin_value)
| bov_variable (x : variable)
.

Definition SymbolicTerm {Σ : StaticModel}
    := Term' symbol BuiltinOrVar
.

Inductive SideCondition {Σ : StaticModel} :=
| sc_constraint (c : AtomicProposition)
.

Definition ExpressionTerm {Σ : StaticModel} :=
    Term' symbol Expression
.


Inductive LeftRight : Set := LR_Left | LR_Right.

Record RewritingRule
    {Σ : StaticModel}
    (Act : Set)
:= mkRewritingRule
{
    fr_from : SymbolicTerm ;
    fr_to : ExpressionTerm ;
    fr_scs : list SideCondition ;
    fr_act : Act ;
}.

Arguments fr_from {Σ} {Act}%_type_scope r.
Arguments fr_to {Σ} {Act}%_type_scope r.
Arguments fr_scs {Σ} {Act}%_type_scope r.
Arguments fr_act {Σ} {Act}%_type_scope r.

Definition RewritingTheory
    {Σ : StaticModel}
    (Act : Set)
    := list (RewritingRule Act)
.

Definition to_Term'
    {Σ : StaticModel}
    {T : Type}
    (x : ((T)+(PreTerm' symbol T)))
    : Term' symbol T
:=
match x with
| inl x' => term_operand x'
| inr x' => term_preterm x'
end
.

Definition helper {Σ : StaticModel} {T : Type} a b : PreTerm' symbol T
    :=match b with
            | term_operand b' => pt_app_operand a b'
            | term_preterm b' => pt_app_ao a b'
            end.

Definition to_PreTerm'
    {Σ : StaticModel}
    {T : Type}
    (s : symbol)
    (l : list ((Term' symbol T)))
    : PreTerm' symbol T
:=
    fold_left
        helper
        l
        (pt_operator s)
.

Lemma to_PreTerm'_app
    {Σ : StaticModel}
    {T : Type}
    (s : symbol)
    (l1 l2 : list ((Term' symbol T)))
    : to_PreTerm' s (l1 ++ l2) = fold_left helper l2 (to_PreTerm' s l1)
.
Proof.
    unfold to_PreTerm'.
    rewrite fold_left_app.
    reflexivity.
Qed.

Definition apply_symbol'
    {Σ : StaticModel}
    {T : Type}
    (s : symbol)
: 
    list ((Term' symbol T)) ->
    Term' symbol T
:=
    fun l =>
    (to_Term' (inr (to_PreTerm' ((s):symbol) l)))
.



Definition TermOver {Σ : StaticModel} (A : Type) : Type := @TermOver' symbol A.

Fixpoint TermOver_size
    {T : Type}
    {A : Type}
    (t : @TermOver' T A)
    : nat
:=
match t with
| t_over _ => 1
| t_term _ l => S (sum_list_with (S ∘ TermOver_size) l)
end.

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


Definition apply_symbol''
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
    | t_term s l => apply_symbol'' s (map uglify' l)
    end
.

Fixpoint PreTerm'_get_symbol
    {T : Type}
    {A : Type}
    (pt : PreTerm' T A)
    : T
:=
    match pt with
    | pt_operator s => s
    | pt_app_operand x y => PreTerm'_get_symbol x
    | pt_app_ao x y => PreTerm'_get_symbol x
    end
.

Fixpoint prettify'
    {T : Type}
    {A : Type}
    (pt : PreTerm' T A)
    : @TermOver' T A
:=
    t_term
        (PreTerm'_get_symbol pt) (
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
            assert (Hs: (PreTerm'_get_symbol (to_PreTerm'' s (map uglify' l))) = s).
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
            unfold apply_symbol''. simpl. f_equal.
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
                unfold apply_symbol'' in *. simpl in *.
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
                unfold apply_symbol'' in *. simpl in *.
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
            unfold apply_symbol''. simpl. f_equal.
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
                unfold apply_symbol'' in *. simpl in *.
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
                unfold apply_symbol'' in *. simpl in *.
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

Lemma uglify'_prettify'
    {Σ : StaticModel}
    {T : Type}
    (t : PreTerm' symbol T)
    :
    uglify' (prettify' t) = term_preterm t
.
Proof.
    rewrite <- (cancel uglify' prettify (term_preterm t)).
    apply f_equal.
    simpl. reflexivity.
Qed.

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

Fixpoint TermOver_map
    {Σ : StaticModel}
    {A B : Type}
    (f : A -> B)
    (t : TermOver A)
    : TermOver B
:=
    match t with
    | t_over b => t_over (f b)
    | t_term s l => t_term s (map (TermOver_map f) l)
    end
.

Definition TermOverBuiltin_to_TermOverBoV
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : TermOver BuiltinOrVar
:=
    TermOver_map bov_builtin t
.

Definition BoV_to_Expr
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : Expression
:=
    match bov with
    | bov_builtin b => (ft_element (uglify' (t_over b)))
    | bov_variable x => ft_variable x
    end
.

Definition TermOverBoV_to_TermOverExpr
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    : TermOver Expression
:=
    TermOver_map BoV_to_Expr t
.

Lemma vars_of_to_l2r_of_tob
    {Σ : StaticModel}
    (r : TermOver builtin_value)
    :
    vars_of_to_l2r (TermOverBuiltin_to_TermOverBoV r) = []
.
Proof.
    induction r; simpl.
    { reflexivity. }
    {
        revert H.
        induction l; intros H; simpl.
        { reflexivity. }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            rewrite IHl.
            unfold TermOverBuiltin_to_TermOverBoV  in *.
            rewrite H1.
            reflexivity.
        }
    }
Qed.

Fixpoint Expression_subst
    {Σ : StaticModel}
    (e : Expression)
    (x : variable)
    (e' : Expression)
    : Expression
:=    
match e with
| ft_element g => ft_element g
| ft_variable y =>
    if (decide (y = x)) then e' else (ft_variable y)
| ft_nullary f => ft_nullary f
| ft_unary f e1 => ft_unary f (Expression_subst e1 x e')
| ft_binary f e1 e2 => ft_binary f (Expression_subst e1 x e') (Expression_subst e2 x e')
| ft_ternary f e1 e2 e3 => ft_ternary f (Expression_subst e1 x e') (Expression_subst e2 x e') (Expression_subst e3 x e')
end
.

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

Fixpoint Expression2_to_Expression
    {Σ : StaticModel}
    (e : Expression2)
    : Expression
:=
match e with
| e_ground g => ft_element (uglify' g)
| e_variable x => ft_variable x
| e_nullary f => ft_nullary f
| e_unary f e1 => ft_unary f (Expression2_to_Expression e1)
| e_binary f e1 e2 => ft_binary f (Expression2_to_Expression e1) (Expression2_to_Expression e2)
| e_ternary f e1 e2 e3 => ft_ternary f (Expression2_to_Expression e1) (Expression2_to_Expression e2) (Expression2_to_Expression e3)
end
.


Fixpoint Expression_to_Expression2
    {Σ : StaticModel}
    (e : Expression)
    : Expression2
:=
match e with
| ft_element g => e_ground (prettify g)
| ft_variable x => e_variable x
| ft_nullary f => e_nullary f
| ft_unary f e1 => e_unary f (Expression_to_Expression2 e1)
| ft_binary f e1 e2 => e_binary f (Expression_to_Expression2 e1) (Expression_to_Expression2 e2)
| ft_ternary f e1 e2 e3 => e_ternary f (Expression_to_Expression2 e1) (Expression_to_Expression2 e2) (Expression_to_Expression2 e3)
end
.

#[export]
Instance cancel_expression_expression2
    {Σ : StaticModel}
    : Cancel eq Expression2_to_Expression Expression_to_Expression2
.
Proof.
    intros e.
    induction e; simpl; (repeat (rewrite (cancel uglify' prettify))); ltac1:(congruence).
Qed.

#[export]
Instance cancel_expression2_expression
    {Σ : StaticModel}
    : Cancel eq Expression_to_Expression2 Expression2_to_Expression
.
Proof.
    intros e.
    induction e; simpl; (repeat (rewrite (cancel prettify uglify'))); ltac1:(congruence).
Qed.

Record SideCondition2
    {Σ : StaticModel}
    :=
mkSideCondition2 {
    sc_left: Expression2 ;
    sc_right: Expression2 ;
}.

Definition sc2_to_sc
    {Σ : StaticModel}
    (c : SideCondition2)
    : SideCondition
.
Proof.
    constructor.
    constructor.
    { exact (Expression2_to_Expression (sc_left c)). }
    { exact (Expression2_to_Expression (sc_right c)). }
Defined.

Definition sc_to_sc2
    {Σ : StaticModel}
    (c : SideCondition)
    : SideCondition2
.
Proof.
    destruct c.
    destruct c.
    constructor.
    {
        apply Expression_to_Expression2. exact e1.
    }
    {
        apply Expression_to_Expression2. exact e2.
    }
Defined.

#[export]
Instance cancel_sc_sc2
    {Σ : StaticModel}
    :
    Cancel eq (sc_to_sc2) (sc2_to_sc)
.
Proof.
    intros c; destruct c; simpl.
    rewrite (cancel Expression_to_Expression2 Expression2_to_Expression).
    rewrite (cancel Expression_to_Expression2 Expression2_to_Expression).
    reflexivity.
Qed.

#[export]
Instance cancel_sc2_sc
    {Σ : StaticModel}
    :
    Cancel eq (sc2_to_sc) (sc_to_sc2)
.
Proof.
    intros c. destruct c; destruct c; simpl.
    unfold sc2_to_sc. simpl.
    rewrite (cancel Expression2_to_Expression Expression_to_Expression2).
    rewrite (cancel Expression2_to_Expression Expression_to_Expression2).
    reflexivity.
Qed.

Record RewritingRule2
    {Σ : StaticModel}
    (Act : Set)
:= mkRewritingRule2
{
    r_from : TermOver BuiltinOrVar ;
    r_to : TermOver Expression2 ;
    r_scs : list SideCondition2 ;
    r_act : Act ;
}.

Arguments r_from {Σ} {Act%_type_scope} r.
Arguments r_to {Σ} {Act%_type_scope} r.
Arguments r_scs {Σ} {Act%_type_scope} r.
Arguments r_act {Σ} {Act%_type_scope} r.

Definition r_to_fr
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    : RewritingRule Act
:=
    mkRewritingRule
        Σ
        Act
        (uglify' (r_from r))
        (uglify' (TermOver_map Expression2_to_Expression (r_to r)))
        (fmap sc2_to_sc (r_scs r))
        (r_act r)
.

Definition fr_to_r
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    : RewritingRule2 Act
.
Proof.
    destruct r.
    constructor.
    { exact (prettify fr_from0). }
    { 
        apply prettify in fr_to0.
        apply (TermOver_map Expression_to_Expression2).
        exact fr_to0.
    }
    {
        apply (fmap sc_to_sc2).
        exact fr_scs0.
    }
    {
        exact fr_act0.
    }
Defined.


#[export]
Instance cancel_TermOver_map
    {Σ : StaticModel}
    (A B : Type)
    (f : A -> B)
    (g : B -> A)
    :
    Cancel eq f g ->
    Cancel eq (TermOver_map f) (TermOver_map g)
.
Proof.
    intros Hcancel.
    intros t.
    induction t; simpl.
    { rewrite (cancel f g). reflexivity. }
    {
        f_equal.
        induction l; simpl.
        { reflexivity. }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2).
            rewrite H1. rewrite IHl.
            reflexivity.
        }
    }
Qed.

Definition RewritingTheory2
    {Σ : StaticModel}
    (Act : Set)
    := list (RewritingRule2 Act)
.