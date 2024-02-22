From stdpp Require Import finite.

From Minuska Require Import
    prelude
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


Arguments term_operand {Operator Operand}%type_scope operand.
Arguments term_preterm {Operator Operand}%type_scope ao.

Arguments pt_operator {operator operand}%type_scope s.
Arguments pt_app_operand {operator operand}%type_scope aps b.
Arguments pt_app_ao {operator operand}%type_scope aps x.

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
        -> (Term' symbol builtin_value) ;

    builtin_unary_function_interp
        : builtin_unary_function
        -> (Term' symbol builtin_value)
        -> (Term' symbol builtin_value) ;

    builtin_binary_function_interp
        : builtin_binary_function
        -> (Term' symbol builtin_value)
        -> (Term' symbol builtin_value)
        -> (Term' symbol builtin_value) ;

    builtin_ternary_function_interp
        : builtin_ternary_function
        -> (Term' symbol builtin_value)
        -> (Term' symbol builtin_value)
        -> (Term' symbol builtin_value)
        -> (Term' symbol builtin_value) ;
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

Arguments fr_from {Σ} {Act}%type_scope r.
Arguments fr_to {Σ} {Act}%type_scope r.
Arguments fr_scs {Σ} {Act}%type_scope r.
Arguments fr_act {Σ} {Act}%type_scope r.

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


(*
    Here we define an alternative, more user-friendly term structure.
*)

Unset Elimination Schemes.
#[universes(polymorphic=yes, cumulative=yes)]
Inductive TermOver {Σ : StaticModel} (A : Type) : Type :=
| t_over (a : A)
| t_term (s : symbol) (l : list (TermOver A))
.
Set Elimination Schemes.

Arguments t_over {Σ} {A}%type_scope a.
Arguments t_term {Σ} {A}%type_scope s l%list_scope.

Section custom_induction_principle.

    Context
        {Σ : StaticModel}
        {A : Type}
        (P : TermOver A -> Prop)
        (true_for_over : forall a, P (t_over a) )
        (preserved_by_term :
            forall
                (s : symbol)
                (l : list (TermOver A)),
                Forall P l ->
                P (t_term s l)
        )
    .

    Fixpoint TermOver_ind (p : TermOver A) : P p :=
    match p with
    | t_over a => true_for_over a
    | t_term s l => preserved_by_term s l (Forall_true P l TermOver_ind)
    end.

End custom_induction_principle.

Fixpoint TermOver_size
    {Σ : StaticModel}
    {A : Type}
    (t : TermOver A)
    : nat
:=
match t with
| t_over _ => 1
| t_term _ l => S (sum_list_with (S ∘ TermOver_size) l)
end.

Fixpoint uglify'
    {Σ : StaticModel}
    {A : Type}
    (t : TermOver A)
    {struct t}
    : Term' symbol A
:=
    match t with
    | t_over a => term_operand a
    | t_term s l => apply_symbol' s (map uglify' l)
    end
.

(*
Definition uglify
    {Σ : StaticModel}
    {A : Type}
    (t : (A+(TermOver A)))
:=
    match t with
    | inl a => term_operand a
    | inr t => uglify' t
    end
.
*)

Fixpoint PreTerm'_get_symbol
    {Σ : StaticModel}
    {A : Type}
    (pt : PreTerm' symbol A)
    : symbol
:=
    match pt with
    | pt_operator s => s
    | pt_app_operand x y => PreTerm'_get_symbol x
    | pt_app_ao x y => PreTerm'_get_symbol x
    end
.

Fixpoint prettify'
    {Σ : StaticModel}
    {A : Type}
    (pt : PreTerm' symbol A)
    : TermOver A
:=
    t_term
        (PreTerm'_get_symbol pt) (
        ((fix go (pt : PreTerm' symbol A) : list (TermOver A) :=
            match pt with
            | pt_operator _ => []
            | pt_app_operand x y => (go x)++[(t_over y)]
            | pt_app_ao x y => (go x)++[(prettify' y)]
            end
        ) pt))
.

Definition prettify
    {Σ : StaticModel}
    {A : Type}
    (t : Term' symbol A)
    : ((TermOver A))
:=
    match t with
    | term_preterm pt => (prettify' pt)
    | term_operand a => t_over a
    end
.


#[global]
Instance cancel_prettify_uglify
    {Σ : StaticModel}
    {A : Type}
    : Cancel eq (@prettify Σ A) (@uglify' Σ A)
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
            assert (Hs: (PreTerm'_get_symbol (to_PreTerm' s (map uglify' l))) = s).
            {
                clear.
                induction l using rev_ind; simpl.
                { reflexivity. }
                {
                    unfold to_PreTerm'. simpl.
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
            rewrite to_PreTerm'_app.
            simpl.
            unfold helper.
            destruct (uglify' x) eqn:Hux.
            {
                simpl.
                remember ((to_PreTerm' s (map uglify' l)) ) as tpt.
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
                remember ((to_PreTerm' s (map uglify' l)) ) as tpt.
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
    {Σ : StaticModel}
    {A : Type}
    : Cancel eq (@uglify' Σ A) (@prettify Σ A)
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
            unfold apply_symbol'. simpl. f_equal.
            unfold to_PreTerm'.
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
                unfold apply_symbol' in *. simpl in *.
                inversion IHao'; subst; clear IHao'.
                unfold to_PreTerm' in *.
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
                unfold apply_symbol' in *. simpl in *.
                inversion IHao'; subst; clear IHao'.
                unfold to_PreTerm' in *.
                rewrite map_app in H0.
                rewrite fold_left_app in H0.
                simpl in H0.
                inversion H0; subst; clear H0.
                simpl.
                reflexivity.
            }
        }
        {
            unfold apply_symbol'. simpl. f_equal.
            unfold to_PreTerm'.
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
                unfold apply_symbol' in *. simpl in *.
                inversion IHao1'; subst; clear IHao1'.
                unfold to_PreTerm' in *.
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
                unfold apply_symbol' in *. simpl in *.
                inversion IHao1'; subst; clear IHao1'.
                unfold to_PreTerm' in *.
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

Variant MinusL_Decl {Σ : StaticModel} (Act : Set) :=
| mld_rewrite
    (lc : TermOver BuiltinOrVar) (ld : TermOver BuiltinOrVar)
    (a : Act)
    (rc : TermOver Expression) (rd : TermOver Expression)
    (scs : list SideCondition)
| mld_context
    (c : TermOver BuiltinOrVar)
    (h : variable)
    (Hh : length (filter (eq h) (vars_of_to_l2r c)) = 1)
    (scs : list SideCondition)
. 

Definition actions_of_decl
    {Σ : StaticModel}
    (Act : Set)
    (d : MinusL_Decl Act)
    : list Act
:=
match d with
| mld_rewrite _ _ _ a _ _ _ => [a]
| mld_context _ _ _ _ _ => []
end.


Record MinusL_LangDef
    {Σ : StaticModel}
    (Act : Set)
    : Type
 := mkMinusL_LangDef {
    mlld_isValue : Expression -> (list SideCondition) ;
    mlld_decls : list (MinusL_Decl Act) ;
}.


Definition actions_of_ldef
    {Σ : StaticModel}
    (Act : Set)
    (D : MinusL_LangDef Act)
    : list Act
:=
    concat (map (actions_of_decl Act) (mlld_decls Act D))
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

