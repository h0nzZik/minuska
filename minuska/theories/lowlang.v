From Minuska Require Import
    prelude
    spec
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



Definition Valuation {Σ : StaticModel}
        := gmap variable GroundTerm
    .

#[export]
Instance VarsOf_valuation
    {Σ : StaticModel}
    {var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    : VarsOf (gmap var GroundTerm) var
:= {|
    vars_of := fun ρ => dom ρ ; 
|}.


Fixpoint Expression_evaluate
    {Σ : StaticModel}
    (ρ : gmap variable GroundTerm)
    (t : Expression)
    : option GroundTerm :=
match t with
| ft_element e => Some e
| ft_variable x => ρ !! x
| ft_nullary f =>
    Some (uglify' (builtin_nullary_function_interp f))
| ft_unary f t =>
    e ← prettify <$> Expression_evaluate ρ t;
    Some (uglify' (builtin_unary_function_interp f e))
| ft_binary f t1 t2 =>
    e1 ← prettify <$> Expression_evaluate ρ t1;
    e2 ← prettify <$> Expression_evaluate ρ t2;
    Some (uglify' (builtin_binary_function_interp f e1 e2))
| ft_ternary f t1 t2 t3 =>
    e1 ← prettify <$> Expression_evaluate ρ t1;
    e2 ← prettify <$> Expression_evaluate ρ t2;
    e3 ← prettify <$> Expression_evaluate ρ t3;
    Some (uglify' (builtin_ternary_function_interp f e1 e2 e3))
end.


Definition val_satisfies_ap
    {Σ : StaticModel} (ρ : Valuation) (ap : AtomicProposition)
    : Type :=
match ap with
| apeq e1 e2 => 
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    v1 = v2 /\ isSome v1
end
.

#[export]
Program Instance Satisfies_val_ap
    {Σ : StaticModel} :
    Satisfies
        (gmap variable GroundTerm)
        unit
        AtomicProposition
        variable
:= {|
    satisfies := fun ρ u ap => val_satisfies_ap ρ ap ;
|}.


Inductive aoxy_satisfies_aoxz
    {Σ : StaticModel}
    {V X Y Z var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z var}
    {_S2 : Satisfies V (Y) (PreTerm' X Z) var}
    {_S3 : Satisfies V ((PreTerm' X Y)) Z var}

    :
    V ->
    ((PreTerm' X Y)) ->
    PreTerm' X Z ->
    Type :=

| asa_x:
    forall ρ x,
        aoxy_satisfies_aoxz
            ρ
            (@pt_operator X Y x)
            (@pt_operator X Z x)

| asa_operand:
    forall ρ aoxy aoxz y z,
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ y z ->
        aoxy_satisfies_aoxz
            ρ
            (pt_app_operand aoxy y)
            (pt_app_operand aoxz z)

| asa_operand_asa:
    forall ρ aoxy aoxz aoxy2 z,
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ aoxy2 z ->
        aoxy_satisfies_aoxz
        (* The right-side, the symbolic one, has more compact representation - so *)
            ρ
            (pt_app_ao aoxy aoxy2)
            (pt_app_operand aoxz z)

| asa_asa_operand:
    forall
        (ρ : V)
        (aoxy : PreTerm' X Y)
        (aoxz aoxz2 : PreTerm' X Z)
        (y : Y),
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ y aoxz2 ->
        aoxy_satisfies_aoxz
            ρ
            (pt_app_operand aoxy y)
            ((pt_app_ao aoxz aoxz2))

| asa_asa:
    forall ρ aoxy1 aoxy2 aoxz1 aoxz2,
        aoxy_satisfies_aoxz ρ aoxy1 aoxz1 ->
        aoxy_satisfies_aoxz ρ aoxy2 aoxz2 ->
        aoxy_satisfies_aoxz
            ρ
            (pt_app_ao aoxy1 aoxy2)
            (pt_app_ao aoxz1 aoxz2)
.


#[export]
Instance Satisfies_aoxy_aoxz
    {Σ : StaticModel}
    {V X Y Z var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z var}
    {_S2 : Satisfies V (Y) (PreTerm' X Z) var}
    {_S3 : Satisfies V ((PreTerm' X Y)) Z var}
    :
    Satisfies V ((PreTerm' X Y)) (PreTerm' X Z) var
:= {|
    satisfies := aoxy_satisfies_aoxz ;
|}.


Inductive aoxyo_satisfies_aoxzo
    {Σ : StaticModel}
    (V X Y Z var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z var}
    {_S2 : Satisfies V ((PreTerm' X Y)) Z var}
    {_S3 : Satisfies V ((PreTerm' X Y)) (PreTerm' X Z) var}
    : V ->
        ((Term' X Y)) ->
        (Term' X Z) ->
        Type
:=
| axysaxz_app:
    forall
        (ρ : V)
        (xy : PreTerm' X Y)
        (xz : PreTerm' X Z)
        (pf : satisfies ρ xy xz),
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@term_preterm _ _  xy) (term_preterm xz)

| axysaxz_operand:
    forall (ρ : V) (y : Y) (z : Z) (pf : satisfies ρ y z),
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@term_operand X Y y) (@term_operand X Z z)

| axysaxz_combined:
    forall (ρ : V) axy axz,
        satisfies ρ axy axz ->
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@term_preterm _ _  axy) (@term_operand X Z axz)
.

#[export]
Program Instance Satisfies_aoxyo_aoxzo
    {Σ : StaticModel}
    (V X Y Z var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z var}
    {_S2 : Satisfies V ((PreTerm' X Y)) Z var}
    {_S3 : Satisfies V ((PreTerm' X Y)) (PreTerm' X Z) var}
    :
    Satisfies V ((Term' X Y)) (Term' X Z) var
:= {|
    satisfies := aoxyo_satisfies_aoxzo V X Y Z var;
|}.

Inductive builtin_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    :
    builtin_value ->
    BuiltinOrVar ->
    Type :=

| bsbv_builtin:
    forall b,
        builtin_satisfies_BuiltinOrVar ρ b (bov_builtin b)

| bsbv_var:
    forall (b : builtin_value) (x : variable),
        ρ !! x = Some (@term_operand symbol builtin_value b) ->
        builtin_satisfies_BuiltinOrVar ρ b (bov_variable x)
.

Definition builtin_satisfies_BuiltinOrVar'
    {Σ : StaticModel}
    (ρ : Valuation)
    (b : builtin_value)
    (bov : BuiltinOrVar)
    : Type
:= builtin_satisfies_BuiltinOrVar ρ b bov.

#[export]
Instance Subseteq_Valuation {Σ : StaticModel}
    : SubsetEq Valuation
.
Proof.
    unfold Valuation.
    apply _.
Defined.



#[export]
Instance Satisfies_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation (builtin_value) BuiltinOrVar variable
:= {|
    satisfies := builtin_satisfies_BuiltinOrVar' ;
|}.

Definition PreTerm'_symbol_builtin_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : PreTerm' symbol builtin_value)
    (bov : BuiltinOrVar)
    : Type :=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (term_preterm aop)
end.

#[export]
Program Instance Satisfies__PreTerm'_symbol_builtin__BuiltinOrVar
    {Σ : StaticModel}
    : Satisfies Valuation ((PreTerm' symbol builtin_value)) BuiltinOrVar variable
:= {| 
    satisfies := PreTerm'_symbol_builtin_satisfies_BuiltinOrVar
|}.

Definition PreTerm'_symbol_builtin_satisfies'_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : (PreTerm' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Type
:= PreTerm'_symbol_builtin_satisfies_BuiltinOrVar ρ aop bov.

#[export]
Instance Satisfies_PreTerm'_symbol_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation ((PreTerm' symbol builtin_value)) BuiltinOrVar variable
:= {|
    satisfies := PreTerm'_symbol_builtin_satisfies'_BuiltinOrVar ;
|}.



#[export]
Instance Satisfies__builtin__ao'B
    {Σ : StaticModel}
    {V B var : Type}
    {_SV : SubsetEq V}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VV : VarsOf V var}
    :
    Satisfies
        V
        (builtin_value)
        (PreTerm' symbol B)
        var
:= {| 
    satisfies := fun _ _ _ => false ;
|}.



#[export]
Instance Satisfies_aos__builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        ((PreTerm' symbol builtin_value))
        (PreTerm' symbol BuiltinOrVar)
        variable
.
Proof.
    apply @Satisfies_aoxy_aoxz.
    {
        apply _.
    }
    {
        apply Satisfies__builtin__ao'B.
    }
    {
        apply _.
    }
Defined.


#[export]
Instance Satisfies_aosb_aosbf
    {Σ : StaticModel}
    {A B : Type}
    {SatAB : Satisfies Valuation (A) B variable}
    {_S2 : Satisfies Valuation (A) (PreTerm' symbol B) variable}
    {SatA'B : Satisfies Valuation ((PreTerm' symbol A)) B variable}
    :
    Satisfies Valuation ((PreTerm' symbol A)) (PreTerm' symbol B) variable
.
Proof.
    apply _.
Defined.

#[export]
Instance
Satisfies_aoosb_aoosbf
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        ((Term' symbol builtin_value))
        (Term' symbol BuiltinOrVar)
        variable
.
Proof. apply _. Defined.

#[export]
Instance Satisfies_valGroundTerm_SymbolicTerm
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        GroundTerm
        SymbolicTerm
        variable
.
Proof. 
    apply _.
Defined.




Definition valuation_satisfies_sc
    {Σ : StaticModel}
    (ρ : Valuation)
    (sc : SideCondition) : Type :=
match sc with
| sc_constraint c => satisfies ρ () c
end.

#[export]
Instance Satisfies_val_sc
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        unit
        SideCondition
        variable
:= {|
    satisfies := fun a b c => valuation_satisfies_sc a c ;
|}.


Definition GroundTerm_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (g : GroundTerm)
    (bov : BuiltinOrVar)
    : Type :=
match bov with
| bov_builtin b =>
    match g with
    | term_preterm _ => False
    | term_operand b' => b = b'
    end
| bov_variable x => ρ !! x = Some g
end.

#[export]
Instance Satisfies_GroundTerm_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation (GroundTerm) BuiltinOrVar variable
:= {|
    satisfies := GroundTerm_satisfies_BuiltinOrVar ;
|}.


Definition builtin_value_satisfies_SymbolicTerm
    {Σ : StaticModel}
    :
    Valuation ->
    builtin_value ->
    SymbolicTerm ->
    Type := fun ρ b t =>
match t with
| term_preterm _ => False
| term_operand bov =>
    satisfies ρ b bov
end.

#[export]
Instance Satisfies_builtin_value_SymbolicTerm
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        builtin_value
        SymbolicTerm
        variable
:= {|
    satisfies :=  builtin_value_satisfies_SymbolicTerm ;
|}.

Definition PreTerm'_symbol_builtin_value_satisfies_BOV
    {Σ : StaticModel}
    (ρ : Valuation)
    (ao : (PreTerm' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Type
:=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (term_preterm ao) 
end
.

#[export]
Instance Satisfies__PreTerm'_symbol_builtin_value__BOV
    {Σ : StaticModel}
    {V : Type}
    :
    Satisfies
        Valuation
        ((PreTerm' symbol builtin_value))
        BuiltinOrVar
        variable
:= {|
    satisfies := PreTerm'_symbol_builtin_value_satisfies_BOV;
|}.

Definition PreTerm'_symbol_A_satisfies_SymbolicTermB'
    {Σ : StaticModel}
    (V A B var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (A) B var}
    {_S2 : Satisfies V ((PreTerm' symbol A)) B var}
    {_S3 : Satisfies V (PreTerm' symbol A) (PreTerm' symbol B) var}
    :
    V ->
    (PreTerm' symbol A) ->
    Term' symbol B ->
    Type
:=  fun ρ a =>
    satisfies
    ρ (term_preterm a)
.

#[export]
Instance Satisfies__lift_builtin_to_aosb
    {Σ : StaticModel}
    {V A B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (A) B var}
    {_S2 : Satisfies V ((PreTerm' symbol A)) B var}
    {_S3 : Satisfies V (PreTerm' symbol A) (PreTerm' symbol B) var}
    :
    Satisfies
        V
        ((PreTerm' symbol A))
        (Term' symbol B)
        var
:= {|
    satisfies :=
        PreTerm'_symbol_A_satisfies_SymbolicTermB' V A B var;
|}.

#[export]
Instance Satisfies__lift_builtin_to_aosbo
    {Σ : StaticModel}
    {V A B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {bsB : Satisfies V (A) B var}
    {sat2 : Satisfies V ((PreTerm' symbol A)) B var}
    {sat3 : Satisfies V ((PreTerm' symbol A)) (PreTerm' symbol B) var}
    :
    Satisfies V
        ((Term' symbol A))
        (Term' symbol B)
        var
.
Proof. apply _. Defined.

Definition PreTerm'_symbol_builtin_satisfies_SymbolicTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (PreTerm' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (PreTerm' symbol builtin_value) (PreTerm' symbol BuiltinOrVar) var}
    :
    V ->
    ((PreTerm' symbol builtin_value)) ->
    SymbolicTerm ->
    Type
:=  fun ρ a =>
    satisfies ρ (term_preterm a)
.

#[export]
Instance Satisfies__PreTerm'_symbol_builtin__SymbolicTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (PreTerm' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (PreTerm' symbol builtin_value) (PreTerm' symbol BuiltinOrVar) var}
    :
    Satisfies V
        ((PreTerm' symbol builtin_value))
        SymbolicTerm
        var
:= {|
    satisfies :=
        PreTerm'_symbol_builtin_satisfies_SymbolicTerm ;
|}.




#[local]
Obligation Tactic := idtac.

#[export]
Instance Satisfies_builtin_expr
    {Σ : StaticModel}:
    Satisfies
        Valuation
        builtin_value
        Expression
        variable
:= {|
    satisfies := (fun ρ b e =>
        Expression_evaluate ρ e = Some (term_operand b)
    ) ;
|}.


#[export]
Instance Satisfies_asb_expr
    {Σ : StaticModel}:
    Satisfies
        Valuation
        ((PreTerm' symbol builtin_value))
        Expression
        variable
:= {|
    satisfies := (fun ρ x e =>
        Expression_evaluate ρ e = Some (term_preterm x)
    ) ;
|}.


#[export]
Instance Satisfies__GroundTerm__ExpressionTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) Expression var}
    {_S2 : Satisfies V (PreTerm' symbol builtin_value) Expression var}
    {_S3 : Satisfies V (PreTerm' symbol builtin_value) (PreTerm' symbol Expression) var}
    :
    Satisfies
        V
        GroundTerm
        ExpressionTerm
        var
.
Proof. apply _. Defined.

#[export]
Instance Satisfies_gt_var
    {Σ : StaticModel}:
    Satisfies
        Valuation
        GroundTerm
        variable
        variable
:= {|
    satisfies := (fun ρ g x => ρ !! x = Some g)
|}.

#[export]
Instance Subseteq_ValuationLR
    {Σ : StaticModel}
    : SubsetEq (Valuation * LeftRight)
:= {
    subseteq a b := subseteq a.1 b.1 /\ a.2 = b.2
}.


(* TODO *)
#[export]
Instance VarsOf_ValuationLR
    {Σ : StaticModel}
    : VarsOf (Valuation * LeftRight) variable
:= {
    vars_of a := vars_of a.1
}.


#[export]
Instance Satisfies_sym_bov
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        symbol
        BuiltinOrVar
        variable
:= {|
    satisfies := fun _ _ _ => False ;
|}.


#[export]
Instance Satisfies_Valuation_LR_SideCondition
    {Σ : StaticModel}
    :
    Satisfies
        (Valuation * LeftRight)
        unit
        SideCondition
        variable
:= {|
    satisfies := fun ρd => let ρ := ρd.1 in
        satisfies ρ
        ;
|}.

Definition GroundTerm_satisfies_SymbolicTerm
    {Σ : StaticModel}
    : GroundTerm -> SymbolicTerm -> Type :=
    fun g φ => { ρ : Valuation & satisfies ρ g φ }
.

#[export]
Instance VarsOf_unit {Σ : StaticModel}: VarsOf unit variable := {|
    vars_of _ := ∅ ;
|}.

#[export]
Instance Subseteq_unit {Σ : StaticModel}: SubsetEq unit := 
    fun _ _ => true
.


#[export]
Instance Satisfies__GroundTerm__SymbolicTerm_inall
    {Σ : StaticModel}
    :
    Satisfies
        unit
        GroundTerm
        SymbolicTerm
        variable
:= {|
    satisfies := fun _ => GroundTerm_satisfies_SymbolicTerm ;
|}.

#[export]
Instance Satisfies_valuation_scs
    {Σ : StaticModel}
    : Satisfies
        Valuation
        unit
        (list SideCondition)
        variable
:= {|
    satisfies := fun ρ _ l => forall x, x ∈ l -> satisfies ρ () x;
|}.

#[export]
Instance
    Satisfies_symbol_B
    {Σ : StaticModel}
    {V B var : Type}
    {_SV : SubsetEq V}
    {_EDvar : EqDecision var}
    {_Covar : Countable var}
    {_VV : VarsOf V var}
    :
    Satisfies
        V
        symbol
        B
        var
:= {|
    satisfies := fun _ _ _ => False ;
|}.

Definition flattened_rewrites_in_valuation_under_to
    {Σ : StaticModel}
    {Act : Set}
    (ρ : Valuation)
    (r : RewritingRule Act)
    (from : GroundTerm)
    (under : Act)
    (to : GroundTerm)
    : Type
:= ((satisfies ρ from (fr_from r))
* (satisfies ρ to (fr_to r))
* (@satisfies Σ Valuation unit (list SideCondition) _ _ _ _ _ _ ρ tt (fr_scs r))
* (under = fr_act r)
)%type
.


Definition flattened_rewrites_to
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    (from : GroundTerm)
    (under : Act)
    (to : GroundTerm)
    : Type
:= { ρ : Valuation &
    flattened_rewrites_in_valuation_under_to ρ r from under to
   }
.




#[export]
Instance Satisfies_TermOverBuiltin_TermOverBoV
    {Σ : StaticModel}
    : Satisfies
        Valuation
        (TermOver builtin_value)
        (TermOver BuiltinOrVar)
        variable
:= {|
    satisfies := fun ρ tg ts => satisfies ρ (uglify' tg) (uglify' ts) ;
|}.



#[export]
Instance Satisfies_TermOverBuiltin_TermOverExpression
    {Σ : StaticModel}
    : Satisfies
        Valuation
        (TermOver builtin_value)
        (TermOver Expression)
        variable
:= {|
    satisfies := fun ρ tg ts => satisfies ρ (uglify' tg) (uglify' ts) ;
|}.



Inductive flattened_rewrites_to_over
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    :
    TermOver builtin_value ->
    list Act ->
    TermOver builtin_value ->
    Type
:=
| frto_base: forall t,
        flattened_rewrites_to_over Γ t nil t
| frto_step: forall (t1 t2 t3 : TermOver builtin_value) w a r,
    r ∈ Γ ->
    flattened_rewrites_to r (uglify' t1) a (uglify' t2) ->
    flattened_rewrites_to_over Γ t2 w t3 ->
    flattened_rewrites_to_over Γ t1 (a::w) t3
.
