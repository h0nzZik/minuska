From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
.

(*
    @pre: topSymbol, cseqSymbol, holeSymbol, contVariable, and dataVariable have to be fresh enough
*)
Definition ctx_heat
    {Σ : StaticModel}
    {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (contVariable dataVariable : variable)
    (isValue : Expression -> (list SideCondition))
    (c : TermOver BuiltinOrVar)
    (h : variable)
    (scs : list SideCondition)
    :
    RewritingRule Act
:= {|
    fr_from := (uglify' (t_term topSymbol [
        (t_term cseqSymbol [
            c;
            (t_over (bov_variable contVariable))
        ]);
        t_over (bov_variable dataVariable)])
    );
    fr_to   := (uglify' (t_term topSymbol [
        (t_term cseqSymbol [
            (t_over (ft_variable h));
            (t_term cseqSymbol [
                (TermOverBoV_to_TermOverExpr
                    (TermOverBoV_subst c h (t_term holeSymbol []))
                );
                (t_over (ft_variable contVariable))
            ])
        ]);
        t_over (ft_variable dataVariable)])
    );
    fr_scs := scs;
    fr_act := invisible_act ;
|}.

Definition ctx_cool
    {Σ : StaticModel}
    {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (contVariable dataVariable : variable)
    (isValue : Expression -> (list SideCondition))
    (c : TermOver BuiltinOrVar)
    (h : variable)
    :
    RewritingRule Act
:= {|
    fr_from := (uglify' (t_term topSymbol [
        (t_term cseqSymbol [
            (t_over (bov_variable h));
            (t_term cseqSymbol [
                (TermOverBoV_subst c h (t_term holeSymbol []));
                (t_over (bov_variable contVariable))
            ])
        ]);
        t_over (bov_variable dataVariable)])
    );

    fr_to   := (uglify' (t_term topSymbol [
        (t_term cseqSymbol [
            (TermOverBoV_to_TermOverExpr c);
            (t_over (ft_variable contVariable))
        ]);
        t_over (ft_variable dataVariable)])
    );

    fr_scs := isValue (ft_variable h);

    fr_act := invisible_act ;
|}.


Definition CompileT {Σ : StaticModel} {Act : Set} : Type :=
    MinusL_LangDef Act -> RewritingTheory Act
.

Definition down
    {Σ : StaticModel}
    {A : Type}
    (topSymbol : symbol)
    (ctrl data : TermOver A)
    : TermOver A
:=
    t_term topSymbol [ctrl;data]
.


Definition compile' {Σ : StaticModel} {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (isValue : Expression -> (list SideCondition))
    (d : MinusL_Decl Act)
    : (list (RewritingRule Act))
:=
    match d with
    | mld_rewrite _ lc ld a rc rd scs => [
        ({|
            fr_from := uglify' (down topSymbol lc ld) ;
            fr_to := uglify' (down topSymbol rc rd) ;
            fr_scs := scs ;
            fr_act := a;
        |})
        ]
    | mld_context _ c h scs =>
        let vars := vars_of_to_l2r c in
        let contVariable := fresh vars in
        let dataVariable := fresh (contVariable::vars) in
         [
            (ctx_heat
                invisible_act
                topSymbol cseqSymbol holeSymbol
                contVariable dataVariable
                isValue
                c h scs
            );
            (ctx_cool
                invisible_act
                topSymbol cseqSymbol holeSymbol
                contVariable dataVariable
                isValue
                c h
            )
        ]
    end
.

Definition compile {Σ : StaticModel}
    {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol) 
    : CompileT :=
    fun D => concat (map (compile' invisible_act topSymbol cseqSymbol holeSymbol (mlld_isValue unit D)) (mlld_decls unit D))
.

Lemma satisfies_top_bov
    {Σ : StaticModel}
    (ρ : Valuation)
    topSymbol
    (ctrl1 state1 : TermOver builtin_value) (lc ld : TermOver BuiltinOrVar)
    :
    (satisfies ρ ctrl1 lc /\ satisfies ρ state1 ld) <->
    satisfies ρ (apply_symbol' topSymbol [uglify' ctrl1; uglify' state1])
        (apply_symbol' topSymbol [uglify' lc; uglify' ld])
.
Proof.
    split.
    {
        intros [H1 H2].
        unfold apply_symbol'. simpl.
        destruct ctrl1,lc,state1,ld; simpl in *; (repeat constructor);
            inversion H1; inversion H2; subst; assumption.
    }
    {
        intros H.
        inversion H; subst; clear H.
        inversion pf; subst; clear pf;
        destruct ctrl1,lc,state1,ld;
            unfold to_PreTerm' in *;
            simpl in *;
            try (solve [inversion H1]);
            ltac1:(simplify_eq/=);
            try (inversion H; subst; clear H);
            try (inversion H2; subst; clear H2);
            try (inversion H0; subst; clear H0);
            split; unfold satisfies; simpl;
            (repeat constructor); try assumption;
            unfold apply_symbol'; simpl;
            try constructor; try assumption;
            try (solve [inversion H7]);
            try (solve [inversion H3]).
    }
Qed.

Lemma satisfies_top_expr
    {Σ : StaticModel}
    (ρ : Valuation)
    topSymbol
    (ctrl1 state1 : TermOver builtin_value) (lc ld : TermOver Expression)
    :
    (satisfies ρ ctrl1 lc /\ satisfies ρ state1 ld) <->
    satisfies ρ (apply_symbol' topSymbol [uglify' ctrl1; uglify' state1])
        (apply_symbol' topSymbol [uglify' lc; uglify' ld])
.
Proof.
    split.
    {
        intros [H1 H2].
        unfold apply_symbol'. simpl.
        destruct ctrl1,lc,state1,ld; simpl in *; (repeat constructor);
            inversion H1; inversion H2; subst; assumption.
    }
    {
        intros H.
        inversion H; subst; clear H.
        inversion pf; subst; clear pf;
        destruct ctrl1,lc,state1,ld;
            unfold to_PreTerm' in *;
            simpl in *;
            try (solve [inversion H1]);
            ltac1:(simplify_eq/=);
            try (inversion H; subst; clear H);
            try (inversion H2; subst; clear H2);
            try (inversion H0; subst; clear H0);
            split; unfold satisfies; simpl;
            (repeat constructor); try assumption;
            unfold apply_symbol'; simpl;
            try constructor; try assumption;
            try (solve [inversion H7]);
            try (solve [inversion H3]).
    }
Qed.


Lemma compile_correct
    {Σ : StaticModel}
    (topSymbol cseqSymbol holeSymbol : symbol) 
    (D : MinusL_LangDef unit)
    :
    let Γ := compile topSymbol cseqSymbol holeSymbol D in
    forall
        (lc ld rc rd : TermOver builtin_value)
        (w : list ())
        (ρ : Valuation),
        MinusL_rewritesInVal unit D lc ld w  ρ rc rd
        <->
        flattened_rewrites_to_over Γ
            (down topSymbol lc ld)
            w
            (down topSymbol rc rd)
.
Proof.
    intros.
    destruct D as [iV ds]; simpl in *.
    split; intros HH.
    {
        induction HH.
        {
            unfold compile in Γ. simpl in H. simpl in Γ.
            apply elem_of_list_lookup_1 in H.
            destruct H as [i Hi].
            ltac1:(unfold Γ).
            assert (i < length ds).
            {
                apply lookup_lt_Some in Hi.
                exact Hi.
            }
            rewrite <- (firstn_skipn i ds).
            rewrite <- (firstn_skipn i ds) in Hi.
            rewrite lookup_app_r in Hi>[|rewrite take_length; ltac1:(lia)].
            rewrite take_length in Hi.
            ltac1:(replace ((i - i `min` length ds)) with (0) in Hi by lia).
            remember (drop i ds) as ds'.
            destruct ds'.
            {
                simpl in Hi. inversion Hi.
            }
            simpl in Hi. inversion Hi; subst; clear Hi.
            rewrite map_app.
            rewrite concat_app.
            simpl.
            eapply frto_step>[|()|apply frto_base].
            {
                rewrite elem_of_app.
                right.
                rewrite elem_of_cons.
                left.
                reflexivity.
            }
            {
                simpl.
                unfold flattened_rewrites_to.
                exists ρ.
                unfold flattened_rewrites_in_valuation_to.
                simpl.
                split.
                {
                    apply satisfies_top_bov.
                    split; assumption.
                }
                split.
                {
                    apply satisfies_top_expr.
                    split; assumption.
                }
                {
                    assumption.
                }
            }
        }
        {

        }

    }
    {

    }

Qed.