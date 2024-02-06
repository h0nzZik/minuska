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
    fun D => concat (map (compile' invisible_act topSymbol cseqSymbol holeSymbol (mlld_isValue Act D)) (mlld_decls Act D))
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
    {Act : Set}
    {_AD : EqDecision Act}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol) 
    (D : MinusL_LangDef Act)
    :
    ~ (invisible_act ∈ actions_of_ldef Act D) ->
    let Γ := compile invisible_act topSymbol cseqSymbol holeSymbol D in
    forall
        (lc ld rc rd : TermOver builtin_value)
        (w : list Act)
        (ρ : Valuation),
        MinusL_rewritesInVal Act D lc ld w  ρ rc rd
        <->
        flattened_rewrites_to_over Γ
            (down topSymbol lc ld)
            (filter (fun x => x <> invisible_act) w)
            (down topSymbol rc rd)
.
Proof.
    intros Hinvisible.
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
            simpl. rewrite filter_cons. rewrite filter_nil.
            destruct (decide (a <> invisible_act)).
            {
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
                    unfold flattened_rewrites_in_valuation_under_to.
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
                    split>[assumption|].
                    reflexivity.
                }
            }
            {
                unfold actions_of_ldef in Hinvisible.
                simpl in Hinvisible.
                rewrite elem_of_list_In in Hinvisible.
                rewrite in_concat in Hinvisible.
                ltac1:(exfalso).
                apply n.
                clear n. intros Hsub. subst a. apply Hinvisible. clear Hinvisible.
                exists [invisible_act].
                split>[|constructor].
                rewrite in_map_iff.
                rewrite <- (firstn_skipn i ds).
                exists (mld_rewrite Act lc ld invisible_act rc rd scs).
                simpl.
                split>[reflexivity|].
                apply in_or_app.
                right.
                rewrite <- Heqds'.
                constructor. reflexivity. reflexivity.
            }
        }
        {
            simpl in *.
            assert (Htmp := @frto_step Σ Act Γ).
            specialize (Htmp (down topSymbol ctrl1 state1)).
            apply elem_of_list_lookup_1 in H.
            destruct H as [i Hi].
            assert (i < length ds).
            {
                apply lookup_lt_Some in Hi.
                exact Hi.
            }
            ltac1:(unfold Γ in Htmp).
            rewrite <- (firstn_skipn i ds) in Htmp.
            unfold compile in Htmp.
            simpl in Htmp.
            rewrite map_app in Htmp.
            rewrite concat_app in Htmp.
            remember (drop i ds) as dids.
            destruct dids.
            {
                rewrite <- (firstn_skipn i ds) in Hi.
                rewrite <- Heqdids in Hi.
                rewrite app_nil_r in Hi.
                apply lookup_take_Some in Hi.
                destruct Hi as [Hi Hcontra].
                clear -Hcontra.
                ltac1:(lia).
            }
            simpl in Htmp.
            ltac1:(setoid_rewrite elem_of_app in Htmp).
            ltac1:(setoid_rewrite elem_of_app in Htmp).
            unfold compile' at 2 in Htmp'.
            destruct m; simpl in *.
            {
                clear Htmp.
                rewrite <- (firstn_skipn i ds) in Hi.
                rewrite <- Heqdids in Hi.
                rewrite lookup_app_r in Hi>[|rewrite take_length;ltac1:(lia)].
                rewrite take_length in Hi.
                ltac1:(replace ((i - i `min` length ds)) with (0) in Hi by lia).
                simpl in Hi.
                inversion Hi.
            }
            {
                ltac1:(epose proof(Htmp' := Htmp ?[t2] ?[t3] ?[w0] ?[a] ?[r])).
                clear Htmp.
                
                ltac1:(ospecialize (Htmp' _)).
                {
                    right. left. rewrite elem_of_list_In. constructor.
                    reflexivity.
                }
                ltac1:(ospecialize (Htmp' _)).
                {
                    unfold flattened_rewrites_to.
                    exists ρ.
                    unfold flattened_rewrites_in_valuation_under_to.
                    simpl.
                    split.
                    {
                        clear Htmp'.
                        ltac1:(
                            replace ((term_operand (bov_variable (fresh (fresh (vars_of_to_l2r c0) :: vars_of_to_l2r c0)))))
                            with (uglify' (t_over ((bov_variable (fresh (fresh (vars_of_to_l2r c0) :: vars_of_to_l2r c0))))))
                            by reflexivity
                        ).
                        ltac1:(
                            replace (apply_symbol' cseqSymbol [uglify' c0; term_operand (bov_variable (fresh (vars_of_to_l2r c0)))])
                            with (uglify' (t_term cseqSymbol [c0; t_over (bov_variable (fresh (vars_of_to_l2r c0)))]))
                            by reflexivity
                        ).
                        apply satisfies_top_bov.
                        
                    }
            
            }


            rewrite concat_app in Htmp.
            ltac1:(setoid_rewrite elem_of_list_In in Htmp).
            ltac1:(setoid_rewrite in_concat in Htmp).
            Search concat.
            rewrite elem_of_concat in Htmp.
            
            About frto_step.
            eapply frto_step in IHHH.

        }

    }
    {

    }

Qed.