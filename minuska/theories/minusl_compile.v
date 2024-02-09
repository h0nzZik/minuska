From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    semantics_properties
    basic_matching
    varsof
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

Definition analyze_list_from_end {A : Type} (l : list A)
    : {l = nil} + { (exists (l' : list A) (x : A), l = l'++[x])}
.
Proof.
    induction l.
    {
        left. reflexivity.
    }
    {
        right.
        destruct IHl as [IHl|IHl].
        {
            subst. exists []. exists a. reflexivity.
        }
        {
            destruct IHl as [l' [x Hl']].
            subst.
            exists (a::l'). exists x. simpl. reflexivity.
        }
    }
Qed.

Lemma satisfies_top_bov_cons
    {Σ : StaticModel}
    (ρ : Valuation)
    (topSymbol topSymbol' : symbol)
    (states : list (TermOver builtin_value))
    (lds : list (TermOver BuiltinOrVar))
    :
    (
        length states = length lds /\
        Forall id (zip_with (satisfies ρ) states lds)
        /\ topSymbol = topSymbol'
    ) <->
    (
        satisfies ρ (fold_left helper (map uglify' states) (pt_operator topSymbol))
        (fold_left helper (map uglify' lds) (pt_operator topSymbol'))
    )
.
Proof.
    split.
    {
        intros H.
        destruct H as [Hlens H].
        revert lds Hlens H.
        induction states using rev_ind; intros lds Hlens H; simpl in *.
        {
            destruct lds; simpl in *.
            {
                destruct H as [_ H]. subst.
                constructor.
            }
            {
                inversion Hlens.
            }
        }
        {
            destruct (analyze_list_from_end lds) as [?|He].
            {
                subst. simpl in *.
                rewrite app_length in Hlens.
                simpl in Hlens.
                ltac1:(lia).
            }
            {
                destruct He as [l' [x0 Hl']].
                subst lds.
                rewrite map_app.
                rewrite map_app.
                rewrite fold_left_app.
                rewrite fold_left_app.
                simpl.
                rewrite app_length in Hlens.
                rewrite app_length in Hlens.
                simpl in Hlens.
                assert (Hlens': length states = length l') by (ltac1:(lia)).
                rewrite (zip_with_app (satisfies ρ) _ _ _ _ Hlens') in H.
                destruct H as [H ?]. subst topSymbol'.
                apply Forall_app in H.
                destruct H as [H1 H2].
                simpl in H2. rewrite Forall_cons in H2. destruct H2 as [H2 _].
                unfold helper. simpl.
                destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                    simpl in *.
                {
                    constructor.
                    apply IHstates.
                    {
                        apply Hlens'.
                    }
                    {
                        split>[|reflexivity].
                        apply H1.
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst.
                        unfold satisfies in H2; simpl in H2.
                        Print prettify.
                        ltac1:(
                            replace (prettify' ao)
                            with (prettify (term_preterm ao))
                            in H2
                            by reflexivity
                        ).
                        ltac1:(
                            replace (prettify' ao0)
                            with (prettify (term_preterm ao0))
                            in H2
                            by reflexivity
                        ).
                        rewrite (cancel uglify' prettify) in H2.
                        rewrite (cancel uglify' prettify) in H2.
                        unfold satisfies in H2; simpl in H2.
                        inversion H2; subst; clear H2; assumption.
                    }
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2; subst; clear H2.
                    constructor.
                    { apply IHstates; (repeat split); try assumption; try reflexivity. }
                    { apply H4. }
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2.
                }
                {
                    unfold satisfies in H2. simpl in H2.
                    rewrite Hux in H2. rewrite Hux0 in H2.
                    inversion H2; subst; clear H2.
                    constructor.
                    { apply IHstates; (repeat split); try assumption; try reflexivity. }
                    { assumption. }
                }
            }
        }
    }
    {
        intros H.
        revert lds H.
        induction states using rev_ind; intros lds pf.
        {
            destruct lds; simpl in *.
            {
                split>[reflexivity|].
                split.
                {
                    apply Forall_nil. exact I.
                }
                {
                    inversion pf. subst. reflexivity.
                }
            }
            {
                inversion pf; subst; clear pf.
                ltac1:(exfalso).
                induction lds using rev_ind.
                {
                    simpl in H2. unfold helper in H2.
                    destruct (uglify' t); simpl in H2; inversion H2.
                }
                {
                    rewrite map_app in H2.
                    rewrite fold_left_app in H2.
                    simpl in H2.
                    unfold helper in H2.
                    destruct (uglify' x) eqn:Hux.
                    {
                        inversion H2.
                    }
                    {
                        inversion H2.
                    }
                }
            }
        }
        {
            destruct (analyze_list_from_end lds); simpl in *.
            {
                ltac1:(exfalso).
                subst.

                rewrite map_app in pf.
                rewrite fold_left_app in pf.
                simpl in pf.
                unfold helper in pf.
                destruct (uglify' x) eqn:Hux.
                {
                    inversion pf.
                }
                {
                    inversion pf.
                }
            }
            {
                destruct e as [l' [x0 Hlds]].
                subst lds; simpl in *.
                rewrite map_app in pf.
                rewrite map_app in pf.
                simpl in pf.
                rewrite fold_left_app in pf.
                rewrite fold_left_app in pf.
                simpl in pf.
                (*
                unfold helper in pf.
                rewrite app_length in Hlens.
                rewrite app_length in Hlens.
                simpl in Hlens.
                assert (Hlens': length states = length l') by (ltac1:(lia)).
                
                rewrite (zip_with_app (satisfies ρ) _ _ _ _ Hlens').
                *)

                specialize (IHstates l').
                ltac1:(ospecialize (IHstates _)).
                {
                    destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                            simpl in *.
                    {
                        inversion pf; subst; clear pf.
                        assumption.
                    }
                    {
                        inversion pf; subst; clear pf.
                        assumption.
                    }
                    {
                        inversion pf; subst; clear pf.
                        assumption.
                    }
                    {
                        inversion pf; subst; clear pf.
                        assumption.
                    }
                }
                destruct IHstates as [IHlen [IHstates ?]].
                subst topSymbol'.
                do 2 (rewrite app_length).
                simpl.
                split>[ltac1:(lia)|].
                split.
                {                
                    rewrite (zip_with_app (satisfies ρ) _ _ _ _ IHlen).
                    rewrite Forall_app.
                    split.
                    {
                        apply IHstates.
                        
                    }
                    {
                        simpl.
                        rewrite Forall_cons.
                        split>[|apply Forall_nil; exact I].
                        destruct (uglify' x) eqn:Hux, (uglify' x0) eqn:Hux0;
                            simpl in *; inversion pf; subst; clear pf;
                            unfold satisfies; simpl; rewrite Hux; rewrite Hux0;
                            try constructor; try assumption.
                        inversion H5.
                    }
                }
                {
                    reflexivity.
                }
            }
        }
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

Lemma satisfies_var
    {Σ : StaticModel}
    (ρ : Valuation)
    x γ:
    ρ !! x = Some (uglify' γ) ->
    satisfies ρ γ (t_over (bov_variable x))
.
Proof.
    intros H.
    destruct γ; (repeat constructor); assumption.
Qed.

Lemma subst_notin
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of_to_l2r φ ->
    TermOverBoV_subst φ h ψ = φ
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        {
            intros _. reflexivity.
        }
        {
            destruct (decide (h = x)); simpl.
            {
                subst. intros HContra. ltac1:(exfalso). apply HContra.
                constructor.
            }
            {
                intros _. reflexivity.
            }
        }
    }
    {
        intros H2.
        f_equal.
        induction l; simpl.
        {
            reflexivity.
        }
        {
            apply Forall_cons in H.
            destruct H as [HH1 HH2].
            simpl in *.
            specialize (IHl HH2).
            rewrite elem_of_app in H2.
            apply Decidable.not_or in H2.
            destruct H2 as [H21 H22].
            specialize (IHl H22). clear H22.
            specialize (HH1 H21).
            rewrite HH1.
            rewrite IHl.
            reflexivity.
        }
    }
Qed.


Lemma weird_lemma
    {Σ : StaticModel}
    l s:
(fix go (pt : PreTerm' symbol builtin_value) :
    list (TermOver builtin_value) :=
  match pt with
| pt_operator _ => []
| pt_app_operand x y => go x ++ [t_over y]
| pt_app_ao x y => go x ++ [prettify' y]
end)
  (fold_left helper (map uglify' l) (pt_operator s)) =
l
.
Proof.
    induction l using rev_ind.
    {
        reflexivity.
    }
    {
        rewrite map_app.
        rewrite fold_left_app.
        simpl.
        unfold helper.
        destruct (uglify' x) eqn:Hux.
        {
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            subst x.
            simpl.
            f_equal.
            {
                apply IHl.
            }
        }
        {
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            subst x.
            simpl.
            f_equal.
            {
                apply IHl.
            }
        }
    }
Qed.

Lemma get_symbol_satisfies
    {Σ : StaticModel}
    (ρ : Valuation)
    (x : PreTerm' symbol builtin_value)
    (y : PreTerm' symbol BuiltinOrVar) :
    aoxy_satisfies_aoxz ρ x y ->
    PreTerm'_get_symbol x = PreTerm'_get_symbol y
.
Proof.
    intros H.
    induction H; simpl; (ltac1:(congruence)).
Qed.

Lemma satisfies_term_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (s : symbol)
    (l : list (TermOver BuiltinOrVar))
    :
    satisfies ρ γ (t_term s l) ->
    exists (lγ : list (TermOver builtin_value)),
        γ = (t_term s lγ) /\
        length l = length lγ /\
        Forall (fun p => p) (zip_with (satisfies ρ) lγ l)
.
Proof.
    revert γ.
    induction l using rev_ind; intros γ.
    {
        intros H. exists []. inversion H; subst; clear H.
        unfold to_PreTerm' in pf. simpl in pf.
        inversion pf. subst; clear pf.
        rewrite <- (cancel prettify uglify' γ).
        rewrite <- H2.
        simpl.
        repeat constructor.
    }
    {
        intros H.
        inversion H; subst; clear H.
        unfold to_PreTerm' in pf. simpl in pf.
        rewrite map_app in pf. rewrite fold_left_app in pf.
        simpl in pf.
        unfold helper in pf. simpl in pf.
        destruct (uglify' x) eqn:Hux.
        {
            simpl in *.
            apply (f_equal prettify) in H2.
            rewrite (cancel prettify uglify') in H2.
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            simpl in H2. simpl in Hux.
            subst x. simpl in *.
            subst γ. simpl in *.

            induction xy; inversion pf; subst; clear pf.
            {
            
                specialize (IHl (prettify' xy)).
                ltac1:(ospecialize (IHl _)).
                {
                    unfold satisfies; simpl.
                    ltac1:(
                        replace ((prettify' xy))
                        with (prettify (term_preterm xy))
                        by reflexivity
                    ).
                    rewrite (cancel uglify' prettify).
                    unfold apply_symbol'. simpl.
                    constructor.
                    apply H3.
                }

                destruct IHl as [lγ [IH1 [IH2 IH3]]].
                rewrite app_length.
                exists (lγ ++ [t_over b]).
                apply (f_equal uglify') in IH1.
                ltac1:(
                    replace ((prettify' xy))
                    with (prettify (term_preterm xy))
                    in IH1
                    by reflexivity
                ).
                rewrite (cancel uglify' prettify) in IH1.
                simpl in IH1. unfold apply_symbol' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                split.
                {
                    unfold to_PreTerm'.
                    simpl.
                    f_equal.
                    {
                        clear. induction lγ using rev_ind.
                        {
                            reflexivity.
                        }
                        {
                            rewrite map_app.
                            rewrite fold_left_app.
                            simpl.
                            unfold helper.
                            destruct (uglify' x); apply IHlγ.
                        }
                    }
                    {
                        f_equal.
                        apply weird_lemma.
                    }
                }
                simpl.
                split.
                {
                    rewrite IH2. reflexivity.
                }
                rewrite zip_with_app.
                rewrite Forall_app.
                split.
                {
                    apply IH3.
                }
                constructor.
                {
                    inversion H5.
                }
                {
                    apply Forall_nil. exact I.
                }
                {
                    symmetry. exact IH2.
                }
            }
            {
                eexists.
                split.
                {
                    simpl.
                    f_equal.
                    clear -H3.
                    fold (@helper Σ (@BuiltinOrVar Σ)) in H3.

                    revert xy1 H3.
                    induction l using rev_ind; simpl in *; intros xy1 H3.
                    {
                        inversion H3. reflexivity.
                    }
                    {

                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        destruct x, xy1; simpl in *;
                            inversion H3; subst; clear H3;
                            auto.
                    }
                }
                simpl.
                fold (@helper Σ (@BuiltinOrVar Σ)) in H3.
                assert (Hl : length l =
                    length
                    ((fix go (pt : PreTerm' symbol builtin_value) :
                        list (TermOver builtin_value) :=
                    match pt with
                    | pt_operator _ => []
                    | pt_app_operand x y => go x ++ [t_over y]
                    | pt_app_ao x y => go x ++ [prettify' y]
                    end)
                  xy1)).
                {
                    clear -H3.
                    revert xy1 H3.
                    induction l using rev_ind; intros xy1 H3.
                    {
                        simpl in *. inversion H3. reflexivity.
                    }
                    {
                        simpl.
                        rewrite app_length.
                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        unfold helper at 1 in H3. simpl in H3.
                        destruct (uglify' x) eqn:Hux.
                        {
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                inversion H3; subst; clear H3.
                                unfold satisfies in H6; simpl in H6.
                                inversion H6.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { apply H4. }
                            }
                        }
                        {
                            simpl.
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { 
                                    inversion H3;
                                    assumption.
                                }
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                {
                                    assumption.
                                }
                            }
                        }
                    }
                }
                split.
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {
                    rewrite zip_with_app.
                    rewrite Forall_app.
                    split.
                    {
                        Print Term'.
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' Σ).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm'. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            apply H3.
                        }
                        destruct IHl as [lγ [Hlγ1 [Hlγ2 Hlγ3]]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        clear -Hlγ3.
                        rewrite Forall_forall.
                        rewrite Forall_forall in Hlγ3.
                        intros x Hin.
                        Search zip_with elem_of.
                        rewrite elem_of_lookup_zip_with in Hin.
                        destruct Hin as [i [a [b [Hab1 [Hab2 Hab3]]]]].
                        specialize (Hlγ3 x).
                        subst x.
                        apply Hlγ3. clear Hlγ3.
                        rewrite elem_of_lookup_zip_with.
                        exists i. exists a. exists b.
                        split>[reflexivity|].
                        split>[|exact Hab3].
                        rewrite <- Hab2. clear Hab2.
                        clear.
                        assert (Htmp := @cancel_prettify_uglify Σ builtin_value).
                        unfold Cancel in Htmp. simpl in Htmp.
                        specialize (Htmp (t_term s lγ)).
                        simpl in Htmp.
                        unfold prettify' in Htmp.
                        remember ((to_PreTerm' s (map uglify' lγ))) as tpt.
                        destruct tpt; simpl in *.
                        {
                            inversion Htmp. reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                    }
                    {
                        constructor.
                        {
                            unfold satisfies.
                            simpl.
                            
                            ltac1:(
                                replace (prettify' xy2)
                                with (prettify (term_preterm xy2))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).

                            ltac1:(
                                replace (prettify' ao)
                                with (prettify (term_preterm ao))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            constructor.
                            apply H5.
                        }
                        {
                            apply Forall_nil. exact I.
                        }
                    }
                    {
                        symmetry. apply Hl.
                    }
                }   
            }
        }
        {
            simpl in *.
            apply (f_equal prettify) in H2.
            rewrite (cancel prettify uglify') in H2.
            apply (f_equal prettify) in Hux.
            rewrite (cancel prettify uglify') in Hux.
            simpl in H2. simpl in Hux.
            subst x. simpl in *.
            subst γ. simpl in *.

            induction xy; inversion pf; subst; clear pf.
            {
            
                specialize (IHl (prettify' xy)).
                ltac1:(ospecialize (IHl _)).
                {
                    unfold satisfies; simpl.
                    ltac1:(
                        replace ((prettify' xy))
                        with (prettify (term_preterm xy))
                        by reflexivity
                    ).
                    rewrite (cancel uglify' prettify).
                    unfold apply_symbol'. simpl.
                    constructor.
                    apply H3.
                }

                destruct IHl as [lγ [IH1 [IH2 IH3]]].
                rewrite app_length.
                exists (lγ ++ [t_over b]).
                apply (f_equal uglify') in IH1.
                ltac1:(
                    replace ((prettify' xy))
                    with (prettify (term_preterm xy))
                    in IH1
                    by reflexivity
                ).
                rewrite (cancel uglify' prettify) in IH1.
                simpl in IH1. unfold apply_symbol' in IH1.
                simpl in IH1. injection IH1 as IH1.
                subst xy. rewrite app_length.
                split.
                {
                    unfold to_PreTerm'.
                    simpl.
                    f_equal.
                    {
                        clear. induction lγ using rev_ind.
                        {
                            reflexivity.
                        }
                        {
                            rewrite map_app.
                            rewrite fold_left_app.
                            simpl.
                            unfold helper.
                            destruct (uglify' x); apply IHlγ.
                        }
                    }
                    {
                        f_equal.
                        apply weird_lemma.
                    }
                }
                simpl.
                split.
                {
                    rewrite IH2. reflexivity.
                }
                rewrite zip_with_app.
                rewrite Forall_app.
                split.
                {
                    apply IH3.
                }
                constructor.
                {
                    constructor.
                    apply H5.
                }
                {
                    apply Forall_nil. exact I.
                }
                {
                    symmetry. exact IH2.
                }
            }
            {
                eexists.
                split.
                {
                    simpl.
                    f_equal.
                    clear -H3.
                    fold (@helper Σ (@BuiltinOrVar Σ)) in H3.

                    revert xy1 H3.
                    induction l using rev_ind; simpl in *; intros xy1 H3.
                    {
                        inversion H3. reflexivity.
                    }
                    {

                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        destruct x, xy1; simpl in *;
                            inversion H3; subst; clear H3;
                            auto.
                    }
                }
                simpl.
                fold (@helper Σ (@BuiltinOrVar Σ)) in H3.
                assert (Hl : length l =
                    length
                    ((fix go (pt : PreTerm' symbol builtin_value) :
                        list (TermOver builtin_value) :=
                    match pt with
                    | pt_operator _ => []
                    | pt_app_operand x y => go x ++ [t_over y]
                    | pt_app_ao x y => go x ++ [prettify' y]
                    end)
                  xy1)).
                {
                    clear -H3.
                    revert xy1 H3.
                    induction l using rev_ind; intros xy1 H3.
                    {
                        simpl in *. inversion H3. reflexivity.
                    }
                    {
                        simpl.
                        rewrite app_length.
                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        unfold helper at 1 in H3. simpl in H3.
                        destruct (uglify' x) eqn:Hux.
                        {
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                inversion H3; subst; clear H3.
                                unfold satisfies in H6; simpl in H6.
                                inversion H6.
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { apply H4. }
                            }
                        }
                        {
                            simpl.
                            destruct xy1; simpl in *.
                            {
                                inversion H3.
                            }
                            {
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                { 
                                    inversion H3;
                                    assumption.
                                }
                            }
                            {
                                inversion H3; subst; clear H3.
                                rewrite app_length. simpl.
                                erewrite IHl.
                                { reflexivity. }
                                {
                                    assumption.
                                }
                            }
                        }
                    }
                }
                split.
                {
                    rewrite app_length.
                    rewrite app_length.
                    simpl.
                    f_equal.
                    apply Hl.
                }
                {
                    rewrite zip_with_app.
                    rewrite Forall_app.
                    split.
                    {
                        Print Term'.
                        specialize (IHl ((prettify (term_preterm xy1)))).
                        ltac1:(ospecialize (IHl _)).
                        {
                            unfold satisfies.
                            fold (@uglify' Σ).
                            simpl.
                            ltac1:(
                                replace (prettify' xy1)
                                with (prettify (term_preterm xy1))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            unfold to_PreTerm'. simpl.
                            unfold satisfies. simpl.
                            unfold apply_symbol'. simpl.
                            constructor.
                            apply H3.
                        }
                        destruct IHl as [lγ [Hlγ1 [Hlγ2 Hlγ3]]].
                        apply (f_equal uglify') in Hlγ1.
                        rewrite (cancel uglify' prettify) in Hlγ1.
                        simpl in Hlγ1.
                        unfold apply_symbol' in Hlγ1.
                        simpl in Hlγ1.
                        injection Hlγ1 as Hlγ1.
                        subst xy1.
                        clear -Hlγ3.
                        rewrite Forall_forall.
                        rewrite Forall_forall in Hlγ3.
                        intros x Hin.
                        rewrite elem_of_lookup_zip_with in Hin.
                        destruct Hin as [i [a [b [Hab1 [Hab2 Hab3]]]]].
                        specialize (Hlγ3 x).
                        subst x.
                        apply Hlγ3. clear Hlγ3.
                        rewrite elem_of_lookup_zip_with.
                        exists i. exists a. exists b.
                        split>[reflexivity|].
                        split>[|exact Hab3].
                        rewrite <- Hab2. clear Hab2.
                        clear.
                        assert (Htmp := @cancel_prettify_uglify Σ builtin_value).
                        unfold Cancel in Htmp. simpl in Htmp.
                        specialize (Htmp (t_term s lγ)).
                        simpl in Htmp.
                        unfold prettify' in Htmp.
                        remember ((to_PreTerm' s (map uglify' lγ))) as tpt.
                        destruct tpt; simpl in *.
                        {
                            inversion Htmp. reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                        {
                            simpl in Htmp.
                            inversion Htmp; subst; clear Htmp.
                            unfold to_PreTerm' in *.
                            fold (@prettify' Σ).
                            reflexivity.
                        }
                    }
                    {
                        constructor.
                        {
                            unfold satisfies.
                            simpl.
                            
                            ltac1:(
                                replace (prettify' xy2)
                                with (prettify (term_preterm xy2))
                                by reflexivity
                            ).
                            rewrite (cancel uglify' prettify).
                            constructor.
                            apply H5.
                        }
                        {
                            apply Forall_nil. exact I.
                        }
                    }
                    {
                        symmetry. apply Hl.
                    }
                }   
            }
        }
    }
Qed.

Lemma satisfies_PreTerm'_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : PreTerm' symbol builtin_value)
    (φ : PreTerm' symbol BuiltinOrVar)
:
    (forall (x : variable), x ∈ vars_of φ -> ρ1!!x = ρ2!!x) ->
    (
    satisfies ρ1 g φ
    <->
    satisfies ρ2 g φ
    )
.
Proof.
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ1 g φ)).
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ2 g φ)).
    revert φ.
    induction g; intros φ Hvars; destruct φ;
        unfold matchesb in *; unfold vars_of in *;
        simpl in *;
        try ltac1:(tauto).
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        destruct b0; simpl.
        {
            ltac1:(tauto).
        }
        rewrite Hvars.
        { reflexivity. }
        {
            simpl. unfold vars_of; simpl.
            ltac1:(set_solver).
        }
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        ltac1:(tauto).
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg1).
        {
            ltac1:(set_solver).
        }
        unfold matchesb; simpl.
        destruct b; simpl.
        {
            ltac1:(tauto).
        }
        rewrite Hvars.
        { reflexivity. }
        {
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
    }
    {
        do 2 (rewrite andb_true_iff).
        ltac1:(rewrite IHg1).
        { ltac1:(set_solver). }
        ltac1:(rewrite IHg2).
        { ltac1:(set_solver). }
        reflexivity.
    }
Qed.

Lemma satisfies_Term'_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : Term' symbol builtin_value)
    (φ : Term' symbol BuiltinOrVar)
:
    (forall (x : variable), x ∈ vars_of φ -> ρ1!!x = ρ2!!x) ->
    (
    satisfies ρ1 g φ
    <->
    satisfies ρ2 g φ
    )
.
Proof.
    intros Hvars.
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ1 g φ)).
    rewrite (reflect_iff _ _ (matchesb_satisfies ρ2 g φ)).
    destruct g, φ; unfold matchesb; simpl.
    {
        rewrite <- (reflect_iff _ _ (matchesb_satisfies ρ1 ao ao0)).
        rewrite <- (reflect_iff _ _ (matchesb_satisfies ρ2 ao ao0)).
        apply satisfies_PreTerm'_vars_of.
        apply Hvars.
    }
    {
        unfold matchesb; simpl.
        destruct operand; simpl.
        { ltac1:(tauto). }
        {
            rewrite Hvars.
            { reflexivity. }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                rewrite elem_of_singleton.
                reflexivity.
            }
        }
    }
    {
        ltac1:(tauto).
    }
    {
        unfold matchesb; simpl.
        destruct operand0; simpl.
        { ltac1:(tauto). }
        {
            rewrite Hvars.
            { reflexivity. }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                rewrite elem_of_singleton.
                reflexivity.
            }
        }
    }
Qed.

Lemma vars_of_uglify
    {Σ : StaticModel}
    (h : variable) a:
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
        unfold to_PreTerm'; simpl.
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

Program Fixpoint pfmap
    {A B : Type}
    (l : list A)
    (f : forall (x : A), x ∈ l -> B)
    : list B
:=
match l with
| nil => nil
| x::xs => (f x _)::(pfmap xs (fun (x' : A) (pf' : x' ∈ xs) => f x' _))
end
.
Next Obligation.
    intros. subst l. rewrite elem_of_cons. left. reflexivity.
Defined.
Next Obligation.
    intros. subst. rewrite elem_of_cons. right. exact pf'.
Defined.
Fail Next Obligation.

Lemma satisfies_subst
    {Σ : StaticModel}
    (ρ : Valuation)
    (h : variable)
    (γ : TermOver builtin_value)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of ρ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    (* h ∈ vars_of_to_l2r φ -> *)
    ~ (h ∈ vars_of_to_l2r ψ) ->
    satisfies
        ρ
        γ
        (TermOverBoV_subst φ h ψ)
        ->
    ∃ (γ0 γ1 : TermOver builtin_value),
        satisfies ρ γ1 ψ /\
        satisfies (<[h:=(uglify' γ1)]>ρ) γ0 φ
    .
Proof.
    revert γ ψ ρ.
    induction φ; intros γ ψ ρ Hhρ Hin Hnotin.
    {
        simpl.
        destruct a; simpl.
        {
            intros Hγ.
            simpl in Hin. inversion Hin.
        }
        {
            simpl in Hin.
            inversion Hin; subst; clear Hin.
            {
                rewrite filter_cons in H0.
                destruct (decide (x=x))>[|ltac1:(congruence)].
                clear e.
                intros Hψ.
                destruct (decide (h=x)).
                {
                    subst.
                    exists γ.
                    exists γ.
                    split>[assumption|].
                    apply satisfies_var.
                    ltac1:(rewrite lookup_insert).
                    reflexivity.
                }
                {
                    inversion H0.
                }
            }
        }
    }
    {
        simpl in *.
        intros HH.

        rewrite Forall_forall in H.

        destruct γ as [?|s0 l0].
        { inversion HH. }
        inversion HH; subst; clear HH.
        unfold to_PreTerm' in pf.
        rewrite <- satisfies_top_bov_cons in pf.
        destruct pf as [H1 [H2 H3]].
        subst s0.
        rewrite map_length in H1.
        rewrite Forall_forall in H2.
        ltac1:(setoid_rewrite elem_of_lookup_zip_with in H2).
        ltac1:(replace map with (@fmap _ list_fmap) in H2 by reflexivity).
        ltac1:(setoid_rewrite list_lookup_fmap in H2).
        unfold fmap in H2.
        unfold option_fmap in H2.
        unfold option_map in H2.
        assert(H2': forall i0 x0 y0,
            l0 !! i0 = Some x0 ->
            l !! i0 = Some y0 ->
            satisfies ρ x0 (TermOverBoV_subst y0 h ψ) 
        ).
        {
            intros.
            apply H2.
            exists i0. exists x0. exists (TermOverBoV_subst y0 h ψ).
            split>[reflexivity|].
            split>[apply H0|].
            rewrite H3.
            reflexivity.
        }
        clear H2.
        unfold Valuation in *.
        assert (Hm: exists m, m ∈ l /\ length (filter (eq h) (vars_of_to_l2r m)) = 1 ).
        {
            clear -Hin.
            induction l; simpl in *.
            { inversion Hin. }
            {
                rewrite filter_app in Hin.            
                rewrite app_length in Hin.
                destruct (decide (h ∈ vars_of_to_l2r a)) as [Histhere|Hisntthere].
                {
                    exists a.
                    split.
                    {
                        rewrite elem_of_cons. left. reflexivity.
                    }
                    {
                        rewrite elem_of_list_lookup in Histhere.
                        destruct Histhere as [i Hi].
                        apply take_drop_middle in Hi.
                        rewrite <- Hi. rewrite <- Hi in Hin. clear Hi.
                        rewrite filter_app. rewrite filter_cons.
                        rewrite app_length. simpl.
                        rewrite filter_app in Hin.
                        rewrite filter_cons in Hin.
                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                        rewrite app_length in Hin.
                        simpl in Hin. simpl.
                        ltac1:(lia).
                    }
                }
                {
                    assert(length (filter (eq h) (vars_of_to_l2r a)) = 0).
                    {
                        assert (h ∉ filter (eq h) (vars_of_to_l2r a)).
                        {
                            intros HContra. apply Hisntthere. clear Hisntthere.
                            rewrite elem_of_list_filter in HContra.
                            destruct HContra as [_ HContra].
                            apply HContra.
                        }
                        remember (vars_of_to_l2r a) as vs.
                        clear -H.
                        induction vs; simpl in *.
                        { reflexivity. }
                        {
                            rewrite filter_cons in H.
                            rewrite filter_cons.
                            destruct (decide (h = a)).
                            {
                                subst. rewrite elem_of_cons in H.
                                apply Decidable.not_or in H.
                                destruct H as [H _].
                                ltac1:(contradiction H).
                                reflexivity.
                            }
                            apply IHvs. apply H.
                        }
                    }
                    ltac1:(ospecialize (IHl _)).
                    {
                        ltac1:(lia).
                    }
                    destruct IHl as [m [H1m H2m]].
                    exists m.
                    split.
                    {
                        rewrite elem_of_cons. right. exact H1m.
                    }
                    {
                        exact H2m.
                    }
                }
            }
        }
        destruct Hm as [m [H1m H2m]].
        assert(Hγ1: exists γ1, satisfies ρ γ1 ψ).
        {
            specialize (H m H1m).
            rewrite elem_of_list_lookup in H1m.
            destruct H1m as [i Hi].
            specialize (H2' i).
            destruct (l0!!i) eqn:Hl0i.
            {
                specialize (H2' t m eq_refl Hi).
                specialize (H t ψ ρ Hhρ H2m Hnotin H2').
                destruct H as [γ0 [γ1 [HH1 HH2]]].
                exists γ1.
                exact HH1.
            }
            {
                apply lookup_ge_None_1 in Hl0i.
                apply lookup_lt_Some in Hi.
                ltac1:(lia).
            }
        }
        destruct Hγ1 as [γ1 H1γ1].
        assert(H': ∀ (i0 : nat)
            (x0 : TermOver builtin_value)
            (y0 : TermOver BuiltinOrVar),
            l0!!i0 = Some x0 ->
            l!!i0 = Some y0 ->
            ∃ (γ1 γ0 : TermOver builtin_value),
            satisfies (<[h := uglify' γ1]>ρ) γ0 y0
        ).
        {
            intros i0 x0 y0 Hx0 Hy0.
            clear m H1m H2m.
            destruct (decide (length (filter (eq h) (vars_of_to_l2r y0) ) = 1)) as [?|Hno1].
            {
                specialize (H2' i0 x0 y0 Hx0 Hy0).
                specialize (H y0).
                ltac1:(ospecialize (H _)).
                {
                    rewrite elem_of_list_lookup.
                    exists i0. assumption.
                }
                specialize (H x0 ψ ρ Hhρ ltac:(assumption)).
                specialize (H Hnotin H2').
                destruct H as [γ0 [γ2 [HH1 HH2]]].
                exists γ2.
                exists γ0.
                exact HH2.
            }
            {
                assert (Hzero: length (filter (eq h) (vars_of_to_l2r y0)) = 0).
                {
                    apply take_drop_middle in Hy0.
                    rewrite <- Hy0 in Hin.
                    rewrite map_app in Hin.
                    rewrite concat_app in Hin.
                    rewrite filter_app in Hin.
                    rewrite app_length in Hin.
                    simpl in Hin.
                    rewrite filter_app in Hin.
                    rewrite app_length in Hin.
                    ltac1:(lia).
                }
                clear Hno1.
                specialize (H2' i0 x0 y0 Hx0 Hy0).
                rewrite subst_notin in H2'.
                {
                    exists x0.
                    exists x0.
                    unfold satisfies; simpl.
                    erewrite satisfies_Term'_vars_of.
                    { 
                        unfold satisfies in H2'. simpl in H2'.
                        apply H2'.
                    }
                    {
                        intros x Hx.
                        destruct (decide (h = x)).
                        {
                            subst.
                            ltac1:(exfalso).
                            clear - Hzero Hx.
                            rewrite <- vars_of_uglify in Hx.
                            ltac1:(rewrite elem_of_list_lookup in Hx).
                            destruct Hx as [i Hi].
                            apply take_drop_middle in Hi.
                            rewrite <- Hi in Hzero.
                            rewrite filter_app in Hzero.
                            simpl in Hzero.
                            rewrite filter_cons in Hzero.
                            destruct (decide (x=x))>[|ltac1:(contradiction)].
                            rewrite app_length in Hzero.
                            simpl in Hzero.
                            ltac1:(lia).
                        }
                        {
                            ltac1:(rewrite lookup_insert_ne).
                            { assumption. }
                            reflexivity.
                        }
                    }
                }
                {
                    clear -Hzero.
                    intros HContra.
                    rewrite elem_of_list_lookup in HContra.
                    destruct HContra as [i Hi].
                    apply take_drop_middle in Hi.
                    rewrite <- Hi in Hzero. clear Hi.
                    rewrite filter_app in Hzero.
                    rewrite filter_cons in Hzero.
                    (destruct (decide (h=h)) as [_|?])>[|ltac1:(contradiction)].
                    rewrite app_length in Hzero.
                    simpl in Hzero.
                    ltac1:(lia).
                }
            }
        }
        clear H H2'.
        (* I think I have to assume that [h] occurs exactly once
        in ϕ. Then it should work.*)

        remember (fun (i:nat) => i) as G.


        ltac1:(unshelve(eremember (fun x' (pfx'l0 : x' ∈ l0) =>
            let pfx'l0' := proj1 (elem_of_list_lookup l0 x') pfx'l0 in 
            match pfx'l0' with
            | ex_intro _ i pfi =>
                (* let y' := (TermOverBoV_subst x' h ψ) in *)
                match (decide (h ∈ vars_of_to_l2r x')) with
                | left pf1 =>
                    H x' pfx'l (t_term s l0) ψ ρ Hhρ pf1 Hnotin
                    (H2
                        (satisfies ρ x' y')
                        (@ex_intro _ _ i 
                            (@ex_intro _ _ x' (
                                @ex_intro _ _ y'
                                (conj (eq_refl) (conj (pfi) (_)))
                            ))
                        )
                    )
                | right _ => True
                end
            end
            ) as F
        )).
        remember (pfmap l0 F) as l0'.
        eexists (t_term s ?[l]).


        revert h γ ψ Hnotin H Hhρ Hin.
        induction l; intros h γ ψ Hnotin H Hhρ Hin; simpl; intros HH.
        {
            simpl in *. inversion Hin.
        }
        {
            simpl in *.
            rewrite elem_of_app in Hin.
            apply satisfies_term_inv in HH.
            destruct HH as [lγ [HH1 [HH2 HH3]]].
            subst γ. simpl in *.
            destruct lγ; simpl in HH2.
            {
                inversion HH2.
            }
            simpl in HH3.
            rewrite Forall_cons in HH3.
            destruct HH3 as [HH3 HH4].
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            destruct (decide (h ∈ vars_of_to_l2r a)) as [HHin|HHnotin].
            {
                assert (H1' := H1).
                specialize (H1 t ψ ρ Hhρ HHin Hnotin HH3).
                destruct H1 as [γ1 [γ2 [Hg1 Hg2]]].
                specialize (IHl h t ψ Hnotin H2 Hhρ).

                destruct a; simpl in *.
                {
                    destruct a.
                    {
                        inversion HHin.
                    }
                    {
                        destruct (decide (h = x)).
                        {
                            subst. simpl in *.
                            clear Hin. clear HHin.
                            destruct γ1.
                            {
                                inversion Hg2; subst; clear Hg2.
                                eexists (t_term s (locked ((t)::?[sl]))).
                                exists t.
                                split>[assumption|].
                                unfold satisfies; simpl.
                                unfold apply_symbol'. unfold to_Term'.
                                constructor.
                                unfold to_PreTerm'.
                                ltac1:(
                                    replace (term_operand (bov_variable x) :: map uglify' l)
                                    with (map uglify' ((t_over (bov_variable x))::l))
                                    by reflexivity
                                ).
                                rewrite <- satisfies_top_bov_cons.
                                split.
                                {

                                }
                                split>[|reflexivity].
                                rewrite <- lock.
                                simpl.
                                rewrite Forall_cons.
                                split.
                                {
                                    unfold satisfies; simpl.
                                    unfold satisfies; simpl.
                                    destruct t; simpl; constructor.
                                    {
                                        constructor.
                                        ltac1:(rewrite lookup_insert).
                                        reflexivity.
                                    }
                                    {
                                        unfold satisfies; simpl.
                                        ltac1:(rewrite lookup_insert).
                                        reflexivity.
                                    }
                                }
                                {

                                }
                            }

                            ltac1:(ospecialize (IHl _)).
                                {
                                    ltac1:(tauto).
                                }
                                ltac1:(ospecialize (IHl _)).
                                {
                                    clear IHl.

                                }
                                exists (t_term s (γ1::lγ)).
                                exists γ2.
                        }
                        {

                        }
                    }
                }
                {
                    destruct t.
                    {
                        inversion HH3.
                    }
                    {
                        inversion HH3; subst; clear HH3.
                    }
                }

                destruct (decide (h ∈ vars_of_to_l2r a)) as [Hha|Hha].
                {

                }
                {
                    ltac1:(ospecialize (IHl _)).
                    {
                        ltac1:(tauto).
                    }
                    ltac1:(ospecialize (IHl _)).
                    {
                        clear IHl.

                    }
                    exists (t_term s (γ1::lγ)).
                    exists γ2.
                    split.
                    { assumption. }
                    unfold satisfies; simpl.
                    unfold apply_symbol'.
                    unfold to_Term'.
                    constructor.
                    unfold to_PreTerm'.
                    ltac1:(
                        replace (uglify' γ1 :: map uglify' lγ)
                        with (map uglify' (γ1::lγ))
                        by reflexivity
                    ).
                    ltac1:(
                        replace (uglify' a :: map uglify' l)
                        with (map uglify' (a::l))
                        by reflexivity
                    ).
                    rewrite <- satisfies_top_bov_cons.
                    rewrite map_length in HH2.
                    split.
                    {
                        simpl.
                        ltac1:(lia).
                    }
                    split>[|reflexivity].
                    simpl.
                    rewrite Forall_cons.
                    split>[assumption|].
                    
                    rewrite vars_of_uglify in Hha.
                    unfold satisfies; simpl.
                    ltac1:(replace map with (@fmap _ list_fmap) in HH4 by reflexivity).
                    rewrite zip_with_fmap_r in HH4.
                    About satisfies_Term'_vars_of.
                    Search satisfies vars_of.
                    exact HH4.
                    Search zip_with fmap.
                }

                
                exists (t_term s (γ1::lγ)).
                exists γ2.
                split.
                { assumption. }
                unfold satisfies; simpl.
                unfold apply_symbol'.
                unfold to_Term'.
                constructor.
                unfold to_PreTerm'.
                ltac1:(
                    replace (uglify' γ1 :: map uglify' lγ)
                    with (map uglify' (γ1::lγ))
                    by reflexivity
                ).
                ltac1:(
                    replace (uglify' a :: map uglify' l)
                    with (map uglify' (a::l))
                    by reflexivity
                ).
                rewrite <- satisfies_top_bov_cons.
                rewrite map_length in HH2.
                split.
                {
                    simpl.
                    ltac1:(lia).
                }
                split>[|reflexivity].
                simpl.
                rewrite Forall_cons.
                split>[assumption|].
                

                (*
                clear H'1.
                specialize (H1' t ψ ρ Hhρ HHin Hnotin HH3).
                destruct H1' as [γ0 [γ3 [H'1 H'2]]].
                *)
                rewrite Forall_forall in H2.
                rewrite Forall_forall.
                intros P HP.
                ltac1:(apply elem_of_lookup_zip_with in HP).
                destruct HP as [i [x [y [HP1 [HP2 HP3]]]]].
                rewrite Forall_forall in HH4.
                ltac1:(setoid_rewrite elem_of_lookup_zip_with in HH4).
                subst P.
                specialize (IHl h).

                destruct (decide (h ∈ vars_of_to_l2r y)) as [Hhy|Hhy].
                {

                }
                {
                    rewrite vars_of_uglify in Hhy.
                    unfold satisfies; simpl.
                    rewrite satisfies_Term'_vars_of with (ρ2 := ρ).
                    {
                        apply HH4.
                        exists i,x,y.
                        split>[reflexivity|].
                        split>[apply HP2|].
                        rewrite <- HP3.
                        ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                        rewrite list_lookup_fmap.
                        rewrite HP3.
                        simpl.
                        f_equal.
                        rewrite subst_notin.
                        { reflexivity. }
                        rewrite <- vars_of_uglify in Hhy.
                        apply Hhy.
                    }
                    {
                        intros.
                        destruct (decide (x0 = h)).
                        {
                            subst.
                            ltac1:(contradiction Hhy).
                        }
                        {
                            ltac1:(rewrite lookup_insert_ne).
                            { symmetry. assumption. }
                            reflexivity.
                        }
                    }
                }
            }
            {
                rewrite subst_notin in HH3>[|assumption].
                assert (( h ∈ concat (map vars_of_to_l2r l))) by (ltac1:(tauto)).
                specialize (IHl h (t_term s lγ) ψ Hnotin H2 Hhρ H).
                ltac1:(ospecialize (IHl _)).
                {
                    unfold satisfies. simpl.
                    ltac1:(
                        replace ((uglify' t :: map uglify' lγ))
                        with (map uglify' (t::lγ))
                        by reflexivity
                    ).
                    unfold apply_symbol'; simpl.
                    constructor.
                    apply satisfies_top_bov_cons.
                    {
                        simpl.
                        rewrite map_length.
                        rewrite map_length in HH2.
                        split>[ltac1:(lia)|].
                        split>[|reflexivity].
                        apply HH4.
                    }
                }
                destruct IHl as [γ0 [γ1 [H'1 H'2]]].
                destruct γ0.
                {
                    inversion H'2.
                }

                exists (t_term s0 (t::l0)).
                exists γ1.
                split>[assumption|].
                inversion H'2; subst; clear H'2.
                constructor.
                fold (@uglify' Σ).
                unfold to_PreTerm' in *; simpl in *|-.
                rewrite <- satisfies_top_bov_cons in pf.
                destruct pf as [Hlen [pf ?]].
                subst s0.
                rewrite <- satisfies_top_bov_cons.
                {
                    simpl.
                    split>[ltac1:(lia)|].
                    split>[|reflexivity].
                    simpl. rewrite Forall_cons.
                    split>[|apply pf].
                    unfold satisfies; simpl.
                    unfold satisfies in HH3; simpl in HH3.

                    rewrite satisfies_Term'_vars_of.
                    { apply HH3. }
                    {
                        intros x Hx.
                        destruct (decide (x = h)) as [?|Hxh].
                        {
                            subst.
                            rewrite <- vars_of_uglify in Hx.
                            clear - Hx HHnotin.
                            ltac1:(exfalso; contradiction HHnotin).
                        }
                        {
                            ltac1:(rewrite lookup_insert_ne).
                            { symmetry. exact Hxh. }
                            reflexivity.
                        }
                    }
                }
            }
        }
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
            (* I shouldn't specialize it with ctrl1.
            It should be: cSeq[ctrl1 with holeSymbol instead of ??;] 
            *)
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
                    ltac1:(rewrite <- (firstn_skipn i ds) in Hi).
                    rewrite <- Heqdids in Hi.
                    rewrite lookup_app_r in Hi>[|rewrite take_length; ltac1:(lia)].
                    ltac1:(
                        replace (i - length (take i ds)) with (0)
                        in Hi
                        by (rewrite take_length; lia)
                    ).
                    simpl in Hi. inversion Hi; subst; clear Hi.

                    exists ρ.
                    unfold flattened_rewrites_in_valuation_under_to.
                    simpl.
                    split.
                    {
                        clear Htmp'.
                        ltac1:(
                            replace ((term_operand (bov_variable (fresh (fresh (vars_of_to_l2r c) :: vars_of_to_l2r c)))))
                            with (uglify' (t_over ((bov_variable (fresh (fresh (vars_of_to_l2r c) :: vars_of_to_l2r c))))))
                            by reflexivity
                        ).
                        ltac1:(
                            replace (apply_symbol' cseqSymbol [uglify' c; term_operand (bov_variable (fresh (vars_of_to_l2r c)))])
                            with (uglify' (t_term cseqSymbol [c; t_over (bov_variable (fresh (vars_of_to_l2r c)))]))
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
    }

Qed.