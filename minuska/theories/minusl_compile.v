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

Lemma satisfies_subst
    {Σ : StaticModel}
    (ρ : Valuation)
    (h : variable)
    (γ : TermOver builtin_value)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∈ vars_of_to_l2r φ ->
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
    induction φ; intros γ ψ ρ Hin Hnotin.
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
                destruct (decide (x=x))>[|ltac1:(congruence)].
                clear e.
                intros Hψ.
                exists γ.
                exists γ.
                split>[assumption|].
                apply satisfies_var.
                ltac1:(rewrite lookup_insert).
                reflexivity.
            }
            {
                rewrite elem_of_nil in H1. inversion H1.
            }
        }
    }
    {
        simpl in *.
        induction l; simpl; intros HH.
        {
            simpl in *. inversion Hin.
        }
        {
            simpl in *.
            rewrite elem_of_app in Hin.
            destruct (decide ( h ∈ concat (map vars_of_to_l2r l))) as [Hholds|Hnothold].
            {
                clear Hin.
            }
            {
                assert (Hin': h ∈ vars_of_to_l2r a) by (ltac1:(tauto)).
                clear Hin.
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
    {

    }

Qed.