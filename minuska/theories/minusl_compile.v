From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    semantics_properties
    basic_matching
    varsof
.

Require Import Ring.
Require Import ArithRing.
Require Import Coq.Logic.FunctionalExtensionality.

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

About list_find.

Fixpoint factor_by_subst
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation)
    (h : variable)
    (γ : TermOver builtin_value)
    (φ ψ : TermOver BuiltinOrVar)
    : ((TermOver builtin_value)*(TermOver builtin_value))
:=
match sz with
| 0 => (γ, γ)
| S sz' =>
    if matchesb ρ (uglify' γ) (uglify' ψ) then (γ, γ) else
    match γ,φ with
    | t_over _, t_over _ => (* do not care*) (γ, γ)
    | t_term _ _, t_over _ => (* do not care*) (γ, γ)
    | t_over _, t_term _ _ => (* do not care*) (γ, γ)
    | t_term _ lγ, t_term s lφ =>
        match list_find (fun φi => h ∈ vars_of_to_l2r φi) lφ with
        | None => (* do not care*) (γ, γ)
        | Some (i, φi) => 
            match lγ !! i with 
            | None => (* do not care*) (γ, γ)
            | Some γi =>
                let xy := factor_by_subst sz' ρ h γi φi ψ in
                (t_term s (<[i := xy.1]>lγ), xy.2)

            end
        end
    end
end
.

Lemma length_filter_l_1_impl_h_in_l
    {Σ : StaticModel}
    (l : list variable)
    (h : variable):
    length (filter (eq h) l) = 1 ->
    h ∈ l
.
Proof.
    intros H.
    induction l; simpl in *.
    { inversion H. }
    {
        rewrite filter_cons in H.
        destruct (decide (h = a)).
        {
            subst. left.
        }
        {
            right. apply IHl. apply H.
        }
    }
Qed.

Lemma size_subst_1
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    TermOver_size φ <= TermOver_size (TermOverBoV_subst φ h ψ)
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        { ltac1:(lia). }
        {
            destruct (decide (h = x)); simpl.
            {
                destruct ψ; simpl; ltac1:(lia).
            }
            {
                ltac1:(lia).
            }
        }
    }
    {
        revert H.
        induction l; intros H; simpl in *.
        { ltac1:(lia). }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            ltac1:(lia).
        }
    }
Qed.

Lemma size_subst_2
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∈ vars_of_to_l2r φ ->
    TermOver_size ψ <= TermOver_size (TermOverBoV_subst φ h ψ)
.
Proof.
    revert h ψ.
    induction φ; intros h ψ Hin; simpl in *.
    {
        destruct a.
        {
            inversion Hin.
        }
        {
            inversion Hin; subst; clear Hin.
            {
                destruct (decide (x = x))>[|ltac1:(contradiction)].
                ltac1:(lia).
            }
            {
                inversion H1.
            }
        }
    }
    {
        revert H Hin.
        induction l; intros H Hin; simpl in *.
        {
            inversion Hin.
        }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2). clear H2.
            destruct (decide (h ∈ vars_of_to_l2r a )) as [Hin'|Hnotin'].
            {
                specialize (H1 h ψ Hin'). clear Hin.
                ltac1:(lia).
            }
            {
                specialize (IHl ltac:(set_solver)).
                ltac1:(lia).
            }
        }
    }
Qed.

Lemma to_preterm_is_pt_operator_inv
    {Σ : StaticModel}
    {T : Type}
    (s s' : symbol)
    (l : list (Term' symbol T)):
    pt_operator s' = to_PreTerm' s l ->
    s' = s /\ l = []
.
Proof.
    revert s s'.
    destruct l using rev_ind; intros s s' H1.
    {
        inversion H1. subst. split; reflexivity.
    }
    {
        unfold to_PreTerm' in H1.
        rewrite fold_left_app in H1. simpl in H1.
        unfold helper in H1; simpl in H1.
        destruct x.
        {
            inversion H1.
        }
        {
            inversion H1.
        }
    }
Qed.

Lemma satisfies_TermOverBuiltin_to_TermOverBoV
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    :
    satisfies ρ γ (TermOverBuiltin_to_TermOverBoV γ)
.
Proof.
    unfold satisfies; simpl.
    induction γ; constructor.
    {
        constructor.
    }
    {
        fold (@uglify' Σ).
        fold (@TermOver_map Σ).
        unfold to_PreTerm'.
        rewrite <- satisfies_top_bov_cons.
        (repeat split).
        {
            rewrite map_length. reflexivity.
        }
        induction l; simpl.
        { apply Forall_nil. exact I. }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2).
            rewrite Forall_cons.
            split.
            {
                apply H1.
            }
            apply IHl.
        }
    }
Qed.

Lemma satisfies_builtin_inv {Σ : StaticModel} (ρ : Valuation) l s b:
    satisfies ρ (fold_left helper l (pt_operator s)) (bov_builtin b) ->
    False
.
Proof.
    destruct l using rev_ind; simpl; intros HH.
    {
        inversion HH.
    }
    {
        rewrite fold_left_app in HH. simpl in HH.
        inversion HH.
    }
Qed.

Lemma to_preterm_eq_inv
    {Σ : StaticModel}
    {T : Type}
    (s1 s2 : symbol)
    (l1 l2 : list (Term' symbol T))
    :
    to_PreTerm' s1 l1 = to_PreTerm' s2 l2
    -> s1 = s2 /\ l1 = l2
.
Proof.
    revert l2.
    induction l1 using rev_ind; intros l2 HH; destruct l2 using rev_ind.
    {
        inversion HH. subst. repeat split.
    }
    {
        unfold to_PreTerm' in *.
        rewrite fold_left_app in HH. simpl in HH.
        destruct l2 using rev_ind.
        {
            simpl in HH. unfold helper in HH.
            destruct x.
            {
                inversion HH.
            }
            {
                inversion HH.
            }
        }
        {
            rewrite fold_left_app in HH. simpl in HH.
            unfold helper in HH.
            destruct x; inversion HH.
        }
    }
    {
        unfold to_PreTerm' in *.
        rewrite fold_left_app in HH. simpl in HH.
        destruct l1 using rev_ind.
        {
            simpl in HH. unfold helper in HH.
            destruct x.
            {
                inversion HH.
            }
            {
                inversion HH.
            }
        }
        {
            rewrite fold_left_app in HH. simpl in HH.
            unfold helper in HH.
            destruct x; inversion HH.
        }
    }
    {
        unfold to_PreTerm' in *.
        rewrite fold_left_app in HH.
        rewrite fold_left_app in HH.
        simpl in HH.
        unfold helper in HH.
        destruct x,x0; simpl in *; inversion HH; subst; clear HH.
        {
            simpl in *.
            specialize (IHl1 l2 H0). clear H0.
            destruct IHl1 as [IH1 IH2].
            subst.
            split>[reflexivity|].
            reflexivity.
        }
        {
            simpl in *.
            specialize (IHl1 l2 H0). clear H0.
            destruct IHl1 as [IH1 IH2].
            subst.
            split>[reflexivity|].
            reflexivity.
        }
    }
Qed.

Lemma map_uglify'_inj
    {Σ : StaticModel}
    {T : Type}
    (l1 l2 : list (TermOver T))
    :
    map uglify' l1 = map uglify' l2 ->
    l1 = l2
.
Proof.
    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
    intros H.
    apply list_fmap_eq_inj in H.
    exact H.
    apply cancel_inj.
Qed.

Lemma forall_satisfies_inv'
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation)
    (γ1 γ2 : list (TermOver builtin_value))
    (l : list (TermOver BuiltinOrVar))
    :
    sum_list_with (S ∘ TermOver_size) l < sz ->
    length γ1 = length l ->
    length γ2 = length l ->
    Forall id (zip_with (satisfies ρ) γ1 l) ->
    Forall id (zip_with (satisfies ρ) γ2 l) ->
    γ1 = γ2
with satisfies_inv'
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation)
    (x y : TermOver builtin_value)
    (z : TermOver BuiltinOrVar)
    :
    TermOver_size z < sz ->
    satisfies ρ x z ->
    satisfies ρ y z ->
    x = y
.
Proof.
    {
        intros Hsz H1 H2 H3.
        destruct sz.
        {
            ltac1:(lia).
        }
        rewrite Forall_forall.
        rewrite Forall_forall in H3.
        intros H4.
        ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
        ltac1:(setoid_rewrite elem_of_lookup_zip_with in H4).
        apply list_eq.
        intros i.
        destruct
            (γ1 !! i) eqn:Hγ1i,
            (γ2 !! i) eqn:Hγ2i.
        {
            destruct (l !! i) eqn:Hli.
            {
                specialize (H3 (satisfies ρ t t1)).
                ltac1:(ospecialize (H3 _)).
                {
                    exists i,t,t1.
                    split>[reflexivity|].
                    split;assumption.
                }
                specialize (H4 (satisfies ρ t0 t1)).
                ltac1:(ospecialize (H4 _)).
                {
                    exists i,t0,t1.
                    split>[reflexivity|].
                    split;assumption.
                }
                clear -H3 H4 satisfies_inv' sz Hsz Hli.
                f_equal.
                specialize (satisfies_inv' Σ sz ρ t t0 t1).
                apply satisfies_inv'; try assumption.
                apply take_drop_middle in Hli.
                rewrite <- Hli in Hsz.

                rewrite sum_list_with_app in Hsz.
                simpl in Hsz.
                ltac1:(lia).
            }
            {
                apply lookup_lt_Some in Hγ1i.
                apply lookup_ge_None in Hli.
                ltac1:(lia).
            }
        }
        {
            apply lookup_lt_Some in Hγ1i.
            apply lookup_ge_None in Hγ2i.
            ltac1:(lia).
        }
        {
            apply lookup_lt_Some in Hγ2i.
            apply lookup_ge_None in Hγ1i.
            ltac1:(lia).
        }
        {
            reflexivity.
        }
    }
    {
        intros Hsz H1 H2.

        destruct sz.
        {
            ltac1:(lia).
        }

        destruct
            x as [ax|cx lx],
            y as [ay|cy ly],
            z as [az|cz lz]
            .
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            inversion pf; subst; clear pf;
            inversion pf0; subst; clear pf0;
            try reflexivity.
            ltac1:(simplify_eq /=).
            reflexivity.
        }
        {
            inversion H1.
        }
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            destruct az.
            {
                inversion pf; subst; clear pf.
                unfold to_PreTerm' in H3.
                apply satisfies_builtin_inv in H3.
                inversion H3.
            }
            {
                inversion pf; subst; clear pf.
                inversion H3; subst; clear H3.
                ltac1:(simplify_eq /=).
            }
        }
        {
            inversion H1.
        }
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            destruct az.
            {
                inversion pf; subst; clear pf.
                unfold to_PreTerm' in H4.
                apply satisfies_builtin_inv in H4.
                inversion H4.
            }
            {
                inversion pf; subst; clear pf.
                inversion H4; subst; clear H4.
                ltac1:(simplify_eq /=).
            }
        }
        {
            inversion H2.
        }
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            destruct az.
            {
                apply satisfies_builtin_inv in H3.
                inversion H3.
            }
            {
                inversion H4; subst; clear H4.
                inversion H3; subst; clear H3.
                ltac1:(simplify_eq /=).
                apply to_preterm_eq_inv in H.
                destruct H as [H1 H2].
                subst cy.
                apply map_uglify'_inj in H2.
                subst ly.
                reflexivity.
            }
        }
        {
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2.
            unfold to_PreTerm' in pf.
            unfold to_PreTerm' in pf0.
            rewrite <- satisfies_top_bov_cons in pf.
            rewrite <- satisfies_top_bov_cons in pf0.
            destruct pf as [H1 H2].
            destruct pf0 as [H3 H4].
            assert (IH1 := forall_satisfies_inv' Σ sz ρ lx ly lz).
            destruct H2 as [H21 H22].
            destruct H4 as [H41 H42].
            simpl in Hsz.
            specialize (IH1 ltac:(lia)).
            subst.
            specialize (IH1 H1 H3 H21 H41).
            subst.
            reflexivity.
        }
    }
Qed.

Lemma forall_satisfies_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ1 γ2 : list (TermOver builtin_value))
    (l : list (TermOver BuiltinOrVar))
    :
    length γ1 = length l ->
    length γ2 = length l ->
    Forall id (zip_with (satisfies ρ) γ1 l) ->
    Forall id (zip_with (satisfies ρ) γ2 l) ->
    γ1 = γ2
.
Proof.
    intros.
    eapply forall_satisfies_inv' with (l := l)(ρ := ρ) (sz := S (sum_list_with (S ∘ TermOver_size) l));
        try assumption.
    ltac1:(lia).
Qed.

Lemma satisfies_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    (x y : TermOver builtin_value)
    (z : TermOver BuiltinOrVar)
    :
    satisfies ρ x z ->
    satisfies ρ y z ->
    x = y
.
Proof.
    intros.
    apply satisfies_inv' with (ρ := ρ) (z := z) (sz := S (TermOver_size z));
        try assumption.
    ltac1:(lia).
Qed.


Lemma satisfies_in_size
    {Σ : StaticModel}
    (ρ : Valuation)
    (x : variable)
    (t t' : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    x ∈ vars_of (uglify' φ) ->
    ρ !! x = Some (uglify' t') ->
    satisfies ρ t φ ->
    TermOver_size t' <= TermOver_size t
.
Proof.
    revert t.
    induction φ; intros t Hin Hsome Hsat.
    {
        destruct a.
        {
            inversion Hsat; subst; clear Hsat.
            {
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                simpl in *.
                unfold vars_of in Hin; simpl in Hin.
                unfold vars_of in Hin; simpl in Hin.
                clear -Hin.
                ltac1:(exfalso).
                ltac1:(set_solver).
            }
            {
                unfold vars_of in Hin; simpl in Hin.
                unfold vars_of in Hin; simpl in Hin.
                clear -Hin.
                ltac1:(exfalso).
                ltac1:(set_solver).
            }
        }
        {
            unfold vars_of in Hin; simpl in Hin.
            unfold vars_of in Hin; simpl in Hin.
            rewrite elem_of_singleton in Hin. subst x0.
            inversion Hsat; subst; clear Hsat.
            {
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                simpl in *.
                inversion pf; subst; clear pf.
                rewrite H1 in Hsome. inversion Hsome; subst; clear Hsome.
                apply (f_equal prettify) in H0.
                rewrite (cancel prettify uglify') in H0.
                subst t'.
                simpl.
                ltac1:(lia).
            }
            {
                apply (f_equal prettify) in H.
                rewrite (cancel prettify uglify') in H.
                subst t.
                simpl in *.
                inversion H2; subst; clear H2.
                rewrite H0 in Hsome. inversion Hsome; subst; clear Hsome.
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t'.
                simpl.
                ltac1:(lia).
            }
        }
    }
    {
        apply satisfies_term_inv in Hsat.
        destruct Hsat as [lγ [H1 [H2 H3]]].
        subst.
        simpl.
        rewrite <- vars_of_uglify in Hin.
        simpl in Hin.
        rewrite elem_of_list_In in Hin.
        rewrite in_concat in Hin.
        destruct Hin as [x0 [H1x0 H2x0]].
        rewrite <- elem_of_list_In in H1x0.
        rewrite <- elem_of_list_In in H2x0.
        ltac1:(replace map with (@fmap _ list_fmap) in H1x0 by reflexivity).
        ltac1:(rewrite elem_of_list_lookup in H1x0).
        destruct H1x0 as [i Hi].
        rewrite list_lookup_fmap in Hi.
        destruct (l !! i) eqn:Hli.
        {
            simpl in Hi. inversion Hi; subst; clear Hi.
            rewrite Forall_forall in H.
            specialize (H t).
            ltac1:(ospecialize (H _)).
            {
                rewrite elem_of_list_lookup.
                exists i. exact Hli.
            }
            rewrite Forall_forall in H3.
            ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
            destruct (lγ !! i) eqn:Hlγi.
            {
                specialize (H3 (satisfies ρ t0 t)).            
                ltac1:(ospecialize (H3 _)).
                {
                    exists i, t0, t.
                    split>[reflexivity|].
                    split;assumption.
                }
                specialize (H t0).
                rewrite <- vars_of_uglify in H.
                specialize (H H2x0 Hsome H3).
                apply take_drop_middle in Hlγi.
                rewrite <- Hlγi.
                rewrite sum_list_with_app.
                simpl.
                ltac1:(lia).
            }
            {
                apply lookup_ge_None_1 in Hlγi.
                apply lookup_lt_Some in Hli.
                ltac1:(lia).
            }
        }
        {
            simpl in Hi. inversion Hi.
        }
    }
Qed.

Lemma double_satisfies_contradiction
    {Σ : StaticModel}
    (ρ : Valuation)
    ay cz lz cx lx
    :
    vars_of (uglify' (t_over ay)) = vars_of (uglify' (t_term cz lz)) ->
    satisfies ρ (t_term cx lx) (t_over ay) ->
    satisfies ρ (t_term cx lx) (t_term cz lz) ->
    False
.
Proof.
    intros Hvars H1 H2.
        inversion H1; subst; clear H1.
        inversion H2; subst; clear H2.
        unfold to_PreTerm' in pf.
        rewrite <- satisfies_top_bov_cons in pf.
        destruct pf as [pf1 [pf2 pf3]].
        subst cz.
        destruct ay.
        {
            inversion H4; subst; clear H4.
        }
        {
            
            ltac1:(exfalso).
            simpl in Hvars.
            assert (Htmp1 := satisfies_in_size ρ x).
            unfold vars_of in Hvars; simpl in Hvars.
            unfold vars_of in Hvars; simpl in Hvars.

            inversion H4; subst; clear H4.
            assert (∃ z, z ∈ map uglify' lz /\ x ∈ (vars_of z)).
            {
                clear -Hvars.
                revert Hvars.
                induction lz using rev_ind; intros Hvars.
                {
                    simpl in Hvars. ltac1:(set_solver).
                }
                {
                    rewrite map_app in Hvars.
                    unfold to_PreTerm' in Hvars.
                    rewrite fold_left_app in Hvars.
                    simpl in Hvars.
                    unfold helper in Hvars.
                    destruct (uglify' x0) eqn:Hux0.
                    {
                        simpl in Hvars.
                        destruct (decide (x ∈ vars_of ao)).
                        {
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0.
                            exists (term_preterm ao).
                            rewrite map_app.
                            split.
                            {
                                rewrite elem_of_app.
                                right. ltac1:(rewrite /map).
                                rewrite (cancel uglify' prettify).
                                clear. constructor.
                            }
                            {
                                unfold vars_of; simpl. assumption.
                            }
                        }
                        {
                            specialize (IHlz ltac:(set_solver)).
                            destruct IHlz as [z [H1z H2z]].
                            exists z.
                            split.
                            {
                                rewrite map_app.
                                rewrite elem_of_app.
                                left. assumption.
                            }
                            {
                                assumption.
                            }
                    }
                }
                {
                    simpl in Hvars.
                    destruct (decide (x ∈ vars_of operand)).
                    {
                        apply (f_equal prettify) in Hux0.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x0.
                        exists (term_operand operand).
                        rewrite map_app.
                        split.
                        {
                            rewrite elem_of_app.
                            right. ltac1:(rewrite /map).
                            rewrite (cancel uglify' prettify).
                            clear. constructor.
                        }
                        {
                            unfold vars_of; simpl. assumption.
                        }
                    }
                    {
                        specialize (IHlz ltac:(set_solver)).
                        destruct IHlz as [z [H1z H2z]].
                        exists z.
                        split.
                        {
                            rewrite map_app.
                            rewrite elem_of_app.
                            left. assumption.
                        }
                        {
                            assumption.
                        }
                    }
                }
            }
        }
        {
            destruct H as [z [H1z H2z]].
            ltac1:(replace map with (@fmap _ list_fmap) in H1z by reflexivity).
            rewrite elem_of_list_lookup in H1z.
            destruct H1z as [i Hi].
            rewrite list_lookup_fmap in Hi.
            destruct (lz !! i) eqn:Hlzi.
            {
                inversion Hi; subst; clear Hi.
                rewrite Forall_forall in pf2.
                ltac1:(setoid_rewrite elem_of_lookup_zip_with in pf2).

                destruct (lx !! i) eqn:Hlxi.
                {
                    specialize (pf2 (satisfies ρ t0 t)).
                    ltac1:(ospecialize (pf2 _)).
                    {
                        exists i.
                        exists t0.
                        exists t.
                        split>[reflexivity|].
                        split; assumption.
                    }
                    specialize (Htmp1 t0 (t_term cx lx)).
                    specialize (Htmp1 t H2z H0 pf2).
                    simpl in Htmp1.
                    clear - Htmp1 Hlxi.
                    apply take_drop_middle in Hlxi.
                    rewrite <- Hlxi in Htmp1.
                    rewrite sum_list_with_app in Htmp1.
                    simpl in Htmp1.
                    ltac1:(lia).
                }
                {
                    apply lookup_ge_None_1 in Hlxi.
                    apply lookup_lt_Some in Hlzi.
                    ltac1:(lia).
                }
            }
            {
                inversion Hi.
            }
        }
    }
Qed.

Lemma double_satisfies_contradiction_weaker
    {Σ : StaticModel}
    (ρ : Valuation)
    ay cz lz cx lx
    :
    vars_of_to_l2r ((t_over ay)) = vars_of_to_l2r ((t_term cz lz)) ->
    satisfies ρ (t_term cx lx) (t_over ay) ->
    satisfies ρ (t_term cx lx) (t_term cz lz) ->
    False
.
Proof.
    intros.
    eapply double_satisfies_contradiction>[|apply H0|apply H1].
    apply set_eq.
    intros x.
    rewrite <- vars_of_uglify.
    rewrite <- vars_of_uglify.
    rewrite H.
    ltac1:(tauto).
Qed.

Lemma vars_of_apply_symbol
    {Σ : StaticModel}
    (s : symbol)
    (l : list (Term' symbol BuiltinOrVar))
    :
    vars_of (apply_symbol' s l) = union_list (fmap vars_of l)
.
Proof.
    induction l using rev_ind.
    {
        simpl. reflexivity.
    }
    {
        rewrite fmap_app.
        rewrite union_list_app_L.
        unfold apply_symbol' in *; simpl in *.
        unfold vars_of in *; simpl in *.
        unfold to_PreTerm' in *.
        rewrite fold_left_app.
        simpl.
        rewrite <- IHl. clear IHl.
        unfold helper.
        ltac1:(repeat case_match); subst; simpl in *.
        {
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            unfold vars_of; simpl.
            ltac1:(set_solver).
        }
    }
Qed.


Definition size_of_var_in_val
    {Σ : StaticModel}
    (ρ : Valuation)
    (x : variable)
    : nat
:=
    match ρ!!x with
    | None => 0
    | Some g => pred (TermOver_size (prettify g))
    end
.

Definition delta_in_val
    {Σ : StaticModel}
    (ρ : Valuation)
    (ψ : TermOver BuiltinOrVar)
    : nat
:=
    sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ)
.



Lemma concrete_is_larger_than_symbolic
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    satisfies ρ γ φ ->
    TermOver_size γ = TermOver_size φ + delta_in_val ρ φ
.
Proof.
    revert φ.
    induction γ; intros φ H1.
    {
        inversion H1; subst; clear H1.
        apply (f_equal prettify) in H3.
        rewrite (cancel prettify uglify') in H3.
        subst φ.
        simpl.
        unfold delta_in_val.
        unfold vars_of_to_l2r.
        destruct z.
        {
            simpl. reflexivity.
        }
        {
            simpl.
            unfold size_of_var_in_val.
            inversion pf; subst; clear pf.
            rewrite H1. simpl.
            reflexivity.
        }
    }
    {
        simpl.
        destruct φ.
        {
            destruct a.
            {
                inversion H1; subst; clear H1.
                inversion H4.
            }
            {
                inversion H1; subst; clear H1.
                inversion H4; subst; clear H4.
                simpl.
                unfold delta_in_val. simpl.
                unfold size_of_var_in_val.
                rewrite H1. simpl.
                apply f_equal.
                ltac1:(replace ((prettify' (to_PreTerm' s (map uglify' l))))
                with ((t_term s l))).
                {
                    simpl. ltac1:(lia).
                }
                {
                    rewrite <- (cancel prettify uglify').
                    simpl.
                    reflexivity.
                }
            }
        }
        {
            apply satisfies_term_inv in H1.
            destruct H1 as [lγ [H2 [H3 H4]]].
            inversion H2; subst; clear H2.
            simpl.
            revert l0 H3 H4.
            induction lγ; intros l0 H3 H4.
            {
                destruct l0.
                {
                    simpl. unfold delta_in_val. simpl. ltac1:(lia).
                }
                {
                    simpl in H3. ltac1:(lia).
                }
            }
            {
                destruct l0.
                {
                    simpl in *. ltac1:(lia).
                }
                {
                    simpl in *.
                    rewrite Forall_cons in H.
                    destruct H as [H H'].
                    specialize (IHlγ H').
                    specialize (IHlγ l0 ltac:(lia)).
                    rewrite Forall_cons in H4.
                    destruct H4 as [H4 H4'].
                    specialize (IHlγ H4').
                    simpl in *.
                    specialize (H _ H4).
                    unfold delta_in_val. simpl.
                    rewrite sum_list_with_app.
                    rewrite H.
                    unfold delta_in_val in IHlγ.
                    simpl in IHlγ.
                    injection H3 as H3.
                    injection IHlγ as IHlγ.
                    rewrite IHlγ.
                    unfold delta_in_val.
                    ltac1:(lia).
                }
            }
        }
    }
Qed.

Lemma enveloping_preserves_or_increases_delta
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ1 γ2 : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    (s : symbol)
    (l1 l2 : list (TermOver BuiltinOrVar))
    (d : nat)
    :
    satisfies ρ γ1 φ ->
    satisfies ρ γ2 (t_term s (l1 ++ φ::l2)) ->
    TermOver_size γ1 = TermOver_size φ + d ->
    TermOver_size γ2 >= TermOver_size (t_term s (l1 ++ φ::l2)) + d
.
Proof.
    intros H1 H2 H3.
    simpl.
    apply satisfies_term_inv in H2.
    destruct H2 as [lγ [h4 [H5 H6]]].
    subst γ2. simpl in *.
    rewrite sum_list_with_app. simpl.
    rewrite app_length in H5. simpl in H5.

    destruct (lγ !! (length l1)) eqn:Hγ.
    {
        apply take_drop_middle in Hγ.
        rewrite <- Hγ in H6.
        rewrite zip_with_app in H6.
        {
            rewrite Forall_app in H6.
            simpl in H6.
            rewrite Forall_cons in H6.
            destruct H6 as [H6 [H7 H8]].
            assert (t = γ1).
            {
                eapply satisfies_inv.
                {
                    apply H7.
                }
                {
                    apply H1.
                }
            }
            subst t.
            simpl in *.
            rewrite <- Hγ.
            rewrite sum_list_with_app.
            simpl.
            rewrite H3.
            clear H3.
            clear Hγ.
            assert (sum_list_with (S ∘ TermOver_size) (take (length l1) lγ) >= sum_list_with (S ∘ TermOver_size) l1).
            {
                assert (Hineq: length lγ >= length l1) by ltac1:(lia).
                clear -H6 Hineq.
                revert lγ H6 Hineq.
                induction l1; intros lγ H6 Hineq.
                {
                    simpl. ltac1:(lia).
                }
                {
                    destruct lγ.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        simpl in H6.
                        rewrite Forall_cons in H6.
                        destruct H6 as [Hsat H6].
                        apply concrete_is_larger_than_symbolic in Hsat.
                        specialize (IHl1 _ H6).
                        simpl in *.
                        specialize (IHl1 ltac:(lia)).
                        ltac1:(lia).
                    }
                }
            }
            assert (((sum_list_with (S ∘ TermOver_size) (drop (S (length l1)) lγ))) >= (sum_list_with (S ∘ TermOver_size) l2)).
            {
                remember ((drop (S (length l1)) lγ)) as lγ'.
                assert (Hlen: length lγ' = length l2).
                {
                    subst.
                    rewrite drop_length.
                    ltac1:(lia).
                }
                clear -Hlen H8.
                revert l2 Hlen H8.
                induction lγ'; intros l2 Hlen H8.
                {
                    destruct l2.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        simpl in *. ltac1:(lia).
                    }
                }
                {
                    destruct l2.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        simpl in *.
                        rewrite Forall_cons in H8.
                        destruct H8 as [H1 H2].
                        apply concrete_is_larger_than_symbolic in H1.
                        specialize (IHlγ' l2 ltac:(lia) H2).
                        ltac1:(lia).
                    }
                }
            }
            
            ltac1:(lia).
        }
        {
            rewrite take_length.
            ltac1:(lia).
        }
        
    }
    {
        apply lookup_ge_None_1 in Hγ.
        ltac1:(lia).
    }
Qed.

Lemma sum_list_with_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 >= f2 x2) ->
    sum_list_with f1 l1 >= sum_list_with f2 l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 ≥ sum_list_with f2 l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.

Lemma sum_list_with_eq_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 = f2 x2) ->
    sum_list_with f1 l1 = sum_list_with f2 l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 = sum_list_with f2 l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.

Lemma sum_list_with_eq_plus_pairwise
    {T1 T2 : Type}
    (f1 : T1 -> nat)
    (f2 : T2 -> nat)
    (g : T2 -> nat)
    (l1 : list T1)
    (l2 : list T2)
    :
    length l1 = length l2 ->
    (forall i x1 x2, l1!!i = Some x1 -> l2!!i = Some x2 -> f1 x1 = f2 x2 + g x2) ->
    sum_list_with f1 l1 = sum_list_with f2 l2 + sum_list_with g l2
.
Proof.
    revert l2.
    induction l1; intros l2 Hlen H; destruct l2; simpl in *; try ltac1:(lia).
    {
        specialize (IHl1 l2 ltac:(lia)).
        assert (H' := H 0 a t eq_refl eq_refl).
        ltac1:(cut (sum_list_with f1 l1 = sum_list_with f2 l2 + sum_list_with g l2)).
        {
            intros HH. ltac1:(lia).
        }
        apply IHl1. intros.
        specialize (H (S i) x1 x2 H0 H1).
        apply H.
    }
Qed.


Lemma subst_notin_2
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of (uglify' ψ) ->
    h ∉ vars_of (uglify' (TermOverBoV_subst φ h ψ))
.
Proof.
    induction φ; intros HH; simpl in *.
    {
        destruct a.
        {
            simpl. unfold vars_of; simpl. unfold vars_of; simpl.
            ltac1:(set_solver).
        }
        {
            destruct (decide (h = x)).
            {
                subst. apply HH.
            }
            {
                unfold vars_of; simpl.
                unfold vars_of; simpl.
                ltac1:(set_solver).
            }
        }
    }
    {
        intros HContra. apply HH. clear HH.
        unfold apply_symbol' in HContra; simpl in HContra.
        unfold to_PreTerm' in HContra; simpl in HContra.
        unfold vars_of in HContra; simpl in HContra.
        revert s ψ  H HContra.
        induction l using rev_ind; intros s ψ HH HContra.
        {
            simpl in *. inversion HContra.
        }
        {
            rewrite Forall_app in HH.
            rewrite map_app in HContra.
            rewrite map_app in HContra.
            rewrite fold_left_app in HContra.
            simpl in HContra.
            destruct HH as [HH1 HH2].
            rewrite Forall_cons in HH2.
            destruct HH2 as [HH2 _].
            specialize (IHl s ψ HH1).
            simpl in *.
            unfold helper in HContra.
            destruct (uglify' (TermOverBoV_subst x h ψ)) eqn:Hugl.
            {
                unfold vars_of in HContra; simpl in HContra.
                rewrite elem_of_union in HContra.
                destruct HContra as [HContra|HContra].
                {
                    specialize (IHl HContra).
                    apply IHl.
                }
                {
                    destruct (decide (h ∈ vars_of (uglify' ψ))) as [Hyes|Hno].
                    {
                        assumption.
                    }
                    {
                        specialize (HH2 Hno). clear Hno. ltac1:(exfalso).
                        unfold vars_of in HH2; simpl in HH2.
                        unfold vars_of in HH2; simpl in HH2.
                        apply HH2. exact HContra.
                    }
                }
            }
            {
                unfold vars_of in HContra; simpl in HContra.
                rewrite elem_of_union in HContra.
                destruct HContra as [HContra|HContra].
                {
                    simpl in *.
                    destruct (decide (h ∈ vars_of (uglify' ψ))) as [Hyes|Hno].
                    {
                        assumption.
                    }
                    {
                        specialize (HH2 Hno). clear Hno. ltac1:(exfalso).
                        unfold vars_of in HH2; simpl in HH2.
                        unfold vars_of in HH2; simpl in HH2.
                        apply HH2. exact HContra.
                    }
                }
                {

                    specialize (IHl HContra).
                    apply IHl.
                }
            }
        }
    }
Qed.

Lemma sum_list_with_compose {A B : Type} (g : A -> B) (f : B -> nat)
    :
    sum_list_with (f ∘ g) = (sum_list_with f) ∘ (fmap g)
.
Proof.
    apply functional_extensionality.
    intros l.
    induction l; simpl.
    {
        reflexivity.
    }
    {
        rewrite IHl. unfold compose. reflexivity.
    }
Qed.

Lemma sum_list_with_S (l : list nat):
    sum_list_with S l = sum_list l + length l
.
Proof.
    induction l; simpl.
    {
        reflexivity.
    }
    {
        rewrite IHl.
        ltac1:(lia).
    }
Qed.

Lemma sum_list_fmap
    {T: Type}
    (f : T -> nat)
    (l : list T)
    :
    sum_list ( f <$> l) = sum_list_with f l
.
Proof.
    induction l; simpl.
    { reflexivity. }
    {
        unfold fmap in IHl.
        rewrite IHl.
        reflexivity.
    }
Qed.

Lemma sum_list_with_sum_list_with
    {T: Type}
    (f : T -> nat)
    (l : list (list T))
    :
    sum_list_with (sum_list_with f) l = sum_list_with f (concat l)
.
Proof.
    induction l; simpl.
    { reflexivity. }
    {
        rewrite IHl.
        rewrite sum_list_with_app.
        reflexivity.
    }
Qed.

Lemma subst_preserves_or_increases_delta
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ1 γ2 : TermOver builtin_value)
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of (uglify' ψ) ->
    h ∉ vars_of ρ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    satisfies ρ γ1 φ ->
    satisfies ρ γ2 (TermOverBoV_subst φ h ψ) ->
    (((TermOver_size γ2)) = (((TermOver_size (TermOverBoV_subst φ h ψ))) + (delta_in_val ρ φ ) + (delta_in_val ρ ψ)))
.
Proof.
    intros Hnotinpsi Hnotinrho Hfilter Hsat1 Hsat2.


    revert γ1 γ2 Hnotinpsi Hnotinrho Hfilter Hsat1 Hsat2.
    induction φ; intros γ1 γ2 Hnotinpsi Hnotinrho Hfilter Hsat1 Hsat2.
    {
        simpl in *.
        destruct a; simpl in *.
        {
            ltac1:(lia).
        }
        {
            rewrite filter_cons in Hfilter.
            destruct (decide (h = x)).
            {
                subst.
                simpl in *.
                apply concrete_is_larger_than_symbolic in Hsat2.
                inversion Hsat1; subst; clear Hsat1.
                {
                    apply (f_equal prettify) in H1.
                    rewrite (cancel prettify uglify') in H1.
                    subst. simpl in *.
                    unfold delta_in_val. simpl.
                    inversion pf; subst; clear pf.
                    unfold size_of_var_in_val.
                    rewrite H1. simpl. rewrite Hsat2. clear Hsat2.
                    unfold delta_in_val. unfold size_of_var_in_val.
                    ltac1:(lia).
                }
                {
                    apply (f_equal prettify) in H.
                    rewrite (cancel prettify uglify') in H.
                    subst. simpl in *.
                    inversion H2; subst; clear H2.
                    clear -H0 Hnotinrho.
                    unfold vars_of in Hnotinrho; simpl in Hnotinrho.
                    rewrite elem_of_dom in Hnotinrho.
                    ltac1:(rewrite H0 in Hnotinrho).
                    ltac1:(exfalso).
                    apply Hnotinrho.
                    unfold is_Some. exists (term_preterm axy).
                    reflexivity.
                }
            }
            {
                simpl in Hfilter. ltac1:(lia).
            }
        }
    }
    {
        simpl in *.
        apply satisfies_term_inv in Hsat2.
        destruct Hsat2 as [lγ [H1 [H2 H3]]].
        subst. simpl in *.
        rewrite map_length in H2.

        apply satisfies_term_inv in Hsat1.
        destruct Hsat1 as [l'γ [H4 [H5 H6]]].
        subst. simpl in *.
        clear Hnotover.

        assert (Hconcat: h ∈ concat (map vars_of_to_l2r l)).
        {
            clear -Hfilter.
            induction l; simpl in *.
            { ltac1:(lia). }
            {
                rewrite filter_app in Hfilter.
                rewrite app_length in Hfilter.
                destruct (decide (h ∈ vars_of_to_l2r a)).
                {
                    rewrite elem_of_app. left. assumption.
                }
                {
                    ltac1:(ospecialize (IHl _)).
                    {
                        ltac1:(cut(length (filter (eq h) (vars_of_to_l2r a)) = 0)).
                        {
                            intros HH. ltac1:(lia).
                        }
                        rewrite length_zero_iff_nil.
                        remember (vars_of_to_l2r a) as l'.
                        clear Heql'.
                        clear -n.
                        induction l'.
                        {
                            reflexivity.
                        }
                        {
                            rewrite elem_of_cons in n.
                            apply Decidable.not_or in n.
                            destruct n as [H1 H2].
                            specialize (IHl' H2).
                            rewrite filter_cons.
                            destruct (decide (h = a)).
                            {
                                subst. ltac1:(contradiction).
                            }
                            {
                                apply IHl'.
                            }
                        }
                    }
                    {
                        rewrite elem_of_app. right. apply IHl.
                    }
                }
            }
        }
        rewrite elem_of_list_In in Hconcat.
        rewrite in_concat in Hconcat.
        destruct Hconcat as [x [H1x H2x]].
        rewrite in_map_iff in H1x.
        destruct H1x as [x0 [H1x0 H2x0]].
        subst.
        rewrite <- elem_of_list_In in H2x0.
        rewrite elem_of_list_lookup in H2x0.
        destruct H2x0 as [i Hi].
        assert (H'i := Hi).
        apply take_drop_middle in Hi.
        rewrite <- Hi.
        rewrite <- Hi in Hfilter.
        rewrite <- Hi in H3.
        rewrite map_app in H3.
        rewrite map_app.
        rewrite sum_list_with_app.
        simpl in *.

        destruct (lγ !! i) eqn:Hlγi.
        {
            destruct (l'γ !! i) eqn:Hl'γi.
            {
                apply take_drop_middle in Hlγi.
                apply take_drop_middle in Hl'γi.
                rewrite <- Hlγi.
                rewrite sum_list_with_app.
                simpl.
                rewrite <- Hi in H.
                rewrite Forall_app in H.
                destruct H as [IH1 IH2].
                rewrite Forall_cons in IH2.
                destruct IH2 as [IH2 IH3].
                rewrite <- Hlγi in H3.
                rewrite zip_with_app in H3.
                {
                    rewrite Forall_app in H3.
                    destruct H3 as [H31 H32].
                    simpl in H32.
                    rewrite Forall_cons in H32.
                    destruct H32 as [H32 H33].
                    rewrite Forall_forall in H31.
                    ltac1:(setoid_rewrite elem_of_lookup_zip_with in H31).


                    assert (
                        (sum_list_with
                            (S ∘ TermOver_size)
                            (take i lγ)) =
                        (sum_list_with
                            (S ∘ TermOver_size)
                            (take i l)
                        ) +
                        sum_list_with (delta_in_val ρ) (take i l)).
                    {
                        apply sum_list_with_eq_plus_pairwise.
                        {
                            rewrite take_length.
                            rewrite take_length.
                            ltac1:(lia).
                        }
                        {
                            intros i0 x1 x2 HH1 HH2.
                            unfold compose. simpl.
                            simpl in HH2.
                            assert (HH'1 := HH1).
                            rewrite lookup_take in HH2.
                            {
                                destruct (l !! i0) eqn:H'li0.
                                {
                                    simpl in HH2. inversion HH2.
                                    subst; clear HH2.
                                    
                                    assert (Hhx2: h ∉ vars_of_to_l2r x2).
                                    {
                                        {
                                            intros HContra.
                                            rewrite map_app in Hfilter.
                                            rewrite concat_app in Hfilter.
                                            assert (H_i0_lt_i: i0 < i).
                                            {
                                                apply lookup_lt_Some in HH1.
                                                rewrite take_length in HH1.
                                                ltac1:(lia).
                                            }
                                            simpl in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            simpl in Hfilter.
                                            rewrite app_length in Hfilter.
                                            rewrite app_length in Hfilter.
                                            assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (take i l))))).
                                            {
                                                destruct ((take i l) !! i0) eqn:Heq.
                                                {
                                                    assert (Heq' := Heq).
                                                    apply take_drop_middle in Heq.
                                                    rewrite <- Heq.
                                                    rewrite map_app.
                                                    rewrite concat_app.
                                                    rewrite filter_app.
                                                    simpl.
                                                    rewrite filter_app.
                                                    apply lookup_take_Some in Heq'.
                                                    rewrite H'li0 in Heq'.
                                                    destruct Heq' as [Heq'1 _].
                                                    inversion Heq'1; subst; clear Heq'1.
                                                    rewrite app_length.
                                                    rewrite app_length.
                                                    rewrite elem_of_list_lookup in HContra.
                                                    destruct HContra as [j Hj].
                                                    apply take_drop_middle in Hj.
                                                    rewrite <- Hj.
                                                    rewrite filter_app.
                                                    rewrite app_length.
                                                    rewrite filter_cons.
                                                    destruct (decide (h = h))>[|ltac1:(contradiction)].
                                                    simpl.
                                                    ltac1:(lia).
                                                }
                                                {
                                                    apply lookup_ge_None_1 in Heq.
                                                    rewrite take_length in Heq.
                                                    apply lookup_lt_Some in H'li0.
                                                    ltac1:(lia).
                                                }
                                            }
                                            clear -Hfilter H2x H'i Htmp.
                                            apply take_drop_middle in H'i.
                                            rewrite <- H'i in Hfilter at 2.
                                            rewrite drop_app in Hfilter.
                                            rewrite map_app in Hfilter.
                                            rewrite concat_app in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            rewrite app_length in Hfilter.
                                            rewrite <- elem_of_list_In in H2x.
                                            assert (H'2x := H2x).
                                            rewrite elem_of_list_lookup in H2x.
                                            destruct H2x as [i0 H2x].
                                            apply take_drop_middle in H2x.
                                            rewrite <- H2x in Hfilter.
                                            rewrite take_length in Hfilter.
                                            simpl in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            rewrite filter_cons in Hfilter.
                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                            rewrite app_length in Hfilter.
                                            simpl in Hfilter.
                                            ltac1:(lia).
                                        }
                                    }
                                    apply f_equal.
                                    apply concrete_is_larger_than_symbolic.
                                    apply H31.
                                    exists i0.
                                    exists x1,x2.
                                    split>[reflexivity|].
                                    split>[assumption|].
                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                    rewrite list_lookup_fmap.
                                    rewrite lookup_take.
                                    {
                                        rewrite H'li0.
                                        simpl.
                                        rewrite subst_notin.
                                        {
                                            reflexivity.
                                        }
                                        {
                                            apply Hhx2.
                                        }
                                    }
                                    {
                                        apply lookup_lt_Some in HH1.
                                        rewrite take_length in HH1.
                                        ltac1:(lia).
                                    }
                                    
                                }
                                {
                                    simpl in HH2. inversion HH2.
                                }
                            }
                            {
                                apply lookup_lt_Some in HH1.
                                rewrite take_length in HH1.
                                ltac1:(lia).
                            }
                        }
                    }

                    assert (
                        (sum_list_with
                            (S ∘ TermOver_size)
                            (drop (S i) lγ)) =
                        (sum_list_with
                            (S ∘ TermOver_size)
                            (drop (S i) l)
                        ) +
                        sum_list_with (delta_in_val ρ) (drop (S i) l)).
                    {
                        apply sum_list_with_eq_plus_pairwise.
                        {
                            rewrite drop_length.
                            rewrite drop_length.
                            ltac1:(lia).
                        }
                        {
                            intros i0 x1 x2 HH1 HH2.
                            unfold compose. simpl.
                            simpl in HH2.
                            assert (HH'1 := HH1).
                            rewrite lookup_drop in HH2.
                            {
                                destruct (l !! i0) eqn:H'li0.
                                {
                                    simpl in HH2. inversion HH2.
                                    subst; clear HH2.
                                    
                                    assert (Hhx2: h ∉ vars_of_to_l2r x2).
                                    {
                                        {
                                            intros HContra.
                                            rewrite map_app in Hfilter.
                                            rewrite concat_app in Hfilter.
                                            simpl in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            simpl in Hfilter.
                                            rewrite app_length in Hfilter.
                                            rewrite app_length in Hfilter.
                                            ltac1:(
                                                replace ( S (i + i0))
                                                with ((S i) + i0)
                                                in H1
                                                by lia
                                            ).
                                            ltac1:(rewrite <- lookup_drop in H1).
                                            apply take_drop_middle in H1.
                                            rewrite <- H1 in Hfilter.
                                            rewrite map_app in Hfilter.
                                            rewrite concat_app in Hfilter.
                                            simpl in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            rewrite app_length in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            rewrite app_length in Hfilter.
                                            rewrite elem_of_list_lookup in HContra.
                                            destruct HContra as [j HContra].
                                            apply take_drop_middle in HContra.
                                            rewrite <- HContra in Hfilter.
                                            rewrite filter_app in Hfilter.
                                            rewrite filter_cons in Hfilter.
                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                            rewrite app_length in Hfilter.
                                            simpl in Hfilter.
                                            rewrite <- elem_of_list_In in H2x.
                                            rewrite elem_of_list_lookup in H2x.
                                            destruct H2x as [j' H2x].
                                            apply take_drop_middle in H2x.
                                            rewrite <- H2x in Hfilter.
                                            clear -Hfilter.
                                            rewrite filter_app in Hfilter.
                                            rewrite filter_cons in Hfilter.
                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                            simpl in Hfilter.
                                            rewrite app_length in Hfilter.
                                            simpl in Hfilter.
                                            ltac1:(lia).
                                        }
                                    }
                                    
                                    apply f_equal.
                                    apply concrete_is_larger_than_symbolic.
                                    rewrite Forall_forall in H33.
                                    apply H33.
                                    rewrite elem_of_lookup_zip_with.
                                    exists i0.
                                    exists x1,x2.
                                    split>[reflexivity|].
                                    split>[assumption|].
                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                    rewrite list_lookup_fmap.
                                    rewrite lookup_drop.
                                    simpl.
                                    rewrite H1.
                                    simpl.
                                    rewrite subst_notin.
                                    {
                                        reflexivity.
                                    }
                                    {
                                        apply Hhx2.
                                    }
                                }
                                {
                                    apply lookup_ge_None_1 in H'li0.
                                    apply lookup_lt_Some in HH'1.
                                    rewrite drop_length in HH'1.
                                    ltac1:(lia).
                                }
                            }
                        }
                    }


                    

                    (* new attempt:*)
                    (*injection Hsz as Hsz.*)
                    rewrite <- Hi in H6.
                    rewrite <- Hl'γi in H6.
                    rewrite zip_with_app in H6.
                    {
                        simpl in H6.
                        rewrite Forall_app in H6.
                        rewrite Forall_cons in H6.
                        destruct H6 as [H61 [H62 H63]].

                        specialize (IH2 t0 t).

                        remember ((sum_list_with (S ∘ TermOver_size) (take i lγ))) as Y1.
                        remember ((sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (take i l)))) as Y1'.
                        remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) lγ) ) as Y2.
                        remember ( sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (drop (S i) l)) ) as Y2'.
                        remember (sum_list_with (S ∘ TermOver_size) (take i l)) as Y3.
                        remember (sum_list_with (S ∘ TermOver_size) (take i l'γ)) as Y3'.
                        remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) l) ) as Y4.
                        remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) l'γ) ) as Y4'.

                        assert (H32' := H32).
                        assert (H62' := H62).
                        apply concrete_is_larger_than_symbolic in H32'.
                        apply concrete_is_larger_than_symbolic in H62'.

                        specialize (IH2 ltac:(assumption) ltac:(assumption)).
                        ltac1:(ospecialize (IH2 _)).
                        {
                            rewrite map_app in Hfilter.
                            rewrite concat_app in Hfilter.
                            rewrite filter_app in Hfilter.
                            rewrite app_length in Hfilter.
                            simpl in Hfilter.
                            clear - H2x Hfilter.
                            rewrite filter_app in Hfilter.
                            rewrite app_length in Hfilter.
                            ltac1:(cut (length (filter (eq h) (vars_of_to_l2r x0)) >= 1)).
                            {
                                intros HH. ltac1:(lia).
                            }
                            clear Hfilter.
                            rewrite <- elem_of_list_In in H2x.
                            rewrite elem_of_list_lookup in H2x.
                            destruct H2x as [j Hj].
                            apply take_drop_middle in Hj.
                            rewrite <- Hj. clear Hj.
                            rewrite filter_app. 
                            simpl. 
                            rewrite app_length.
                            rewrite filter_cons.
                            destruct (decide (h = h))>[|ltac1:(contradiction)].
                            simpl.
                            ltac1:(lia).
                        }
                        specialize (IH2 ltac:(assumption) ltac:(assumption)).


                        apply concrete_is_larger_than_symbolic in H32.
                        apply concrete_is_larger_than_symbolic in H62.
                        unfold delta_in_val.
                        simpl.
                        rewrite map_app. simpl.
                        rewrite concat_app. simpl.
                        apply f_equal.
                        rewrite sum_list_with_app.
                        rewrite sum_list_with_app.
                        subst.
                        remember (sum_list_with (S ∘ TermOver_size) (take i lγ)) as B1.
                        remember ( sum_list_with (S ∘ TermOver_size) (drop (S i) lγ) ) as B2.
                        remember ( sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (take i l)) ) as B3.
                        remember ( sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (drop (S i) l))) as B4.
                        remember ( sum_list_with (size_of_var_in_val ρ) (concat (map vars_of_to_l2r (take i l)) )) as B5.
                        remember ( sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r x0) ) as B6.
                        remember ( sum_list_with (size_of_var_in_val ρ) (concat (map vars_of_to_l2r (drop (S i) l)))) as B7.
                        remember ( delta_in_val ρ x0 ) as DX0.
                        unfold delta_in_val in *. simpl in *.
                        remember (sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ)) as Dψ.
                        remember ((TermOver_size (TermOverBoV_subst x0 h ψ))) as Bsubst.
                        rewrite H32'.
                        remember (sum_list_with (size_of_var_in_val ρ)) as F.
                        remember ((vars_of_to_l2r (TermOverBoV_subst x0 h ψ))) as VS.


                        ltac1:(cut(B1 + (F VS + B2) = B3 + (B4) + (B5 + (B6 + B7)) + Dψ)).
                        {
                            intros HH. ltac1:(lia).
                        }

                        assert (Htmp1: DX0 + Dψ = F VS).
                        {
                            ltac1:(lia).
                        }
                        rewrite <- Htmp1.

                        ltac1:( cut (B1 + (DX0 + B2) = B3 + B4 + (B5 + (B6 + B7))) ).
                        {
                            intros HH. ltac1:(lia).
                        }

                        clear H32'.

                        rewrite <- Htmp1 in H32. clear Htmp1.
                        rewrite sum_list_with_compose in HeqB2.
                        ltac1:(rewrite sum_list_with_compose in HeqB2).
                        rewrite sum_list_with_compose in HeqB1.
                        ltac1:(rewrite sum_list_with_compose in HeqB1).
                        ltac1:(rewrite sum_list_with_compose in HeqB4).
                        unfold compose in HeqB4.
                        ltac1:(rewrite sum_list_with_S in HeqB4).
                        rewrite fmap_length in HeqB4.
                        rewrite map_length in HeqB4.
                        rewrite drop_length in HeqB4.
                        ltac1:(rewrite sum_list_with_compose in H0).
                        unfold compose in H0.
                        ltac1:(rewrite sum_list_with_S in H0).
                        rewrite fmap_length in H0.
                        rewrite drop_length in H0.
                        subst F.
                        unfold compose in HeqB1.
                        ltac1:(rewrite sum_list_with_S in HeqB1).
                        ltac1:(replace (@fmap _ list_fmap) with map in HeqB1 by reflexivity).
                        rewrite map_id in HeqB1.
                        rewrite map_length in HeqB1.
                        rewrite take_length in HeqB1.
                        unfold compose in HeqB2.
                        ltac1:(replace (@fmap _ list_fmap) with map in HeqB2 by reflexivity).
                        rewrite map_id in HeqB2.
                        rewrite sum_list_with_S in HeqB2.
                        rewrite map_length in HeqB2.
                        rewrite drop_length in HeqB2.
                        rewrite sum_list_with_compose in HeqB3.
                        unfold compose in HeqB3.
                        rewrite sum_list_with_S in HeqB3.
                        rewrite fmap_length in HeqB3.
                        rewrite map_length in HeqB3.
                        rewrite take_length in HeqB3.
                        rewrite sum_list_with_compose in H.
                        unfold compose in H.
                        rewrite sum_list_with_S in H.
                        rewrite fmap_length in H.
                        rewrite take_length in H.
                        

                        ltac1:(replace map with (@fmap _ list_fmap) in HeqB3 by reflexivity).
                        subst.
                        (* the only use of [TermOver_size t] *)
                        clear H32 IH2.

                        assert (H0': sum_list (map TermOver_size (drop (S i) lγ))
                        = sum_list (TermOver_size <$> drop (S i) l)
                        + sum_list_with (λ ψ0 : TermOver BuiltinOrVar,  sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0)) (drop (S i) l) ).
                        {
                            ltac1:(lia).
                        }
                        clear H0.
                        rewrite H0'.
                        (* Search drop lγ. *)
                        clear Hlγi H0' H33.

                        assert(HeqB1': sum_list (TermOver_size <$> take i l) + sum_list_with (λ ψ0 : TermOver BuiltinOrVar, sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0)) (take i l) = sum_list (map TermOver_size (take i lγ))).
                        {
                            ltac1:(lia).
                        }
                        clear HeqB1. clear H31.
                        (* Search TermOver_size t0. *)
                        clear H61 H62'.
                        ltac1:(
                            replace
                            (sum_list_with
                                (λ ψ0 : TermOver BuiltinOrVar,
                                sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0))
                                (take i l))
                            with
                            (sum_list_with ((sum_list_with (size_of_var_in_val ρ)) ∘ vars_of_to_l2r) (take i l) )
                            in HeqB1'
                            by reflexivity
                        ).
                        rewrite sum_list_with_compose in HeqB1'.
                        ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                        repeat (rewrite sum_list_fmap).
                        repeat (rewrite sum_list_fmap in HeqB1').
                        ltac1:(
                            replace
                            (sum_list_with (λ ψ0 : TermOver BuiltinOrVar, sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r ψ0)))
                            with
                            (sum_list_with (sum_list_with (size_of_var_in_val ρ) ∘ (vars_of_to_l2r)))
                            by reflexivity
                        ).
                        (*
                        ltac1:(
                            replace
                            (sum_list_with TermOver_size ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> take i l))
                            with
                            (sum_list_with TermOver_size ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> take i l))
                        ).
                        *)
                        repeat (rewrite sum_list_with_compose).
                        repeat (rewrite sum_list_fmap).
                        unfold compose.
                        do 2 (rewrite sum_list_with_sum_list_with).
                        remember ((sum_list_with (size_of_var_in_val ρ) (concat (vars_of_to_l2r <$> take i l)) )) as N1.
                        remember (sum_list_with TermOver_size (take i l)) as N0.
                        remember (sum_list_with TermOver_size ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> take i l)) as N0'.
                        remember ((sum_list_with TermOver_size (drop (S i) l) )) as N3.
                        remember ( (sum_list_with TermOver_size ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> drop (S i) l) )) as N3'.
                        remember ( (sum_list_with (size_of_var_in_val ρ) (vars_of_to_l2r x0) ) ) as N2.
                        remember ( sum_list_with (size_of_var_in_val ρ) (concat (vars_of_to_l2r <$> drop (S i) l)) ) as N4.

                        ltac1:(assert (N0 = (N0'))).
                        {
                            subst N0 N0'.
                            apply sum_list_with_eq_pairwise.
                            {
                                rewrite fmap_length.
                                reflexivity.
                            }
                            {
                                intros i0 x1 x2 Hx1 Hx2.
                                rewrite list_lookup_fmap in Hx2.
                                simpl in Hx2.
                                rewrite Hx1 in Hx2. simpl in Hx2.
                                rewrite subst_notin in Hx2.
                                {
                                    inversion Hx2; subst; clear Hx2.
                                    reflexivity.
                                }
                                {
                                    
                                }
                            }
                        }

                        ltac1:(assert(N3 = N3')).
                        {
                            admit.
                        }

                        ltac1:(lia).
                    }
                    {
                        rewrite take_length.
                        rewrite take_length.
                        ltac1:(lia).
                    }
                    (*
                    specialize (IH2 (2 + d + (sum_list_with (S ∘ TermOver_size) (take i l)) + (sum_list_with (S ∘ TermOver_size) (drop (S i) l)))).
                    ltac1:(ospecialize (IH2 _)).
                    {
                        rewrite <- Hi in Hsz.
                        rewrite sum_list_with_app in Hsz.
                        simpl in Hsz.
                        rewrite Hsz.
                        clear.
                        ltac1:(lia).
                    }
                    specialize (IH2 Hnotinpsi Hnotinrho).
                    ltac1:(ospecialize (IH2 _)).
                    {
                        rewrite map_app in Hfilter.
                        rewrite concat_app in Hfilter.
                        rewrite filter_app in Hfilter.
                        rewrite app_length in Hfilter.
                        simpl in Hfilter.
                        clear - H2x Hfilter.
                        rewrite filter_app in Hfilter.
                        rewrite app_length in Hfilter.
                        ltac1:(cut (length (filter (eq h) (vars_of_to_l2r x0)) >= 1)).
                        {
                            intros HH. ltac1:(lia).
                        }
                        clear Hfilter.
                        rewrite <- elem_of_list_In in H2x.
                        rewrite elem_of_list_lookup in H2x.
                        destruct H2x as [j Hj].
                        apply take_drop_middle in Hj.
                        rewrite <- Hj. clear Hj.
                        rewrite filter_app. 
                        simpl. 
                        rewrite app_length.
                        rewrite filter_cons.
                        destruct (decide (h = h))>[|ltac1:(contradiction)].
                        simpl.
                        ltac1:(lia).
                    }
                    *)
                    (*
                    (* TODO we do not want this, we want to use the IH. *)
                    apply concrete_is_larger_than_symbolic in H32.
                    *)

                    unfold compose in *. simpl in *.
                    rewrite <- Hi in Hsz.
                    rewrite <- Hl'γi in Hsz.
                    simpl in Hsz.
                    rewrite sum_list_with_app in Hsz.
                    rewrite sum_list_with_app in Hsz.
                    simpl in Hsz.
                    remember (TermOver_size t0) as N0'.
                    remember (TermOver_size t) as N0.
                    remember (sum_list_with (λ x : TermOver builtin_value, S (TermOver_size x)) (take i lγ)) as N1.
                    remember (sum_list_with (λ x : TermOver builtin_value, S (TermOver_size x)) (drop (S i) lγ)) as N2.
                    remember ((sum_list_with (λ x : TermOver BuiltinOrVar, S (TermOver_size x)) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (take i l)))) as N3.
                    remember (sum_list_with (λ x : TermOver BuiltinOrVar, S (TermOver_size x)) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) (drop (S i) l))) as N4.
                    remember (TermOver_size (TermOverBoV_subst x0 h ψ)) as N5.
                    remember ((sum_list_with (λ x : TermOver builtin_value, S (TermOver_size x)) (take i l'γ))) as N6.
                    remember (sum_list_with (λ x : TermOver builtin_value, S (TermOver_size x)) (drop (S i) l'γ)) as N7.
                    remember ((sum_list_with (λ x : TermOver BuiltinOrVar, S (TermOver_size x)) (take i l))) as N8.
                    remember (sum_list_with (λ x : TermOver BuiltinOrVar, S (TermOver_size x)) (drop (S i) l)) as N9.


                    revert N1 HeqN1 N6 HeqN6 Hsz H.
                    intros N1 HeqN1 N6 HeqN6 Hsz H.


                    ltac1:(lia).

                }
                {
                    rewrite map_length.
                    rewrite take_length.
                    rewrite take_length.
                    ltac1:(lia).
                }
                
            }
            {
                apply lookup_ge_None_1 in Hl'γi.
                apply lookup_lt_Some in H'i.
                ltac1:(lia).                
            }
        }
        {
            apply lookup_ge_None_1 in Hlγi.
            apply lookup_lt_Some in H'i.
            ltac1:(lia).
        }

        ltac1:(cut((sum_list_with (S ∘ TermOver_size) (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) l) + d) <= (sum_list_with (S ∘ TermOver_size) lγ))).
        {
            intros HH. ltac1:(lia).
        }
        apply sum_list_with_pairwise.
        Search sum_list_with.

        revert l H Hsz H5 H6.

        destruct (decide (h ∈ vars_of (uglify' (t_term s l)))) as [Hin|Hnotin].
        {
            rewrite <- vars_of_uglify in Hin.
            rewrite elem_of_list_lookup in Hin.
            destruct Hin as [i Hi].
            simpl in Hi.
            apply elem_of_list_lookup_2 in Hi.
            rewrite elem_of_list_In in Hi.
            rewrite in_concat in Hi.
            destruct Hi as [x [H1x H2x]].
            rewrite <- elem_of_list_In in H1x.
            rewrite <- elem_of_list_In in H2x.
            ltac1:(replace map with (@fmap _ list_fmap) in H2x by reflexivity).
            apply elem_of_list_fmap_2 in H1x.
            destruct H1x as [y [H1y H2y]].
            subst x.
            rewrite elem_of_list_lookup in H2y.
            destruct H2y as [j Hj].
            apply take_drop_middle in Hj.
            simpl in *.
        }
        {
            rewrite subst_notin.
            {
                rewrite subst_notin in Hsat2.
                {
                    assert (Hsativ := satisfies_inv ρ _ _ _ Hsat1 Hsat2).
                    subst γ2.
                    ltac1:(lia).
                }
                {
                    rewrite vars_of_uglify. apply Hnotin.
                }
            }
            {
                rewrite vars_of_uglify. apply Hnotin.
            }
        }
    }




    induction φ.
    {
        simpl. destruct a.
        {
            simpl in *.
            rewrite <- Hsz. clear Hsz.
            destruct γ1.
            {
                inversion Hsat1; subst; clear Hsat1;
                inversion Hsat2; subst; clear Hsat2.
                {
                    inversion pf; subst; clear pf.
                    apply (f_equal prettify) in H1.
                    rewrite (cancel prettify uglify') in H1.
                    subst.
                    simpl.
                    ltac1:(lia).
                }
                {
                    inversion pf; subst; clear pf.
                    inversion H2; subst; clear H2.
                }
            }
            {
                simpl in *.
                inversion Hsat2; subst; clear Hsat2.
                {
                    apply (f_equal prettify) in H1.
                    rewrite (cancel prettify uglify') in H1.
                    subst.
                    inversion pf; subst; clear pf.
                    simpl.
                    inversion Hsat1; subst; clear Hsat1.
                    inversion H2; subst; clear H2.
                }
                {
                    apply (f_equal prettify) in H.
                    rewrite (cancel prettify uglify') in H.
                    subst.
                    inversion Hsat1; subst; clear Hsat1.
                    inversion H2; subst; clear H2.
                }
            }
        }
        {
            simpl in *.
            destruct (decide (h = x)).
            {
                subst. simpl in *.
                inversion Hsat1; subst; clear Hsat1.
                {
                    apply (f_equal prettify) in H1.
                    rewrite (cancel prettify uglify') in H1.
                    subst.
                    simpl in *.
                    inversion Hsz; subst; clear Hsz.
                    inversion pf; subst; clear pf.
                    apply concrete_is_larger_than_symbolic in Hsat2.
                    ltac1:(lia).
                }
                {
                    apply (f_equal prettify) in H.
                    rewrite (cancel prettify uglify') in H.
                    subst. simpl in *.
                    inversion H2; subst; clear H2.
                    apply concrete_is_larger_than_symbolic in Hsat2.
                    ltac1:(lia).
                }
            }
            {

            }
        }
    }
Qed.
*)
(*
Lemma satisfies_subst_instance
    {Σ : StaticModel}
    (ρ : Valuation)
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    (γ : TermOver builtin_value)
    :
    satisfies ρ γ (TermOverBoV_subst φ h ψ)  ->
    satisfies ρ γ ψ ->
    satisfies ρ γ (TermOverBoV_subst φ h (TermOverBuiltin_to_TermOverBoV γ))
.
Proof.
    intros H1 H2.
    assert (H3: ψ = (TermOverBoV_subst φ h ψ)).
    {
        About satisfies_inv.
        eapply satisfies_inv.
    }
    assert (Htmp := satisfies_inv ρ).
    revert γ ψ.
    induction φ; intros γ ψ HH1 HH2.
    {
        destruct a; simpl in *.
        { apply HH1. }
        {
            destruct (decide (h = x)).
            {
                subst.
                apply satisfies_TermOverBuiltin_to_TermOverBoV.
            }
            {
                apply HH1.
            }
        }
    }
    {
        simpl in *.
        destruct γ; simpl in *.
        {
            inversion HH1.
        }
        inversion HH1; subst; clear HH1.
        ltac1:(rename pf into HH1).
        unfold to_PreTerm' in HH1.
        rewrite <- satisfies_top_bov_cons in HH1.
        destruct HH1 as [HH1 [HH3 HH4]].
        subst s0.
        rewrite map_length in HH1.
        constructor.
        fold (@uglify' Σ).
        unfold to_PreTerm'.
        rewrite <- satisfies_top_bov_cons.
        (repeat split).
        {
            rewrite map_length.
            exact HH1.
        }
        {
            rewrite Forall_forall in H.


            rewrite Forall_forall.
            intros x Hx.
            
            apply elem_of_lookup_zip_with in Hx.
            destruct Hx as [i0 [x0 [y0 [H1x0y0 [H2x0y0 H3x0y0]]]]].
            subst x.

            ltac1:(replace map with (@fmap _ list_fmap) in H3x0y0 by reflexivity).
            rewrite list_lookup_fmap in H3x0y0.


            destruct (l !! i0) eqn:Hli0.
            {
                specialize (H t).
                ltac1:(ospecialize (H _)).
                {
                    rewrite elem_of_list_lookup.
                    eexists. exact Hli0.
                }
                inversion H3x0y0; subst; clear H3x0y0.
                unfold TermOverBuiltin_to_TermOverBoV.
                unfold TermOver_map.
                fold (@TermOver_map Σ).

                (*
                destruct ψ.
                {
                    destruct a.
                    {
                        inversion HH2. subst. clear HH2. inversion H3.
                    }
                    {
                        simpl in *.
                        inversion HH2. subst. clear HH2.
                        inversion H3. subst. clear H3.
                    }
                }
                *)

                rewrite Forall_forall in HH3.
                ltac1:(setoid_rewrite elem_of_lookup_zip_with in HH3).
                assert(HH3' := HH3).
                specialize (HH3 (satisfies ρ x0 ((TermOverBoV_subst t h ψ)))).
                ltac1:(ospecialize (HH3 _)).
                {
                    exists i0.
                    exists x0.
                    exists ((TermOverBoV_subst t h ψ)).
                    split>[reflexivity|].
                    split>[apply H2x0y0|].
                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                    rewrite list_lookup_fmap.
                    rewrite Hli0.
                    simpl.
                    reflexivity.
                }
                clear HH3'.
                revert H.
                induction t; intros H'; simpl in *.
                {
                    destruct a; simpl in *.
                    {
                        exact HH3.
                    }
                    {
                        destruct (decide (h = x)).
                        {
                            subst.
                            specialize (H' _ _ HH3 HH3).
                            destruct x0; simpl in *.
                            {
                                inversion H'; subst; clear H'.
                                inversion HH3; subst; clear HH3.
                                apply (f_equal prettify) in H2.
                                rewrite (cancel prettify uglify') in H2.
                                subst ψ.
                                simpl in *.
                                inversion HH2; subst; clear HH2.
                                unfold to_PreTerm' in H2.
                                destruct z; simpl in *.
                                {
                                    inversion pf0; subst; clear pf0.
                                    apply satisfies_builtin_inv in H2.
                                    inversion H2.
                                }
                                {
                                    inversion pf0; subst; clear pf0.
                                    inversion H2; subst; clear H2.
                                    rewrite H1 in H0.
                                    inversion H0; subst; clear H0.
                                }
                            }
                            {
                                unfold TermOverBuiltin_to_TermOverBoV in H'.
                                unfold TermOver_map in H'.
                                fold (@TermOver_map Σ) in H'.
                                destruct ψ; simpl in *.
                                {
                                    destruct a; simpl in *.
                                    {
                                        inversion HH2; subst; clear HH2.
                                        inversion HH3; subst; clear HH3.
                                        apply satisfies_builtin_inv in H3.
                                        inversion H3.
                                    }
                                    {
                                        inversion HH2; subst; clear HH2.
                                        inversion HH3; subst; clear HH3.
                                        inversion H2; subst; clear H2.
                                        inversion H3; subst; clear H3.
                                        rewrite H0 in H1.
                                        inversion H1; subst; clear H1.
                                        apply to_preterm_eq_inv in H2.
                                        destruct H2 as [H21 H22].
                                        subst s0.
                                        clear - H' H22.
                                        apply map_uglify'_inj in H22.
                                        subst l0.
                                        exact H'.
                                    }
                                }
                                {
                                    apply satisfies_term_inv in HH3.
                                    destruct HH3 as [lγ [HH31 [HH32 HH33]]].
                                    inversion HH31; subst; clear HH31.
                                    apply satisfies_term_inv in HH2.
                                    destruct HH2 as [γ1 [HH21 [HH22 HH23]]].
                                    inversion HH21; subst; clear HH21.
                                }
                            }
                            Search satisfies t_term.
                        }
                        {

                        }
                    }
                }
                specialize (H x0 ψ HH3).
                
            }
            {
                ltac1:(exfalso).
                apply lookup_ge_None_1 in Hli0.
                apply lookup_lt_Some in H2x0y0.
                ltac1:(lia).
            }

            rewrite Forall_forall in HH3.
            specialize (HH3 x).
            rewrite elem_of_lookup_zip_with in HH3.
            ltac1:(ospecialize (HH3 _)).
            {
                clear HH3.
                exists i0, x0, y0.
                split>[reflexivity|].
                split>[assumption|].
            }
            exists i0, x0, y0.

            ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
            ltac1:(replace map with (@fmap _ list_fmap) in H3x0y0 by reflexivity).
            rewrite list_lookup_fmap in H3x0y0.
            rewrite list_lookup_fmap.
            destruct (l !! i0) eqn:Hli0.
            {
                inversion H3x0y0; subst; clear H3x0y0.
                simpl.
                apply f_equal.
            }
            {
                ltac1:(exfalso).
                apply lookup_ge_None_1 in Hli0.
                apply lookup_lt_Some in H2x0y0.
                ltac1:(lia).
            }

        }




        revert γ ψ HH1 HH2 H.
        induction l using rev_ind; intros γ ψ HH1 HH2 H.
        {
            simpl in *. apply HH1.
        }
        {
            rewrite Forall_app in H.
            destruct H as [H1 H2].
            destruct γ.
            {
                inversion HH1.
            }
            simpl in HH1.
            apply satisfies_term_inv in HH1.
            destruct HH1 as [lγ [Hl1 [Hl2 Hl3]]].
            unfold satisfies.
            simpl.
            unfold apply_symbol'. unfold to_Term'.
            constructor.
            unfold to_PreTerm'.
            rewrite <- satisfies_top_bov_cons.
            inversion Hl1; subst; clear Hl1.
            (repeat split).
            {
                simpl.
                rewrite map_length.
                simpl in Hl2.
                rewrite map_length in Hl2.
                ltac1:(lia).
            }
            {
                rewrite Forall_cons in H2.
                destruct H2 as [H2 _].
                destruct lγ using rev_ind.
                {
                    simpl in *.
                    rewrite map_app in Hl2.
                    rewrite app_length in Hl2.
                    simpl in Hl2.
                    ltac1:(lia).
                }
                simpl in *.
                rewrite map_app.
                rewrite zip_with_app.
                {
                    rewrite Forall_app.
                    split.
                    {

                    }
                    {
                        simpl.
                        rewrite Forall_cons.
                        split>[|apply Forall_nil].

                    }
                }
                {
                    rewrite map_length.
                    rewrite map_length in Hl2.
                    rewrite app_length in Hl2.
                    rewrite app_length in Hl2.
                    simpl in Hl2.
                    ltac1:(lia).
                }
                split.
                {
                    simpl. unfold TermOverBuiltin_to_TermOverBoV.
                    unfold TermOver_map. fold (@TermOver_map Σ).
                    simpl.
                    destruct a.
                    {
                        simpl in *.
                        destruct a; simpl in *.
                        {
                            exact Ht.
                        }
                        {
                            destruct (decide (h = x)).
                            {
                                subst. simpl in *.
                                destruct t; simpl in *.
                                {
                                    clear -Ht HH2.
                                    ltac1:(exfalso).
                                    destruct ψ.
                                    {
                                        simpl in *.
                                        inversion Ht; subst; clear Ht.
                                    }
                                }
                                apply IHl.
                            }
                            {

                            }
                        }
                    }
                    (* specialize (IHl H2). clear H2. *)
                    eapply H1.
                    specialize (H1 t Ht).
                    simpl.
                }
            }
        }
    }
Qed.
*)
(*
Lemma satisfies_subst_iff_psi_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    (γ : TermOver builtin_value)
    :
    h ∈ vars_of_to_l2r φ ->
    satisfies ρ γ (TermOverBoV_subst φ h ψ)  ->
    satisfies ρ γ ψ ->
    φ = t_over (bov_variable h)
.
Proof.
    intros H1 H2 H3.
    destruct φ.
    {
        destruct a.
        {
            simpl in *. inversion H1.
        }
        {
            simpl in *.
            inversion H1; subst; clear H1;
            try reflexivity.
            inversion H4.
        }
    }
    {
        ltac1:(exfalso).
        simpl in *.
        destruct γ.
        {
            inversion H2.
        }
        apply satisfies_term_inv in H2.
        destruct H2 as [ly [H'1 [H'2 H'3]]].
        inversion H'1; subst; clear H'1.
        rewrite elem_of_list_In in H1.
        rewrite in_concat in H1.
        destruct H1 as [x [Hx1 Hx2]].
        rewrite <- elem_of_list_In in Hx1.
        ltac1:(replace map with (@fmap _ list_fmap) in Hx1 by reflexivity).
        rewrite <- elem_of_list_In in Hx2.
        rewrite elem_of_list_lookup in Hx1.
        destruct Hx1 as [i Hi].
        rewrite list_lookup_fmap in Hi.
        destruct (l !! i) eqn:Heq.
        {
            assert (H: i < length ly).
            {
                rewrite map_length in H'2.
                rewrite <- H'2.
                apply lookup_lt_Some in Heq.
                exact Heq.
            }
            rewrite <- lookup_lt_is_Some in H.
            unfold is_Some in H.
            destruct H as [y Hy].
            simpl in Hi. inversion Hi; subst; clear Hi.
            assert (Hlen1 := Heq).
            assert (Hlen2 := Hy).
            apply lookup_lt_Some in Hlen1.
            apply lookup_lt_Some in Hlen2.
            apply take_drop_middle in Heq.
            apply take_drop_middle in Hy.
            rewrite <- Heq in H'2.
            rewrite <- Heq in H'3.
            clear Heq.
            rewrite <- Hy in H'3.
            rewrite map_app in H'3.
            rewrite zip_with_app in H'3.
            {

                rewrite Forall_app in H'3.
                destruct H'3 as [H'31 H'32].
                simpl in H'32.
                rewrite Forall_cons in H'32.
                destruct H'32 as [H'32 H'33].
                clear H'31 H'33 Hy Hlen1 Hlen2 H'2.
            }
            {
                rewrite map_length.
                rewrite take_length.
                rewrite take_length.
                rewrite map_length in H'2.
                rewrite app_length in H'2.
                simpl in *.
                rewrite take_length in H'2.
                ltac1:(lia).
            }
        }
        {
            inversion Hi.
        }
    }




    revert ψ γ.
    induction φ; simpl; intros ψ γ Hin Hsat1 Hsat2.
    {
        destruct a.
        {
            inversion Hin.
        }
        {
            destruct (decide (h = x)).
            {
                subst. reflexivity.
            }
            {
                ltac1:(set_solver).
            }
        }
    }
    {
        ltac1:(exfalso).
        revert Hin Hsat1 Hsat2 H.
        induction l; intros Hin Hsat1 Hsat2 H;
            simpl in *.
        {
            inversion Hin.
        }
        {
            destruct (decide (h ∈ vars_of_to_l2r a)) as [Hin'|Hnotin'].
            {
                clear Hin. clear IHl.
                assert (Htmp := size_subst_2 h a ψ Hin').
                destruct γ; simpl in *.
                {
                    inversion Hsat1.
                }
                {
                    inversion Hsat1; subst; clear Hsat1.
                    unfold to_PreTerm' in pf.
                    ltac1:(
                        replace
                            (uglify' (TermOverBoV_subst a h ψ)
                                :: map uglify'
                                (map
                                (λ t'' : TermOver BuiltinOrVar,
                                TermOverBoV_subst t'' h ψ)
                                l)
                            )
                        with (map uglify' (((TermOverBoV_subst a h ψ))::((map
                            (λ t'' : TermOver BuiltinOrVar,
                            TermOverBoV_subst t'' h ψ)
                            l))))
                        in pf
                        by reflexivity
                    ).
                    rewrite <- satisfies_top_bov_cons in pf.
                    destruct pf as [H1 [H2 H3]].
                    subst s0.
                    destruct l0.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    simpl in H2.
                    rewrite Forall_cons in H2.
                    destruct H2 as [H2 H3].
                    rewrite Forall_cons in H.
                    destruct H as [H'1 H'2].
                    destruct ψ.
                    {
                        destruct a0.
                        {
                            inversion Hsat2;
                            subst; clear Hsat2.
                            inversion H5.
                        }
                        {


                        }
                    }
                    specialize (H'1 ψ t Hin' H2).
                }
            }
            {

            }
        }
    }
Qed.
*)

Lemma factor_by_subst_correct'
    {Σ : StaticModel}
    (sz : nat)
    (ρ : Valuation)
    (h : variable)
    (γ : TermOver builtin_value)
    (φ ψ : TermOver BuiltinOrVar)
    : sz >= TermOver_size γ ->
    h ∉ vars_of ρ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    ~ (h ∈ vars_of_to_l2r ψ) ->
    satisfies ρ γ (TermOverBoV_subst φ h ψ) ->
    let xy := factor_by_subst sz ρ h γ φ ψ in
    satisfies ρ xy.2 ψ /\
    satisfies (<[h := (uglify' xy.2)]>ρ) xy.1 φ
.
Proof.
    induction sz; intros Hsz.
    {
        destruct γ; simpl in Hsz; ltac1:(lia).
    }
    intros Hnotinρ Hlf Hnotinψ Hsat.
    unfold factor_by_subst. fold (@factor_by_subst Σ).
    simpl.
    destruct (matchesb ρ (uglify' γ) (uglify' ψ)) eqn:Heqmb.
    {
        simpl.
        split.
        {
            apply matchesb_implies_satisfies in Heqmb.
            unfold satisfies; simpl.
            apply Heqmb.
        }
        {
            
        }
    }
    {
        destruct γ, φ; simpl in *.
        {
            {

            }
        }
        {

        }
        {

        }
        {

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
    h ∉ vars_of ρ ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    ~ (h ∈ vars_of_to_l2r ψ) ->
    satisfies
        ρ
        γ
        (TermOverBoV_subst φ h ψ)
        ->
    {  γ1 : TermOver builtin_value &
        ((satisfies ρ γ1 ψ) *
         {γ0 : TermOver builtin_value &
            satisfies (<[h:=(uglify' γ1)]>ρ) γ0 φ} )%type }    .
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
            (* FIXME I have to get rid of the quantifier over γ1 *)
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