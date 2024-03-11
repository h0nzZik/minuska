From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    semantics_properties
    basic_matching
    varsof
    syntax_properties
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
    (h : variable) (* occurs once in `c` *)
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

(* This should not be used *)
(*
Definition down
    {Σ : StaticModel}
    {A : Type}
    (topSymbol : symbol)
    (ctrl data : TermOver A)
    : TermOver A
:=
    t_term topSymbol [ctrl;data]
.
*)

Definition down2
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (continuationVariable : variable)
    (ctrl data : TermOver BuiltinOrVar)
    : TermOver BuiltinOrVar
:=
    t_term topSymbol
        [
            (t_term cseqSymbol
                [
                    ctrl;
                    t_over (bov_variable continuationVariable)
                ]
            );
            data
        ]
.

Definition down2E
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (continuationVariable : variable)
    (ctrl data : TermOver Expression)
    : TermOver Expression
:=
    t_term topSymbol
        [
            (t_term cseqSymbol
                [
                    ctrl;
                    t_over (ft_variable continuationVariable)
                ]
            );
            data
        ]
.

Definition downC
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (ctrl data continuation : TermOver builtin_value)
    : TermOver builtin_value
:=
    t_term topSymbol
        [
            (t_term cseqSymbol
                [
                    ctrl;
                    continuation
                ]
            );
            data
        ]
.

Definition compile' {Σ : StaticModel} {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable)
    (isValue : Expression -> (list SideCondition))
    (d : MinusL_Decl Act)
    : (list (RewritingRule Act))
:=
    match d with
    | mld_rewrite _ lc ld a rc rd scs => [
        ({|
            fr_from := uglify' (down2 topSymbol cseqSymbol continuationVariable lc ld) ;
            fr_to := uglify' (down2E topSymbol cseqSymbol continuationVariable rc rd) ;
            fr_scs := scs ;
            fr_act := a;
        |})
        ]
    | mld_context _ c h Hh scs =>
        let vars := vars_of_to_l2r c in
        let contVariable := fresh (h::vars) in
        let dataVariable := fresh (h::contVariable::vars) in
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
    (continuationVariable : variable)
    : CompileT :=
    fun D => concat (map (
        compile' invisible_act topSymbol cseqSymbol holeSymbol continuationVariable (mlld_isValue Act D)
        ) (mlld_decls Act D))
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

(* The proof if the same as for satisfies_top_bov_cons*)
Lemma satisfies_top_bov_cons_expr
    {Σ : StaticModel}
    (ρ : Valuation)
    (topSymbol topSymbol' : symbol)
    (states : list (TermOver builtin_value))
    (lds : list (TermOver Expression))
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

Lemma satisfies_var_expr
    {Σ : StaticModel}
    (ρ : Valuation)
    x γ:
    ρ !! x = Some (uglify' γ) ->
    satisfies ρ γ (t_over (ft_variable x))
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


Lemma satisfies_term_expr_inv
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (s : symbol)
    (l : list (TermOver Expression))
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

                    revert xy1 H3.
                    induction l using rev_ind; simpl in *; intros xy1 H3.
                    {
                        inversion H3. reflexivity.
                    }
                    {

                        rewrite map_app in H3.
                        rewrite fold_left_app in H3.
                        simpl in H3.
                        ltac1:(case_match).
                        {
                            apply (f_equal prettify) in H.
                            rewrite (cancel prettify uglify') in H.
                            subst x.
                            inversion H3; subst; clear H3; simpl in *.
                            {
                                apply IHl.
                                apply H4.
                            }
                            {
                                apply IHl.
                                apply H4.
                            }
                        }
                        {
                            apply (f_equal prettify) in H.
                            rewrite (cancel prettify uglify') in H.
                            subst x.
                            inversion H3; subst; clear H3; simpl in *.
                            {
                                apply IHl.
                                apply H4.
                            }
                            {
                                apply IHl.
                                apply H4.
                            }
                        }
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
                        simpl in H3.
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
                        simpl in H3.
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

Lemma h_in_l_impl_length_filter_l_gt_1
    {T : Type}
    (P : T -> Prop)
    {_dP: forall x, Decision (P x)}
    (l : list T)
    (h : T)
    :
    h ∈ l ->
    P h ->
    length (filter P l) >= 1
.
Proof.
    induction l; simpl.
    {
        intros HH. inversion HH.
    }
    {
        intros HH1 HH2.
        rewrite elem_of_cons in HH1.
        destruct HH1 as [HH1|HH1].
        {
            subst. rewrite filter_cons.
            destruct (decide (P a))>[|ltac1:(contradiction)].
            simpl.
            ltac1:(lia).
        }
        {
            specialize (IHl HH1 HH2).
            rewrite filter_cons.
            ltac1:(case_match).
            {
                simpl. ltac1:(lia).
            }
            {
                exact IHl.
            }
        }
    }
Qed.


Lemma length_filter_l_1_impl_h_in_l'
    {T : Type}
    (P : T -> Prop)
    {_dP: forall x, Decision (P x)}
    (l : list T)
    :
    length (filter P l) = 1 ->
    exists h, 
    h ∈ l /\ P h
.
Proof.
    intros H.
    induction l; simpl in *.
    { inversion H. }
    {
        rewrite filter_cons in H.
        destruct (decide (P a)).
        {
            subst. exists a. split. left. assumption.
        }
        {
            specialize (IHl H).
            destruct IHl as [h [H1h H2h]].
            exists h. split.
            right. assumption. assumption.
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
                                            (* TODO this should be extracted somehow somewhere *)
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
                            (* TODO reuse in the N3=N3' case *)
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
                                    intros HContra.
                                    rewrite map_app in Hfilter.
                                    rewrite concat_app in Hfilter.
                                    assert (H_i0_lt_i: i0 < i).
                                    {
                                        apply lookup_lt_Some in Hx1.
                                        rewrite take_length in Hx1.
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
                                            inversion Hx1; subst; clear Hx1.
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
                                            inversion Hx1.
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
                        }

                        ltac1:(assert(N3 = N3')).
                        {
                            subst N3 N3'.

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
                                    clear Hx2.
                                    intros HContra.
                                    rewrite map_app in Hfilter.
                                    rewrite concat_app in Hfilter.
                                    (*
                                    assert (H_i0_lt_i: i0 < i).
                                    {
                                        apply lookup_lt_Some in Hx1.
                                        rewrite take_length in Hx1.
                                        ltac1:(lia).
                                    }
                                    *)
                                    simpl in Hfilter.
                                    rewrite filter_app in Hfilter.
                                    rewrite filter_app in Hfilter.
                                    simpl in Hfilter.
                                    rewrite app_length in Hfilter.
                                    rewrite app_length in Hfilter.
                                    assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (drop (S i) l))))).
                                    {
                                        destruct ((drop (S i) l) !! i0) eqn:Heq.
                                        {
                                            assert (Heq' := Heq).
                                            apply take_drop_middle in Heq.
                                            rewrite <- Heq.
                                            rewrite map_app.
                                            rewrite concat_app.
                                            rewrite filter_app.
                                            simpl.
                                            rewrite filter_app.
                                            inversion Hx1; subst; clear Hx1.
                                            (*
                                            apply lookup_take_Some in Heq'.
                                            inversion Hx1; subst; clear Hx1.
                                            destruct Heq' as [Heq'1 _].
                                            inversion Heq'1; subst; clear Heq'1.
                                            *)
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
                                            inversion Hx1.
                                        }
                                    }
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
                            }
                        }

                        ltac1:(lia).
                    }
                    {
                        rewrite take_length.
                        rewrite take_length.
                        ltac1:(lia).
                    }
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
    }
Qed.

Lemma list_filter_Forall_not
    {T : Type}
    (P : T -> Prop)
    {_dP : forall x, Decision (P x)}
    (l : list T)
    :
    Forall (fun x => not (P x)) l ->
    filter P l = []
.
Proof.
    induction l; simpl; intros H.
    {
        reflexivity.
    }
    {
        apply Forall_cons in H.
        destruct H as [H1 H2].
        specialize (IHl H2). clear H2.
        rewrite filter_cons.
        destruct (decide (P a)).
        {
            ltac1:(contradiction).
        }
        apply IHl.
    }
Qed.


Lemma list_filter_Forall_all
    {T : Type}
    (P : T -> Prop)
    {_dP : forall x, Decision (P x)}
    (l : list T)
    :
    Forall P l ->
    filter P l = l
.
Proof.
    induction l; simpl; intros H.
    {
        reflexivity.
    }
    {
        apply Forall_cons in H.
        destruct H as [H1 H2].
        specialize (IHl H2). clear H2.
        rewrite filter_cons.
        destruct (decide (P a)).
        {
            rewrite IHl. reflexivity.
        }
        ltac1:(contradiction).
    }
Qed.

Lemma TermOver_size_not_zero
    {Σ : StaticModel}
    {A : Type}
    (t : TermOver A)
    : TermOver_size t <> 0
.
Proof.
    destruct t; simpl; ltac1:(lia).
Qed.

Lemma TermOverBoV_subst_once_size
    {Σ : StaticModel}
    (h : variable)
    (φ ψ : TermOver BuiltinOrVar)
    :
    h ∉ vars_of (uglify' ψ) ->
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    TermOver_size (TermOverBoV_subst φ h ψ) = Nat.pred (TermOver_size φ + TermOver_size ψ)
.
Proof.
    induction φ; simpl; intros Hnotinψ Hexactlyonce.
    {
        destruct a.
        {
            simpl in *. ltac1:(lia).
        }
        {
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h = x)).
            {
                simpl in *. reflexivity.
            }
            {
                simpl in *. ltac1:(lia).
            }
        }
    }
    {
        simpl in *.
        rewrite sum_list_with_compose.
        unfold compose.
        do 2 (rewrite sum_list_with_S).
        do 2 (rewrite map_length).
        do 2 (rewrite sum_list_fmap).
        rewrite fmap_length.

        assert (Hconcat: h ∈ concat (map vars_of_to_l2r l)).
        {
            clear -Hexactlyonce.
            induction l; simpl in *.
            { ltac1:(lia). }
            {
                rewrite filter_app in Hexactlyonce.
                rewrite app_length in Hexactlyonce.
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

        rewrite <- elem_of_list_In in H2x.
        rewrite elem_of_list_lookup in H2x.
        destruct H2x as [i Hi].

        rewrite <- elem_of_list_In in H2x0.
        assert (H2x0' := H2x0).
        rewrite elem_of_list_lookup in H2x0.
        destruct H2x0 as [j Hj].
        apply take_drop_middle in Hj.
        rewrite <- Hj.
        rewrite app_length.
        rewrite sum_list_with_app.
        rewrite map_app.
        rewrite sum_list_with_app.
        simpl.

        rewrite <- Hj in Hexactlyonce.
        rewrite map_app in Hexactlyonce. simpl in Hexactlyonce.
        rewrite concat_app in Hexactlyonce. simpl in Hexactlyonce.
        do 2 (rewrite filter_app in Hexactlyonce).
        do 2 (rewrite app_length in Hexactlyonce).
        simpl in Hexactlyonce.
        
        assert(Hnotintake: forall x2, x2 ∈ take j l -> h ∉ vars_of_to_l2r x2).
        {
            intros x2 Hx2.
            intros HContra.
            
            assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (take j l))))).
            {
                rewrite elem_of_list_lookup in Hx2.
                destruct Hx2 as [i0 Hx2].
                
                assert (Heq' := Hx2).
                apply take_drop_middle in Heq'.
                rewrite <- Heq'.
                rewrite map_app.
                rewrite concat_app.
                rewrite filter_app.
                simpl.
                rewrite filter_app.
                rewrite app_length.
                rewrite app_length.
                rewrite elem_of_list_lookup in HContra.
                destruct HContra as [k Hk].
                apply take_drop_middle in Hk.
                rewrite <- Hk.
                rewrite filter_app.
                rewrite app_length.
                rewrite filter_cons.
                destruct (decide (h = h))>[|ltac1:(contradiction)].
                simpl.
                ltac1:(lia).
            }
            apply take_drop_middle in Hi.
            rewrite <- Hi in Hexactlyonce.
            rewrite filter_app in Hexactlyonce.
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h=h))>[|ltac1:(contradiction)].
            rewrite app_length in Hexactlyonce.
            simpl in Hexactlyonce.
            ltac1:(lia).
        }

        assert(Hnotindrop: forall x2, x2 ∈ drop (S j) l -> h ∉ vars_of_to_l2r x2).
        {
            intros x2 Hx2.
            intros HContra.
            simpl in Hexactlyonce.
            assert(Htmp: 1 <= length (filter (eq h) (concat (map vars_of_to_l2r (drop (S j) l))))).
            {
                rewrite elem_of_list_lookup in Hx2.
                destruct Hx2 as [i0 Hx2].
                
                assert (Heq' := Hx2).
                apply take_drop_middle in Heq'.
                rewrite <- Heq'.
                rewrite map_app.
                rewrite concat_app.
                rewrite filter_app.
                simpl.
                rewrite filter_app.
                rewrite app_length.
                rewrite app_length.
                rewrite elem_of_list_lookup in HContra.
                destruct HContra as [k Hk].
                apply take_drop_middle in Hk.
                rewrite <- Hk.
                rewrite filter_app.
                rewrite app_length.
                rewrite filter_cons.
                destruct (decide (h = h))>[|ltac1:(contradiction)].
                simpl.
                ltac1:(lia).
            }
            apply take_drop_middle in Hi.
            rewrite <- Hi in Hexactlyonce.
            rewrite filter_app in Hexactlyonce.
            rewrite filter_cons in Hexactlyonce.
            destruct (decide (h=h))>[|ltac1:(contradiction)].
            rewrite app_length in Hexactlyonce.
            simpl in Hexactlyonce.
            ltac1:(lia).
        }

        assert (HH1: (sum_list_with TermOver_size
                (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ)
                (take j l))  )
                = sum_list_with TermOver_size (take j l) ).
        {
            apply sum_list_with_eq_pairwise.
            {
                rewrite map_length.
                reflexivity.
            }
            {
                intros i0 x1 x2 Hx1 Hx2.
                ltac1:(replace map with (@fmap _ list_fmap) in Hx1 by reflexivity).
                rewrite list_lookup_fmap in Hx1.
                rewrite Hx2 in Hx1. simpl in Hx1. inversion Hx1; subst; clear Hx1.
                rewrite subst_notin.
                {
                    reflexivity.
                }
                {
                    intros HContra.
                    specialize (Hnotintake x2).
                    ltac1:(ospecialize (Hnotintake _)).
                    {
                        rewrite elem_of_list_lookup.
                        exists i0. exact Hx2.
                    }
                    apply Hnotintake. apply HContra.
                }
            }
        }

        assert (HH2: (sum_list_with TermOver_size
                (map (λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ)
                (drop (S j) l))  )
                = sum_list_with TermOver_size (drop (S j) l) ).
        {
            apply sum_list_with_eq_pairwise.
            {
                rewrite map_length.
                reflexivity.
            }
            {
                intros i0 x1 x2 Hx1 Hx2.
                ltac1:(replace map with (@fmap _ list_fmap) in Hx1 by reflexivity).
                rewrite list_lookup_fmap in Hx1.
                rewrite Hx2 in Hx1. simpl in Hx1. inversion Hx1; subst; clear Hx1.
                rewrite subst_notin.
                {
                    reflexivity.
                }
                {

                    intros HContra.
                    specialize (Hnotindrop x2).
                    ltac1:(ospecialize (Hnotindrop _)).
                    {
                        rewrite elem_of_list_lookup.
                        exists i0. exact Hx2.
                    }
                    apply Hnotindrop. apply HContra.
                }
            }
        }

        rewrite HH1. clear HH1.
        rewrite HH2. clear HH2.
        remember (sum_list_with TermOver_size (take j l) ) as N1.
        remember (sum_list_with TermOver_size (drop (S j) l) ) as N2.
        rewrite take_length.
        rewrite drop_length.

        rewrite Forall_forall in H.
        specialize (H x0 H2x0' Hnotinψ).

        assert (Hnotintake': length (filter (eq h) (concat (map vars_of_to_l2r (take j l)))) = 0).
        {
            rewrite length_zero_iff_nil.
            apply list_filter_Forall_not.
            rewrite Forall_forall.
            intros x Hx HContra.
            subst x.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [x [H1x H2x]].
            rewrite in_map_iff in H1x.
            destruct H1x as [x1 [H1x1 H2x1]].
            rewrite <- elem_of_list_In in H2x.
            subst x.
            rewrite <- elem_of_list_In in H2x1.
            specialize (Hnotintake _ H2x1).
            apply Hnotintake. apply H2x.
        }

        assert (Hnotindrop': length (filter (eq h) (concat (map vars_of_to_l2r (drop (S j) l)))) = 0).
        {
            rewrite length_zero_iff_nil.
            apply list_filter_Forall_not.
            rewrite Forall_forall.
            intros x Hx HContra.
            subst x.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [x [H1x H2x]].
            rewrite in_map_iff in H1x.
            destruct H1x as [x1 [H1x1 H2x1]].
            rewrite <- elem_of_list_In in H2x.
            subst x.
            rewrite <- elem_of_list_In in H2x1.
            specialize (Hnotindrop _ H2x1).
            apply Hnotindrop. apply H2x.
        }
        specialize (H ltac:(lia)).
        rewrite H.
        assert (Htmp1 := TermOver_size_not_zero x0).
        ltac1:(lia).
    }
Qed.

Lemma count_one_split
    {T : Type}
    (P : T -> Prop)
    (_dP : forall x, Decision (P x))
    (l : list T)
    :
    length (filter P l) = 1 ->
    exists (la : list T) (b : T) (lc : list T),
    l = la ++ b::lc
    /\ P b
    /\ Forall (fun x => not (P x)) la
    /\ Forall (fun x => not (P x)) lc
.
Proof.
    remember (list_find P l) as lf.
    destruct lf.
    {
        symmetry in Heqlf.
        destruct p.
        apply list_find_Some in Heqlf.
        intros HH.
        destruct Heqlf as [H1 [H2 H3]].
        apply take_drop_middle in H1.
        exists (take n l).
        exists t.
        exists (drop (S n) l).
        split.
        {
            symmetry. exact H1.
        }
        split>[exact H2|].
        split.
        {
            rewrite Forall_forall.
            intros x Hx.
            rewrite elem_of_list_lookup in Hx.
            destruct Hx as [i Hi].
            rewrite lookup_take_Some in Hi.
            destruct Hi as [Hi H'i].
            eapply H3.
            { apply Hi. }
            { apply H'i. }
        }
        {
            rewrite Forall_forall.
            intros x Hx HContra.
            rewrite elem_of_list_lookup in Hx.
            destruct Hx as [i Hi].
            apply take_drop_middle in Hi.
            rewrite <- Hi in H1.
            rewrite <- H1 in HH.
            clear H1 Hi.
            rewrite filter_app in HH.
            rewrite filter_cons in HH.
            destruct (decide (P t))>[|ltac1:(contradiction)].
            rewrite filter_app in HH.
            rewrite filter_cons in HH.
            destruct (decide (P x))>[|ltac1:(contradiction)].
            rewrite app_length in HH. simpl in HH.
            rewrite app_length in HH. simpl in HH.
            ltac1:(lia).
        }
    }
    {
        symmetry in Heqlf.
        apply list_find_None in Heqlf.
        intros Hlength.
        apply length_filter_l_1_impl_h_in_l' in Hlength.
        destruct Hlength as [h [H1h H2h]].
        rewrite Forall_forall in Heqlf.
        ltac1:(exfalso).
        ltac1:(naive_solver).
    }
Qed.

Lemma length_filter_eq__eq__length_filter_in__zero
    {T : Type}
    {_edT: EqDecision T}
    (h : T)
    (l : list (list T))
    :
    length (filter (eq h) (concat l)) = 0 ->
    length (filter (elem_of h) l) = 0
.
Proof.
    induction l; simpl; intros HH.
    {
        ltac1:(lia).
    }
    {
        rewrite filter_app in HH.
        rewrite filter_cons.
        destruct (decide (h ∈ a)) as [Hin|Hnotin].
        {
            simpl. rewrite app_length in HH.
            assert(Htmp := h_in_l_impl_length_filter_l_gt_1 (eq h) a h Hin eq_refl).
            ltac1:(exfalso).
            ltac1:(lia).
        }
        {
            simpl. rewrite app_length in HH.
            apply IHl. ltac1:(lia).
        }
    }
Qed.


Lemma length_filter_eq__eq__length_filter_in__one
    {T : Type}
    {_edT: EqDecision T}
    (h : T)
    (l : list (list T))
    :
    length (filter (eq h) (concat l)) = 1 ->
    length (filter (elem_of h) l) = 1
.
Proof.
    {
        induction l; simpl; intros HH.
        {
            ltac1:(lia).
        }
        {
            rewrite filter_cons.
            rewrite filter_app in HH.
            rewrite app_length in HH.
            destruct (decide (h ∈ a)) as [Hin|Hnotin].
            {
                assert(Htmp := h_in_l_impl_length_filter_l_gt_1 (eq h) a h Hin eq_refl).
                simpl in *.
                assert (length (filter (eq h) (concat l)) = 0).
                {
                    ltac1:(lia).
                }
                apply length_filter_eq__eq__length_filter_in__zero in H.
                rewrite H.
                reflexivity.                
            }
            {
                apply IHl. clear IHl.
                assert (length (filter (eq h) a) = 0).
                {
                    clear -Hnotin.
                    induction a.
                    {
                        simpl. reflexivity.
                    }
                    {
                        rewrite elem_of_cons in Hnotin.
                        apply Decidable.not_or in Hnotin.
                        destruct Hnotin as [Hnotin1 Hnotin2].
                        rewrite filter_cons.
                        destruct (decide (h = a))>[ltac1:(subst;contradiction)|].
                        apply IHa. exact Hnotin2.
                    }
                }
                ltac1:(lia).
            }
        }
    }
Qed.

Lemma filter_fmap
    {T1 T2: Type}
    (f : T1 -> T2)
    (P : T2 -> Prop)
    {_decP : forall x, Decision (P x)}
    {_decfP : forall x, Decision ((P ∘ f) x)}
    (l : list T1)
    :
    filter P (f <$> l) = f <$> (filter (P ∘ f) l)
.
Proof.
    induction l.
    {
        simpl. rewrite filter_nil. reflexivity.
    }
    {
        rewrite filter_cons.
        rewrite fmap_cons.
        rewrite filter_cons.
        rewrite IHl.
        unfold compose.
        simpl in *.
        ltac1:(repeat case_match); try (ltac1:(contradiction)).
        {
            reflexivity.
        }
        {
            reflexivity.
        }
    }
Qed.

Lemma on_a_shared_prefix
    {T : Type}
    (_edT : EqDecision T)
    (b : T)
    (l1 l2 l1' l2' : list T)
    :
    b ∉ l1 ->
    b ∉ l1' ->
    l1 ++ b::l2 = l1' ++ b::l2' ->
    l1 = l1'
.
Proof.
    revert l1'.
    induction l1; simpl; intros l1' H1 H2 H3.
    {
        destruct l1'; simpl in *.
        { reflexivity. }
        {
            ltac1:(exfalso).
            inversion H3; subst; clear H3.
            apply H2. clear H2.
            rewrite elem_of_cons. left. reflexivity.
        }
    }
    {
        destruct l1'.
        {
            ltac1:(exfalso).
            inversion H3; subst; clear H3.
            apply H1. clear H1.
            rewrite elem_of_cons. left. reflexivity.
        }
        {
            rewrite elem_of_cons in H1.
            rewrite elem_of_cons in H2.
            apply Decidable.not_or in H1.
            apply Decidable.not_or in H2.
            destruct H1 as [H11 H12].
            destruct H2 as [H21 H22].
            simpl in H3. inversion H3; subst; clear H3.
            specialize (IHl1 l1' H12 H22 H1).
            subst l1'.
            reflexivity.
        }
    }
Qed.

Lemma vars_of_to_l2r_subst
    {Σ : StaticModel}
    (φ ψ : TermOver BuiltinOrVar)
    (h : variable)
    :
    length (filter (eq h) (vars_of_to_l2r φ)) = 1 ->
    h ∉ vars_of_to_l2r ψ ->
    vars_of_to_l2r (TermOverBoV_subst φ h ψ)
    ≡ₚ ((filter (fun x => x <> h) (vars_of_to_l2r φ)) ++ (vars_of_to_l2r ψ))
.
Proof.
    intros Hinφ Hnotinψ.
    induction φ; simpl.
    {
        destruct a; simpl in *.
        {
            ltac1:(lia).
        }
        {
            rewrite filter_cons in Hinφ.
            rewrite filter_cons.
            destruct (decide (h = x)); simpl in *.
            {
                subst x.
                destruct (decide (h<>h))>[ltac1:(contradiction)|].
                rewrite filter_nil. simpl. reflexivity.
            }
            {
                ltac1:(lia).
            }
        }
    }
    {
        simpl in *.
        assert (H'inφ := Hinφ).
        assert (Hlen: length (filter (fun x => h ∈ vars_of_to_l2r x) l) = 1).
        {
            apply length_filter_eq__eq__length_filter_in__one in H'inφ.
            ltac1:(replace map with (@fmap _ list_fmap) in H'inφ by reflexivity).
            ltac1:(unshelve(erewrite filter_fmap in H'inφ)).
            {
                intros x.
                unfold compose.
                apply _.
            }
            rewrite fmap_length in H'inφ.
            apply H'inφ.
        }
        apply count_one_split in Hlen.
        destruct Hlen as [la1 [b1 [lc1 [HH'1 [HH'2 [HH'3 HH'4]]]]]].

        assert (Hvl := HH'1).
        apply (f_equal (fmap vars_of_to_l2r)) in Hvl.
        rewrite fmap_app in Hvl.
        rewrite fmap_cons in Hvl.
        ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
        rewrite Hvl.
        rewrite concat_app.
        rewrite concat_cons.
        rewrite filter_app.
        rewrite filter_app.
        rewrite HH'1.
        rewrite fmap_app.
        rewrite fmap_cons.
        rewrite fmap_app.
        rewrite concat_app.
        rewrite fmap_cons.
        rewrite concat_cons.

        assert (HJ1: Forall (λ x : variable, h ≠ x) (concat (vars_of_to_l2r <$> la1))).
        {
            rewrite Forall_forall.
            rewrite Forall_forall in HH'3.
            intros x Hx.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [l0 [H1 H2]].
            rewrite <- elem_of_list_In in H2.
            rewrite <- elem_of_list_In in H1.
            rewrite elem_of_list_fmap in H1.
            destruct H1 as [t [H1t H2t]].
            subst l0.
            specialize (HH'3 t H2t).
            clear -HH'3 H2.
            intros HContra. subst.
            apply HH'3. apply H2.
        }

        assert (HJ2 : Forall (λ x : variable, h ≠ x) (concat (vars_of_to_l2r <$> lc1))).
        {
            rewrite Forall_forall.
            rewrite Forall_forall in HH'4.
            intros x Hx.
            rewrite elem_of_list_In in Hx.
            rewrite in_concat in Hx.
            destruct Hx as [l0 [H1 H2]].
            rewrite <- elem_of_list_In in H2.
            rewrite <- elem_of_list_In in H1.
            rewrite elem_of_list_fmap in H1.
            destruct H1 as [t [H1t H2t]].
            subst l0.
            specialize (HH'4 t H2t).
            clear -HH'4 H2.
            intros HContra. subst.
            apply HH'4. apply H2.
        }


        rewrite HH'1 in H.
        rewrite Forall_app in H.
        rewrite Forall_cons in H.
        destruct H as [IHH1 [IH2 IH3]].


        ltac1:(ospecialize (IH2 _)).
        {

            rewrite HH'1 in H'inφ.
            ltac1:(replace map with (@fmap _ list_fmap) in H'inφ by reflexivity).
            rewrite fmap_app in H'inφ.
            rewrite fmap_cons in H'inφ.
            rewrite concat_app in H'inφ.
            rewrite concat_cons in H'inφ.
            rewrite filter_app in H'inφ.
            rewrite filter_app in H'inφ.
            rewrite app_length in H'inφ.
            rewrite app_length in H'inφ.
            assert (Hfil1 : length (filter (eq h) (concat (vars_of_to_l2r <$> la1))) = 0).
            {
                rewrite list_filter_Forall_not.
                { reflexivity. }
                {
                    assumption.
                }
            }
            assert (Hfil2 : length (filter (eq h) (concat (vars_of_to_l2r <$> lc1))) = 0).
            {
                rewrite list_filter_Forall_not.
                { reflexivity. }
                {
                    assumption.
                }
            }
            ltac1:(lia).
        }
        rewrite IH2. clear IH2.

        assert (Heq1: ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> la1) = la1).
        {
            clear -HH'3.
            induction la1.
            { reflexivity. }
            {
                rewrite Forall_cons in HH'3.
                destruct HH'3 as [H1 H2].
                specialize (IHla1 H2).
                rewrite fmap_cons.
                rewrite IHla1.
                rewrite subst_notin.
                { reflexivity. }
                { apply H1. }
            }
        }

        assert (Heq2: ((λ t'' : TermOver BuiltinOrVar, TermOverBoV_subst t'' h ψ) <$> lc1) = lc1).
        {
            clear -HH'4.
            induction lc1.
            { reflexivity. }
            {
                rewrite Forall_cons in HH'4.
                destruct HH'4 as [H1 H2].
                specialize (IHlc1 H2).
                rewrite fmap_cons.
                rewrite IHlc1.
                rewrite subst_notin.
                { reflexivity. }
                { apply H1. }
            }
        }
        rewrite Heq1. rewrite Heq2. clear Heq1 Heq2.

        assert (HJ1': filter (λ x : variable, x ≠ h) (concat (vars_of_to_l2r <$> la1)) = concat (vars_of_to_l2r <$> la1)).
        {
            clear -HJ1.
            rewrite list_filter_Forall_all.
            { reflexivity. }
            {
                eapply List.Forall_impl>[|apply HJ1].
                intros x Ha. simpl in Ha. ltac1:(congruence).
            }
        }

        assert (HJ2': filter (λ x : variable, x ≠ h) (concat (vars_of_to_l2r <$> lc1)) = concat (vars_of_to_l2r <$> lc1)).
        {
            clear -HJ2.
            rewrite list_filter_Forall_all.
            { reflexivity. }
            {
                eapply List.Forall_impl>[|apply HJ2].
                intros x Ha. simpl in Ha. ltac1:(congruence).
            }
        }

        rewrite HJ1'. clear HJ1 HJ1'.
        rewrite HJ2'. clear HJ2 HJ2'.
        clear.
        ltac1:(solve_Permutation).
    }
Qed.

Lemma sum_list_with_perm
    {T : Type}
    (f : T -> nat)
    (l1 l2 : list T)
    :
    l1 ≡ₚ l2 ->
    sum_list_with f l1 = sum_list_with f l2
.
Proof.
    intros H.
    induction H.
    {
        reflexivity.
    }
    {
        simpl. rewrite IHPermutation. reflexivity.
    }
    {
        simpl. ltac1:(lia).
    }
    {
        ltac1:(congruence).
    }
Qed.

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
    revert γ φ.
    induction sz; intros γ φ Hsz.
    {
        destruct γ; simpl in Hsz; ltac1:(lia).
    }
    {
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
                apply matchesb_implies_satisfies in Heqmb.
                assert (Heqmb': satisfies ρ γ ψ).
                {
                    unfold satisfies; simpl.
                    apply Heqmb.
                }

                assert (Htmp2 := TermOver_size_not_zero ψ).
                assert (Htmp3 := TermOver_size_not_zero φ).
                assert (Hsat' := Hsat).
                apply concrete_is_larger_than_symbolic in Hsat'.
                apply concrete_is_larger_than_symbolic in Heqmb'.

                unfold delta_in_val in Hsat'.
                assert (Hperm := vars_of_to_l2r_subst φ ψ h Hlf Hnotinψ).
                apply sum_list_with_perm with (f := (size_of_var_in_val ρ)) in Hperm.
                rewrite Hperm in Hsat'. clear Hperm.
                rewrite TermOverBoV_subst_once_size in Hsat'.
                {

                    rewrite sum_list_with_app in Hsat'.
                    unfold delta_in_val in Heqmb'.
                    assert (Hszφ: TermOver_size φ = 1) by ltac1:(lia).
                    clear Hsat.
                    destruct φ.
                    {
                        simpl in *. clear Hszφ.
                        clear Htmp3.
                        destruct a.
                        {
                            simpl in *. ltac1:(lia).
                        }
                        simpl in *. rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst.
                            clear Heqmb' Hsat' Htmp2. clear Hlf.
                            simpl.
                            apply satisfies_var.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in *. ltac1:(lia).
                        }
                    }
                    {
                        simpl in Hszφ.
                        destruct l.
                        {
                            simpl in *. clear Hszφ Htmp3 Heqmb' Hsat'.
                            ltac1:(lia).
                        }
                        {
                            simpl in *.
                            ltac1:(lia).
                        }
                    }
                }
                {
                    rewrite <- vars_of_uglify.
                    assumption.
                }
                {
                    assumption.
                }
            }
        }
        {
            destruct γ.
            {
                destruct φ.
                {
                    destruct a0; simpl in *.
                    {
                        ltac1:(lia).
                    }
                    {
                        rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst. simpl in *. clear Hlf.
                            split>[exact Hsat|]. clear IHsz.
                            apply satisfies_var.
                            simpl.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in Hlf. inversion Hlf.
                        }
                    }
                }
                {
                    simpl in *.
                    apply satisfies_term_inv in Hsat.
                    destruct Hsat as [? [HContra ?]].
                    inversion HContra.
                }
            }
            {
                simpl in *.
                destruct φ.
                {
                    simpl in *.
                    destruct a.
                    {
                        simpl in *. ltac1:(lia).
                    }
                    {
                        simpl in *.
                        rewrite filter_cons in Hlf.
                        destruct (decide (h = x)).
                        {
                            subst. simpl in *.
                            clear Hlf.
                            split>[apply Hsat|].
                            apply satisfies_var.
                            unfold Valuation in *.
                            apply lookup_insert.
                        }
                        {
                            simpl in *. ltac1:(lia).
                        }
                    }
                }
                {
                    destruct (list_find (λ φi : TermOver BuiltinOrVar, h ∈ vars_of_to_l2r φi) l0) eqn:Hfind.
                    {
                        destruct p.
                        apply list_find_Some in Hfind.
                        destruct (l !! n) eqn:Hln.
                        {
                            apply satisfies_term_inv in Hsat.
                            destruct Hsat as [lγ [H1 [H2 H3]]].
                            inversion H1; subst; clear H1.
                            simpl in *.
                            fold (@TermOverBoV_subst Σ) in *.
                            rewrite map_length in H2.
                            destruct Hfind as [Hfind1 [Hfind2 Hfind3]].
                            specialize (IHsz t0 t).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                apply take_drop_middle in Hln.
                                rewrite <- Hln in Hsz. simpl in Hsz.
                                rewrite sum_list_with_app in Hsz. simpl in Hsz.
                                ltac1:(lia).
                            }
                            specialize (IHsz Hnotinρ).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                assert (Hlf' := Hlf).
                                apply take_drop_middle in Hfind1.
                                rewrite <- Hfind1 in Hlf.
                                rewrite map_app in Hlf.
                                rewrite map_cons in Hlf.
                                rewrite concat_app in Hlf.
                                rewrite concat_cons in Hlf.
                                rewrite filter_app in Hlf.
                                rewrite filter_app in Hlf.
                                rewrite list_filter_Forall_not in Hlf.
                                {
                                    clear IHsz. simpl in Hlf.
                                    rewrite app_length in Hlf.
                                    ltac1:(rewrite -> list_filter_Forall_not with (l := (concat (map vars_of_to_l2r (drop (S n) l0)))) in Hlf).
                                    {
                                        simpl in Hlf.
                                        rewrite Nat.add_0_r in Hlf.
                                        exact Hlf.
                                    }
                                    {
                                        apply not_Exists_Forall.
                                        { intros ?. apply variable_eqdec. }
                                        {
                                            intros HContra. rewrite Exists_exists in HContra.
                                            destruct HContra as [x [HContra ?]].
                                            subst x.
                                            rewrite elem_of_list_lookup in HContra.
                                            destruct HContra as [j1 HContra].
                                            apply take_drop_middle in HContra.
                                            rewrite elem_of_list_lookup in Hfind2.
                                            destruct Hfind2 as [j2 Hfind2].
                                            apply take_drop_middle in Hfind2.
                                            rewrite <- Hfind2 in Hlf.
                                            rewrite <- HContra in Hlf.
                                            clear -Hlf.
                                            rewrite filter_app in Hlf.
                                            rewrite filter_app in Hlf.
                                            rewrite filter_cons in Hlf.
                                            rewrite filter_cons in Hlf.
                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                            simpl in Hlf.
                                            rewrite app_length in Hlf.
                                            rewrite app_length in Hlf.
                                            simpl in Hlf.
                                            ltac1:(lia).
                                        }
                                    }
                                }
                                {
                                    clear -Hfind3.
                                    rewrite Forall_forall.
                                    intros x Hx.
                                    rewrite elem_of_list_In in Hx.
                                    rewrite in_concat in Hx.
                                    destruct Hx as [x0 [H1x0 H2x0]].
                                    rewrite in_map_iff in H1x0.
                                    destruct H1x0 as [x1 [H1x1 H2x1]].
                                    rewrite <- elem_of_list_In in H2x1.
                                    rewrite <- elem_of_list_In in H2x0.
                                    subst. intros HContra. subst.
                                    rewrite elem_of_take in H2x1.
                                    destruct H2x1 as [i [H1i H2i]].
                                    ltac1:(naive_solver).
                                }
                            }
                            specialize (IHsz Hnotinψ).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                clear IHsz.
                                apply take_drop_middle in Hfind1.
                                apply take_drop_middle in Hln.
                                rewrite <- Hfind1 in H3.
                                rewrite <- Hln in H3.
                                rewrite map_app in H3.
                                rewrite map_cons in H3.
                                rewrite zip_with_app in H3.
                                {
                                    rewrite Forall_app in H3.
                                    simpl in H3.
                                    rewrite Forall_cons in H3.
                                    destruct H3 as [H31 [H32 H33]].
                                    exact H32.
                                }
                                {
                                    rewrite take_length.
                                    rewrite map_length.
                                    rewrite take_length.
                                    ltac1:(lia).
                                }
                            }
                            destruct IHsz as [IH1 IH2].
                            split>[apply IH1|].
                            unfold satisfies; simpl.
                            unfold apply_symbol'.
                            unfold to_PreTerm'.
                            unfold to_Term'.
                            constructor.
                            apply satisfies_top_bov_cons.
                            (repeat split); try reflexivity.
                            {
                                rewrite insert_length. ltac1:(lia).
                            }
                            {
                                assert (Hln' := Hln).
                                assert (Hfind1' := Hfind1).
                                apply take_drop_middle in Hln.
                                apply take_drop_middle in Hfind1.
                                rewrite <- Hln.
                                rewrite <- Hfind1.
                                rewrite insert_app_r_alt.
                                {
                                    rewrite take_length.
                                    rewrite Nat.min_l.
                                    {
                                        rewrite Nat.sub_diag.
                                        simpl.
                                        rewrite zip_with_app.
                                        {
                                            simpl.
                                            rewrite Forall_app.
                                            rewrite Forall_cons.
                                            repeat split.
                                            {
                                                rewrite Forall_forall.
                                                intros x Hx.
                                                rewrite elem_of_lookup_zip_with in Hx.
                                                destruct Hx as [i [x0 [y0 [HH1 [HH2 HH3]]]]].
                                                assert (Hi_lt_n : i < n).
                                                {
                                                    apply lookup_lt_Some in HH2.
                                                    rewrite take_length in HH2.
                                                    ltac1:(lia).
                                                }
                                                subst x.
                                                rewrite Forall_forall in H3.
                                                ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
                                                eapply satisfies_ext>[|apply H3;exists i,x0,y0;(split>[reflexivity|])].
                                                {
                                                    unfold Valuation in *.
                                                    apply insert_subseteq.
                                                    clear -Hnotinρ.
                                                    unfold vars_of in Hnotinρ; simpl in Hnotinρ.
                                                    apply not_elem_of_dom_1. exact Hnotinρ.
                                                }
                                                {
                                                    rewrite lookup_take in HH2.
                                                    split>[exact HH2|].
                                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                                    rewrite list_lookup_fmap.
                                                    rewrite lookup_take in HH3.
                                                    rewrite HH3.
                                                    simpl.
                                                    rewrite subst_notin.
                                                    { reflexivity. }
                                                    {
                                                        intros HContra.
                                                        rewrite elem_of_list_lookup in HContra.
                                                        destruct HContra as [j Hj].
                                                        apply take_drop_middle in Hj.
                                                        apply take_drop_middle in HH3.
                                                        rewrite <- HH3 in Hlf.
                                                        
                                                        rewrite map_app in Hlf.
                                                        rewrite map_cons in Hlf.
                                                        rewrite concat_app in Hlf.
                                                        rewrite concat_cons in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite <- Hj in Hlf.
                                                        clear Hj.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_cons in Hlf.
                                                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                        clear e.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        simpl in Hlf.
                                                        rewrite <- Hfind1 in Hlf.
                                                        assert (Hnl0: n < length l0).
                                                        {
                                                            apply lookup_lt_Some in Hfind1'.
                                                            exact Hfind1'.
                                                        }
                                                        (* clear -Hlf Hfind2 Hnl0. *)
                                                        apply elem_of_list_lookup in Hfind2.
                                                        destruct Hfind2 as [j' Hj'].
                                                        apply take_drop_middle in Hj'.
                                                        rewrite take_app in Hlf.
                                                        rewrite drop_app in Hlf.
                                                        rewrite take_length in Hlf.
                                                        destruct ((i - n `min` length l0)) eqn:Heq1.
                                                        {
                                                            simpl in Hlf.
                                                            destruct ((S i - n `min` length l0)) eqn:Heq2.
                                                            {
                                                                simpl in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_cons in Hlf.
                                                                simpl in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_cons in Hlf.
                                                                rewrite <- Hj' in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_cons in Hlf.
                                                                destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                                repeat (rewrite app_length in Hlf).
                                                                simpl in Hlf.
                                                                ltac1:(lia).
                                                            }
                                                            {
                                                                ltac1:(lia).
                                                            }
                                                        }
                                                        {
                                                            repeat (rewrite map_app in Hlf).
                                                            repeat (rewrite concat_app in Hlf).
                                                            repeat (rewrite filter_app in Hlf).
                                                            simpl in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite <- Hj' in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_cons in Hlf.
                                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                            repeat (rewrite app_length in Hlf).
                                                            simpl in Hlf.
                                                            ltac1:(lia).
                                                        }
                                                    }
                                                    {
                                                        ltac1:(lia).
                                                    }
                                                    {
                                                        ltac1:(lia).
                                                    }
                                                }
                                            }
                                            {
                                                exact IH2.
                                            }
                                            {
                                                rewrite Forall_forall.
                                                intros x Hx.
                                                rewrite elem_of_lookup_zip_with in Hx.
                                                destruct Hx as [i [x0 [y0 [HH1 [HH2 HH3]]]]].
                                                rewrite lookup_drop in HH2.
                                                rewrite lookup_drop in HH3.
                                                assert (S n + i < length l0).
                                                {
                                                    apply lookup_lt_Some in HH3.
                                                    ltac1:(lia).
                                                }
                                                subst x.
                                                rewrite Forall_forall in H3.
                                                ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
                                                eapply satisfies_ext>[|apply H3;exists (S n + i),x0,y0;(split>[reflexivity|])].
                                                {
                                                    unfold Valuation in *.
                                                    apply insert_subseteq.
                                                    clear -Hnotinρ.
                                                    unfold vars_of in Hnotinρ; simpl in Hnotinρ.
                                                    apply not_elem_of_dom_1. exact Hnotinρ.
                                                }
                                                {
                                                    split>[exact HH2|].
                                                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                                                    rewrite list_lookup_fmap.
                                                    rewrite HH3.
                                                    simpl.
                                                    rewrite subst_notin.
                                                    { reflexivity. }
                                                    {
                                                        intros HContra.
                                                        rewrite elem_of_list_lookup in HContra.
                                                        destruct HContra as [j Hj].
                                                        apply take_drop_middle in Hj.
                                                        apply take_drop_middle in HH3.
                                                        rewrite <- HH3 in Hlf.
                                                        
                                                        rewrite map_app in Hlf.
                                                        rewrite map_cons in Hlf.
                                                        rewrite concat_app in Hlf.
                                                        rewrite concat_cons in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_app in Hlf.
                                                        rewrite <- Hj in Hlf.
                                                        clear Hj.
                                                        rewrite filter_app in Hlf.
                                                        rewrite filter_cons in Hlf.
                                                        destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                        clear e.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        rewrite app_length in Hlf.
                                                        simpl in Hlf.
                                                        rewrite <- Hfind1 in Hlf.
                                                        assert (Hnl0: n < length l0).
                                                        {
                                                            apply lookup_lt_Some in Hfind1'.
                                                            exact Hfind1'.
                                                        }
                                                        (* clear -Hlf Hfind2 Hnl0. *)
                                                        apply elem_of_list_lookup in Hfind2.
                                                        destruct Hfind2 as [j' Hj'].
                                                        apply take_drop_middle in Hj'.
                                                        rewrite take_app in Hlf.
                                                        rewrite drop_app in Hlf.
                                                        rewrite take_length in Hlf.
                                                        destruct (((S (n + i)) - n `min` length l0)) eqn:Heq1.
                                                        {
                                                            simpl in Hlf.
                                                            destruct ((S (S (n + i)) - n `min` length l0)) eqn:Heq2.
                                                            {
                                                                simpl in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_app in Hlf.
                                                                rewrite map_cons in Hlf.
                                                                simpl in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_app in Hlf.
                                                                rewrite concat_cons in Hlf.
                                                                rewrite <- Hj' in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_app in Hlf.
                                                                rewrite filter_cons in Hlf.
                                                                destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                                repeat (rewrite app_length in Hlf).
                                                                simpl in Hlf.
                                                                ltac1:(lia).
                                                            }
                                                            {
                                                                ltac1:(lia).
                                                            }
                                                        }
                                                        {
                                                            repeat (rewrite map_app in Hlf).
                                                            repeat (rewrite concat_app in Hlf).
                                                            repeat (rewrite filter_app in Hlf).
                                                            simpl in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite <- Hj' in Hlf.
                                                            rewrite filter_app in Hlf.
                                                            rewrite filter_cons in Hlf.
                                                            destruct (decide (h=h))>[|ltac1:(contradiction)].
                                                            repeat (rewrite app_length in Hlf).
                                                            simpl in Hlf.
                                                            ltac1:(lia).
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        {
                                            rewrite take_length.
                                            rewrite take_length.
                                            ltac1:(lia).
                                        }
                                    }
                                    {
                                        apply lookup_lt_Some in Hln'.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    rewrite take_length. ltac1:(lia).
                                }
                            }
                        }
                        {
                            simpl in *.
                            apply satisfies_term_inv in Hsat.
                            destruct Hsat as [lγ [H1 [H2 H3]]].
                            inversion H1; subst; clear H1.
                            simpl in *.
                            rewrite map_length in H2.
                            destruct Hfind as [HContra ?].
                            apply lookup_lt_Some in HContra.
                            apply lookup_ge_None in Hln.
                            ltac1:(lia).
                        }
                    }
                    {
                        apply list_find_None in Hfind.
                        simpl in *.
                        apply satisfies_term_inv in Hsat.
                        destruct Hsat as [lγ [H1 [H2 H3]]].
                        inversion H1; subst; clear H1.
                        rewrite map_length in H2.
                        clear Heqmb.
                        ltac1:(exfalso).
                        clear -Hlf Hfind.
                        rewrite list_filter_Forall_not in Hlf.
                        {
                            simpl in Hlf. inversion Hlf.
                        }
                        {
                            clear -Hfind.
                            rewrite Forall_forall.
                            rewrite Forall_forall in Hfind.
                            intros x Hx.
                            rewrite elem_of_list_In in Hx.
                            rewrite in_concat in Hx.
                            destruct Hx as [x0 [H1x0 H2x0]].
                            rewrite in_map_iff in H1x0.
                            destruct H1x0 as [x1 [H1x2 H2x1]].
                            subst x0.
                            specialize (Hfind x1).
                            rewrite <- elem_of_list_In in H2x1.
                            specialize (Hfind H2x1).
                            intros HContra. subst x.
                            apply Hfind.
                            rewrite <- elem_of_list_In in H2x0.
                            apply H2x0.
                        }
                    }
                }
            }
        }
    }
Qed.


Lemma frto_step_app
    {Σ : StaticModel}
    (Act : Set)
    :
    forall
        Γ
        (t1 t2 t3 : TermOver builtin_value)
        (w : list Act)
        (a : Act)
        r,
    r ∈ Γ ->
    flattened_rewrites_to_over Γ t1 w t2 ->
    flattened_rewrites_to r (uglify' t2) a (uglify' t3) ->
    flattened_rewrites_to_over Γ t1 (w++[a]) t3
.
Proof.
    intros Γ t1 t2 t3 w a r Hr H1 H2.
    induction H1.
    {
        simpl.
        eapply frto_step.
        { exact Hr. }
        { exact H2. }
        { apply frto_base. }
    }
    {
        simpl.
        specialize (IHflattened_rewrites_to_over H2).
        eapply frto_step.
        { exact H. }
        { exact H0. }
        { apply IHflattened_rewrites_to_over. }
    }
Qed.

Lemma satisfies_TermOver_vars_of
    {Σ : StaticModel}
    (ρ1 ρ2 : Valuation)
    (g : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    (∀ x : variable, x ∈ vars_of (uglify' φ) → ρ1 !! x = ρ2 !! x) →
    satisfies ρ1 g φ ↔ satisfies ρ2 g φ
.
Proof.
    intros H.
    assert (Htmp := satisfies_Term'_vars_of ρ1 ρ2 (uglify' g) (uglify' φ) H).
    apply Htmp.
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

Lemma satisfies_TermOverBoV_to_TermOverExpr
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    satisfies ρ γ (TermOverBoV_to_TermOverExpr φ)
    <->
    satisfies ρ γ φ
.
Proof.
    revert γ.
    induction φ; intros γ.
    {
        unfold TermOverBoV_to_TermOverExpr.
        simpl.
        split; intros H.
        {
            destruct a; simpl in *.
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    constructor.
                    inversion pf; subst; clear pf.
                    constructor.
                }   
                {
                    apply (f_equal prettify) in H0.
                    rewrite (cancel prettify uglify') in H0.
                    subst γ.
                    inversion H3.
                }             
            }
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    constructor.
                    inversion pf; subst; clear pf.
                    constructor.
                    assumption.
                }
                {
                    apply (f_equal prettify) in H0.
                    rewrite (cancel prettify uglify') in H0.
                    subst γ.
                    inversion H3; subst; clear H3.
                    simpl.
                    apply satisfies_var.
                    rewrite uglify'_prettify'.
                    assumption.
                }
            }
        }
        {
            destruct a.
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    simpl.
                    constructor.
                    inversion pf; subst; clear pf.
                    constructor.
                }
                {

                    apply (f_equal prettify) in H0.
                    rewrite (cancel prettify uglify') in H0.
                    subst γ.
                    simpl.
                    inversion H3.
                }
            }
            {
                inversion H; subst; clear H.
                {
                    apply (f_equal prettify) in H2.
                    rewrite (cancel prettify uglify') in H2.
                    subst γ.
                    simpl.
                    inversion pf; subst; clear pf.
                    constructor.
                    unfold satisfies; simpl.
                    assumption.
                }
                {
                    apply (f_equal prettify) in H0.
                    rewrite (cancel prettify uglify') in H0.
                    subst γ.
                    simpl.
                    inversion H3; subst; clear H3.
                    unfold satisfies; simpl.
                    rewrite uglify'_prettify'.
                    constructor.
                    assumption.
                }
            }
        }
    }
    {
        split; intros HH.
        {
            unfold TermOverBoV_to_TermOverExpr in HH.
            simpl in HH.
            apply satisfies_term_expr_inv in HH.
            destruct HH as [lγ [H1 [H2 H3]]].
            subst γ.
            unfold satisfies; simpl.
            unfold apply_symbol'; simpl.
            constructor.
            unfold to_PreTerm'; simpl.
            apply satisfies_top_bov_cons.
            split.
            {
                rewrite map_length in H2. ltac1:(lia).
            }
            {
                split>[|reflexivity].
                rewrite Forall_forall in H.
                rewrite Forall_forall in H3.
                rewrite Forall_forall.
                intros P.
                rewrite elem_of_lookup_zip_with.
                intros HH.
                ltac1:(setoid_rewrite elem_of_lookup_zip_with in H3).
                destruct HH as [i [x [y [HH1 [HH2 HH3]]]]].
                subst P.
                rewrite <- H.
                {
                    apply H3.
                    exists i,x.
                    exists (TermOverBoV_to_TermOverExpr y).
                    split>[reflexivity|].
                    split>[assumption|].
                    ltac1:(replace map with (@fmap _ list_fmap) by reflexivity).
                    rewrite list_lookup_fmap.
                    rewrite HH3. simpl. reflexivity.
                }
                {
                    rewrite elem_of_list_lookup. exists i. assumption.
                }
            }
        }
        {
            unfold TermOverBoV_to_TermOverExpr. simpl.
            apply satisfies_term_inv in HH.
            destruct HH as [lγ [HH1 [HH2 HH3]]].
            subst γ.
            unfold satisfies; simpl.
            unfold apply_symbol'; simpl.
            constructor.
            unfold to_PreTerm'; simpl.
            apply satisfies_top_bov_cons_expr.
            split.
            {
                rewrite map_length. ltac1:(lia).
            }
            split>[|reflexivity].
            rewrite Forall_forall in H.
            rewrite Forall_forall in HH3.
            rewrite Forall_forall.
            intros P HP.
            rewrite elem_of_lookup_zip_with in HP.
            destruct HP as [i [x [y [HH4 [HH5 HH6]]]]].
            subst P.
            ltac1:(replace map with (@fmap _ list_fmap) in HH6 by reflexivity).
            rewrite list_lookup_fmap in HH6.
            destruct (l !! i) eqn:Hli.
            {
                simpl in HH6. inversion HH6. subst. clear HH6.
                apply H.
                {
                    rewrite elem_of_list_lookup. exists i. assumption.
                }
                apply HH3.
                rewrite elem_of_lookup_zip_with.
                exists i,x,t.
                repeat split; assumption.
            }
            {
                apply lookup_ge_None in Hli.
                apply lookup_lt_Some in HH5.
                ltac1:(lia).
            }
        }
    }
Qed.

Lemma subterm_matches_variable
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ γ' : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    satisfies ρ γ φ  ->
    is_subterm_b γ' γ = true  ->
    is_subterm_b (TermOverBuiltin_to_TermOverBoV γ') φ = false ->
    ∃ x γ'', ρ !! x = Some (uglify' γ'') /\ is_subterm_b γ' γ''
    (*/\ is_subterm_b γ'' γ *)
.
Proof.
    revert γ.
    induction φ; intros γ H1 H2 H3.
    {
        simpl in *.
        ltac1:(case_match).
        { ltac1:(congruence). }
        destruct a; simpl in *.
        {
            inversion H1; subst; clear H1.
            {
                apply (f_equal prettify) in H5.
                rewrite (cancel prettify uglify') in H5.
                subst γ.
                simpl in *.
                ltac1:(case_match).
                {
                    unfold satisfies in pf; simpl in pf.
                    unfold builtin_satisfies_BuiltinOrVar' in pf; simpl in pf.
                    inversion pf; subst; clear pf.
                    simpl in *.
                    unfold is_left in *.
                    ltac1:(repeat case_match); try ltac1:(congruence).
                    subst; simpl in *.
                    ltac1:(contradiction n).
                    simpl. reflexivity.
                }
                {
                    ltac1:(congruence).
                }
            }
            {
                apply (f_equal prettify) in H0.
                rewrite (cancel prettify uglify') in H0.
                subst γ.
                simpl in *.
                unfold is_left in *.
                ltac1:(repeat case_match); try ltac1:(congruence).
                inversion H6; subst; clear H6.
            }
        }
        {
            inversion H1; subst; clear H1.
            {
                inversion pf; subst; clear pf.
                unfold is_left in *.
                ltac1:(repeat case_match); try ltac1:(congruence).
                exists x.
                exists γ.
                rewrite <- H5.
                split>[assumption|].
                assumption.
            }
            {
                unfold is_left in *.
                ltac1:(repeat case_match); try ltac1:(congruence).
                inversion H6; subst; clear H6.
                exists x.
                exists γ.
                rewrite <- H0.
                split>[assumption|].
                assumption.
            }
        }
    }
    {
        destruct γ; simpl in *.
        {
            inversion H1.
        }
        apply satisfies_term_inv in H1.
        destruct H1 as [lγ [H4 [H5 H6]]].
        simpl in *.
        unfold is_left in *.
        ltac1:(repeat case_match; try congruence); simpl in *.
        {
            inversion H4; subst; clear H4.
            clear H0 H1 H2 H7 H8.
        }
        {
            inversion H4; subst; clear H4.
            simpl in *.
        }
    }
Qed.

Lemma satisfies_subst_subst
    {Σ : StaticModel}
    (ρ : Valuation)
    (γ γ1 : TermOver builtin_value)
    (h : variable)
    (holeSymbol : symbol)
    (φ : TermOver BuiltinOrVar)
    :
    h ∈ vars_of (uglify' φ) ->
    is_subterm_b (TermOverBuiltin_to_TermOverBoV γ1) φ = false ->
    (forall x, ρ !! x <> Some (uglify' (t_term holeSymbol []))) ->
    satisfies (<[h:=uglify' γ1]>ρ) γ φ ->
    satisfies ρ
        (TermOverBuiltin_subst γ γ1 (t_term holeSymbol []))
        (TermOverBoV_subst φ h (t_term holeSymbol []))
.
Proof.
    revert γ γ1 holeSymbol.
    induction φ; intros γ γ1 holeSymbol Hhφ Hnotsub Hnotincod HH2.
    {
        (* φ is BoV `a` *)
        unfold TermOverBuiltin_subst.
        destruct γ; simpl in *.
        {
            (* γ is a builtin value `a0` *)
            inversion HH2; subst; clear HH2.
            unfold is_left in *.
            destruct (decide (t_over a0 = γ1)) as [Heq|Hneq].
            {
                subst.
                unfold vars_of in Hhφ; simpl in Hhφ.
                unfold vars_of in Hhφ; simpl in Hhφ.
                destruct a.
                {
                    subst.
                    inversion Hhφ; subst; clear Hhφ.
                }
                {
                    simpl in Hhφ. rewrite elem_of_singleton in Hhφ.
                    subst.
                    destruct (decide (x=x))>[|ltac1:(contradiction)].
                    constructor. constructor.
                }
            }
            {
                unfold vars_of in Hhφ; simpl in Hhφ.
                unfold vars_of in Hhφ; simpl in Hhφ.
                destruct a.
                {
                    simpl in Hhφ.
                    rewrite elem_of_empty in Hhφ. inversion Hhφ.
                }
                {
                    simpl in Hhφ.
                    rewrite elem_of_singleton in Hhφ.
                    subst.
                    destruct (decide (x=x))>[|ltac1:(contradiction)].
                    inversion pf; subst; clear pf.
                    ltac1:(rewrite lookup_insert_Some in H1).
                    destruct H1 as [H1|H1].
                    {
                        destruct H1 as [_ H1].
                        apply (f_equal prettify) in H1.
                        rewrite (cancel prettify uglify') in H1.
                        subst. simpl in Hneq.
                        ltac1:(contradiction Hneq).
                        reflexivity.
                    }
                    {
                        ltac1:(naive_solver).
                    }
                }
            }
        }
        {
            destruct a.
            {
                inversion HH2; subst; clear HH2.
                apply satisfies_builtin_inv in H2.
                inversion H2.
            }
            {
                inversion HH2; subst; clear HH2.
                inversion H2; subst; clear H2.
                destruct (decide (h = x)).
                {
                    subst.
                    ltac1:(rewrite lookup_insert in H0).
                    inversion H0; subst; clear H0.
                    apply (f_equal prettify) in H1.
                    rewrite (cancel prettify uglify') in H1.
                    subst.
                    unfold is_left in *.
                    clear Hnotsub.
                    ltac1:(repeat case_match); try assumption; try ltac1:(congruence).
                    {
                        do 2 constructor.
                    }
                    {
                        clear H0 H.
                        ltac1:(rename n into HH).
                        ltac1:(exfalso).
                        apply HH. clear H2 HH.
                        simpl.
                        rewrite <- (cancel prettify uglify').
                        simpl.
                        reflexivity.
                    }
                }
                {
                    unfold vars_of in Hhφ; simpl in Hhφ.
                    unfold vars_of in Hhφ; simpl in Hhφ.
                    ltac1:(set_solver).
                }
            }
        }
    }
    {
        destruct γ.
        {
            simpl in *.
            unfold is_left.
            apply satisfies_term_inv in HH2.
            destruct HH2 as [? [HContra ?]].
            inversion HContra.
        }
        {
            rewrite <- vars_of_uglify in Hhφ.
            assert (HHsizes := HH2).
            apply concrete_is_larger_than_symbolic in HHsizes.
            apply satisfies_term_inv in HH2.
            destruct HH2 as [lγ [HH2 [HH3 HH4]]].
            inversion HH2; subst; clear HH2.
            simpl.
            destruct (decide (t_term s lγ = γ1)) as [?|Hneq].
            {
                simpl in *. subst.
                ltac1:(exfalso).
                clear -HHsizes Hhφ.
                unfold delta_in_val in HHsizes.
                unfold size_of_var_in_val in HHsizes.
                rewrite elem_of_list_In in Hhφ.
                rewrite in_concat in Hhφ.
                destruct Hhφ as [x [H1x H2x]].
                rewrite in_map_iff in H1x.
                destruct H1x as [x0 [H1x0 H2x0]].
                subst.
                rewrite <- elem_of_list_In in H2x0.
                ltac1:(rewrite elem_of_list_lookup in H2x0).
                destruct H2x0 as [i Hi].
                apply take_drop_middle in Hi.
                rewrite <- Hi in HHsizes.
                repeat (rewrite sum_list_with_app in HHsizes).
                simpl in HHsizes.
                rewrite map_app in HHsizes.
                rewrite map_cons in HHsizes.
                rewrite concat_app in HHsizes.
                rewrite concat_cons in HHsizes.
                repeat (rewrite sum_list_with_app in HHsizes).
                simpl in HHsizes.
                rewrite <- elem_of_list_In in H2x.
                rewrite elem_of_list_lookup in H2x.
                destruct H2x as [j Hj].
                apply take_drop_middle in Hj.
                rewrite <- Hj in HHsizes.
                repeat (rewrite sum_list_with_app in HHsizes).
                simpl in HHsizes.
                ltac1:(case_match).
                {
                    ltac1:(rewrite lookup_insert in H).
                    inversion H; subst; clear H.
                    remember ((λ x : variable,
                        match
                        <[h:=apply_symbol' s (map uglify' lγ)]> ρ
                        !! x
                        with
                        | Some g =>
                            Init.Nat.pred
                        (TermOver_size (prettify g))
                        | None => 0
                        end)
                    ) as F.
                    ltac1:(replace ((prettify (apply_symbol' s (map uglify' lγ)))) with (t_term s lγ) in HHsizes).
                    {
                        simpl in HHsizes.
                        repeat (rewrite sum_list_with_compose in HHsizes).
                        unfold compose in HHsizes.
                        repeat (rewrite sum_list_with_S in HHsizes).
                        repeat (rewrite sum_list_fmap in HHsizes).
                        repeat (rewrite fmap_length in HHsizes).
                        repeat (rewrite drop_length in HHsizes).
                        assert (Htmp := TermOver_size_not_zero ((t_term s lγ))).
                        ltac1:(lia).
                    }
                    {
                        rewrite <- (cancel prettify uglify').
                        simpl. reflexivity.
                    }
                }
                {
                    ltac1:(rewrite lookup_insert in H).
                    inversion H.
                }
            }
            {
                simpl.
                unfold satisfies; simpl.
                unfold apply_symbol'; simpl.
                constructor.
                unfold to_PreTerm'; simpl.
                apply satisfies_top_bov_cons.
                rewrite map_length.
                rewrite map_length.
                split>[ltac1:(lia)|].
                split>[|reflexivity].
                rewrite Forall_forall.
                rewrite Forall_forall in HH4.
                ltac1:(setoid_rewrite elem_of_lookup_zip_with).
                ltac1:(setoid_rewrite elem_of_lookup_zip_with in HH4).
                intros x Hx.
                destruct Hx as [i [x0 [y0 [Hx1 [Hx2 Hx3]]]]].
                subst x.
                ltac1:(replace map with (@fmap _ list_fmap) in Hx2).
                ltac1:(replace map with (@fmap _ list_fmap) in Hx3).
                rewrite list_lookup_fmap in Hx2.
                rewrite list_lookup_fmap in Hx3.
                rewrite Forall_forall in H.
                destruct ((l!!i)) eqn:Hli.
                {
                    simpl in Hx3.
                    inversion Hx3; subst; clear Hx3.
                    destruct (lγ!!i) eqn:Hlγi.
                    {
                        simpl in Hx2.
                        inversion Hx2; subst; clear Hx2.

                        specialize (HH4 (satisfies (<[h:=uglify' γ1]> ρ) t0 t)).
                        ltac1:(ospecialize (HH4 _)).
                        {
                            exists i, t0, t.
                            split>[reflexivity|].
                            split;assumption.
                        }
                        
                        destruct 
                            (is_subterm_b γ1 t0) eqn:Hsγ1t0,
                            (decide (h ∈ (vars_of (uglify' t)))) as[Hhint|Hhnotint].
                        {
                            specialize (H t).
                            ltac1:(ospecialize (H _)).
                            {
                                rewrite elem_of_list_lookup.
                                exists i.
                                exact Hli.
                            }
                            specialize (H t0 γ1 holeSymbol).
                            specialize (H ltac:(assumption)).
                            simpl in Hnotsub.
                            destruct (decide (t_term s l = TermOverBuiltin_to_TermOverBoV γ1)) as [His|Hisnot].
                            {
                                simpl in Hnotsub. inversion Hnotsub.
                            }
                            {
                                simpl in Hnotsub.
                                assert (Hnot' := @existsb_nth (TermOver BuiltinOrVar)).
                                specialize (Hnot' (is_subterm_b (TermOverBuiltin_to_TermOverBoV γ1)) l).
                                specialize (Hnot' i t).
                                ltac1:(ospecialize (Hnot' _)).
                                {
                                    apply lookup_lt_Some in Hli.
                                    exact Hli.
                                }
                                specialize (Hnot' Hnotsub).
                                assert (Hli' := Hli).
                                apply nth_lookup_Some with (d := t) in Hli'.
                                rewrite Hli' in Hnot'.
                                specialize (H Hnot').
                                clear Hli' Hnot'.
                                specialize (H Hnotincod).
                                specialize (H HH4).
                                exact H.
                            }
                        }
                        {
                            rewrite subst_notin>[|rewrite <- vars_of_uglify in Hhnotint; exact Hhnotint].
                            (*ltac1:(exfalso).*)
                            simpl in *.
                            destruct ((decide (t_term s l = TermOverBuiltin_to_TermOverBoV γ1)));
                                inversion Hnotsub; subst; clear Hnotsub.
                            rewrite satisfies_TermOver_vars_of with (ρ2 := ρ) in HH4.
                            {
                                assert (is_subterm_b (TermOverBuiltin_to_TermOverBoV γ1) t = false).
                                {
                                    apply take_drop_middle in Hli.
                                    rewrite <- Hli in H1.
                                    rewrite existsb_app in H1.
                                    simpl in H1.
                                    rewrite orb_false_iff in H1.
                                    destruct H1 as [H11 H12].
                                    rewrite orb_false_iff in H12.
                                    destruct H12 as [H12 H13].
                                    exact H12.
                                }
                                clear H1 Hhnotint.
                                clear Hli Hlγi.
                                Search holeSymbol.
                            }
                            {
                                intros x Hx.
                                destruct (decide (h = x)).
                                {
                                    subst. ltac1:(contradiction Hhnotint).
                                }
                                {
                                    ltac1:(rewrite lookup_insert_ne).
                                    { assumption. }
                                    { reflexivity. }
                                }
                            }
                        }
                        {
                            specialize (H t).
                            ltac1:(ospecialize (H _)).
                            {
                                rewrite elem_of_list_lookup.
                                exists i.
                                exact Hli.
                            }
                            specialize (H t0 γ1 γ2 holeSymbol).
                            specialize (H ltac:(assumption)).
                            simpl in Hnotsub.
                            destruct (decide (t_term s l = TermOverBuiltin_to_TermOverBoV γ1)) as [His|Hisnot].
                            {
                                simpl in Hnotsub. inversion Hnotsub.
                            }
                            {
                                simpl in Hnotsub.
                                assert (Hnot' := @existsb_nth (TermOver BuiltinOrVar)).
                                specialize (Hnot' (is_subterm_b (TermOverBuiltin_to_TermOverBoV γ1)) l).
                                specialize (Hnot' i t).
                                ltac1:(ospecialize (Hnot' _)).
                                {
                                    apply lookup_lt_Some in Hli.
                                    exact Hli.
                                }
                                specialize (Hnot' Hnotsub).
                                assert (Hli' := Hli).
                                apply nth_lookup_Some with (d := t) in Hli'.
                                rewrite Hli' in Hnot'.
                                specialize (H Hnot').
                                clear Hli' Hnot'.
                                specialize (H Hnotincod).
                                specialize (H HH1).
                                specialize (H HH4).
                                exact H.
                            }
                        }
                        {
                            rewrite not_subterm_subst>[|assumption].
                            rewrite subst_notin>[|(rewrite <- vars_of_uglify in Hhnotint;assumption)].
                            erewrite satisfies_TermOver_vars_of>[apply HH4|].
                            intros x Hx.
                            destruct (decide (h = x)).
                            {
                                subst. ltac1:(contradiction Hhnotint).
                            }
                            {
                                ltac1:(rewrite lookup_insert_ne).
                                { assumption. }
                                { reflexivity. }
                            }
                        }
                    }
                    {
                        simpl in Hx2. inversion Hx2.
                    }
                }
                {
                    simpl in Hx3.
                    inversion Hx3.
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
    (continuationVariable : variable) 
    (D : MinusL_LangDef Act)
    :
    ~ (invisible_act ∈ actions_of_ldef Act D) ->
    let Γ := compile invisible_act topSymbol cseqSymbol holeSymbol continuationVariable D in
    forall
        (lc ld rc rd : TermOver builtin_value)
        (w : list Act)
        (ρ : Valuation)
        (Hnocvρ : continuationVariable ∉ vars_of ρ)
        (HnoHoleSymbolInRho : forall x, ρ !! x <> Some (uglify' (t_term holeSymbol []))),
        MinusL_rewritesInVal Act D lc ld w  ρ rc rd
        <->
        (
            forall continuation,
            flattened_rewrites_to_over Γ
                (downC topSymbol cseqSymbol lc ld continuation)
                (filter (fun x => x <> invisible_act) w)
                (downC topSymbol cseqSymbol rc rd continuation)
        )
.
Proof.
    intros Hinvisible.
    intros.
    destruct D as [iV ds]; simpl in *.
    split; intros HH.
    {
        induction HH; intros continuation.
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
            rewrite filter_cons. rewrite filter_nil.
            destruct (decide (a <> invisible_act)).
            {
                eapply frto_step>[|()|apply frto_base].
                {
                    simpl.
                    rewrite elem_of_app.
                    right.
                    rewrite elem_of_cons.
                    left.
                    reflexivity.
                }
                {
                    unfold flattened_rewrites_to.
                    exists (<[continuationVariable := (uglify' continuation)]>ρ).
                    unfold flattened_rewrites_in_valuation_under_to.
                    split.
                    {
                        unfold apply_symbol'.
                        unfold to_Term'.
                        constructor.
                        unfold to_PreTerm'.
                        fold (@uglify' Σ).
                        ltac1:(
                            replace
                            (term_preterm (fold_left helper [uglify' lc; term_operand (bov_variable continuationVariable)] (pt_operator cseqSymbol)))
                            with
                            (uglify' (t_term cseqSymbol [lc; t_over (bov_variable continuationVariable)]))
                            by reflexivity
                        ).
                        ltac1:(
                            replace
                            ([uglify' (t_term cseqSymbol [lc; t_over (bov_variable continuationVariable)]); uglify' ld])
                            with
                            (map uglify' [((t_term cseqSymbol [lc; t_over (bov_variable continuationVariable)]));(ld)])
                            by reflexivity
                        ).
                        apply satisfies_top_bov_cons.
                        split.
                        {
                            simpl. reflexivity.
                        }
                        {
                            split>[|reflexivity].
                            simpl.
                            rewrite Forall_cons.
                            split.
                            {
                                apply satisfies_top_bov.
                                split.
                                {
                                    eapply satisfies_ext>[|apply H0].
                                    unfold Valuation in *.
                                    apply insert_subseteq.
                                    clear -Hnocvρ.
                                    unfold vars_of in Hnocvρ.
                                    simpl in Hnocvρ.
                                    rewrite not_elem_of_dom in Hnocvρ.
                                    exact Hnocvρ.
                                }
                                {
                                    apply satisfies_var.
                                    unfold Valuation in *.
                                    apply lookup_insert.
                                }
                            }
                            {
                                rewrite Forall_cons.
                                split.
                                {
                                    eapply satisfies_ext>[|apply H1].
                                    unfold Valuation in *.
                                    apply insert_subseteq.
                                    clear -Hnocvρ.
                                    unfold vars_of in Hnocvρ.
                                    simpl in Hnocvρ.
                                    rewrite not_elem_of_dom in Hnocvρ.
                                    exact Hnocvρ.   
                                }
                                {
                                    apply Forall_nil. exact I.
                                }
                            }
                        }
                    }
                    split.
                    {
                        unfold apply_symbol'.
                        unfold to_Term'.
                        constructor.
                        unfold to_PreTerm'.
                        fold (@uglify' Σ).
                        ltac1:(
                            replace
                            ([term_preterm (fold_left helper [uglify' rc; term_operand (ft_variable continuationVariable)] (pt_operator cseqSymbol)); uglify' rd])
                            with
                            (
                                map uglify' [(t_term cseqSymbol [rc; t_over (ft_variable continuationVariable)]);(rd)]
                            )
                            by reflexivity
                        ).
                        apply satisfies_top_bov_cons_expr.
                        (repeat split); try reflexivity.
                        simpl.
                        repeat (rewrite Forall_cons).
                        rewrite Forall_nil.
                        (repeat split).
                        {
                            constructor.
                            apply satisfies_top_bov_cons_expr.
                            (repeat split).
                            simpl.
                            repeat (rewrite Forall_cons).
                            rewrite Forall_nil.
                            (repeat split).
                            {
                                eapply satisfies_ext>[|apply H2].
                                unfold Valuation in *.
                                apply insert_subseteq.
                                clear -Hnocvρ.
                                unfold vars_of in Hnocvρ.
                                simpl in Hnocvρ.
                                rewrite not_elem_of_dom in Hnocvρ.
                                exact Hnocvρ.   
                            }
                            {
                                apply satisfies_var_expr.
                                unfold Valuation in *.
                                apply lookup_insert.
                            }
                        }
                        {
                            eapply satisfies_ext>[|apply H3].
                            unfold Valuation in *.
                            apply insert_subseteq.
                            clear -Hnocvρ.
                            unfold vars_of in Hnocvρ.
                            simpl in Hnocvρ.
                            rewrite not_elem_of_dom in Hnocvρ.
                            exact Hnocvρ.   
                        }
                    }
                    {
                        simpl.
                        split>[|reflexivity].
                        eapply satisfies_ext>[|apply H4].
                        unfold Valuation in *.
                        apply insert_subseteq.
                        clear -Hnocvρ.
                        unfold vars_of in Hnocvρ.
                        simpl in Hnocvρ.
                        rewrite not_elem_of_dom in Hnocvρ.
                        exact Hnocvρ.
                    }
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
            
            (* (1) decompose the first substitution *)
            assert (Hfbsc1 := factor_by_subst_correct' (TermOver_size ctrl1) ρ h ctrl1 c ((TermOverBuiltin_to_TermOverBoV r))).
            specialize (Hfbsc1 ltac:(lia) Hnotinρ Hh).
            rewrite vars_of_to_l2r_of_tob in Hfbsc1.
            specialize (Hfbsc1 ltac:(set_solver)).
            specialize (Hfbsc1 H2).
            simpl in Hfbsc1.
            destruct Hfbsc1 as [HA1 HB1].
            remember ((factor_by_subst (TermOver_size ctrl1) ρ h ctrl1 c (TermOverBuiltin_to_TermOverBoV r)).1) as G1.
            remember ((factor_by_subst (TermOver_size ctrl1) ρ h ctrl1 c (TermOverBuiltin_to_TermOverBoV r)).2) as F1.
            clear HeqF1 HeqG1.

            (* (2) decompose the second substitution *)
            assert (Hfbsc2 := factor_by_subst_correct' (TermOver_size ctrl2) ρ h ctrl2 c ((TermOverBuiltin_to_TermOverBoV v))).
            specialize (Hfbsc2 ltac:(lia) Hnotinρ Hh).
            rewrite vars_of_to_l2r_of_tob in Hfbsc2.
            specialize (Hfbsc2 ltac:(set_solver)).
            specialize (Hfbsc2 H3).
            simpl in Hfbsc2.
            destruct Hfbsc2 as [HA2 HB2].
            remember ((factor_by_subst (TermOver_size ctrl2) ρ h ctrl2 c (TermOverBuiltin_to_TermOverBoV v)).1) as G2.
            remember ((factor_by_subst (TermOver_size ctrl2) ρ h ctrl2 c (TermOverBuiltin_to_TermOverBoV v)).2) as F2.
            clear HeqF2 HeqG2.

            (* (3) Find the heating and cooling rules in Γ *)

            assert (ctx_heat invisible_act topSymbol cseqSymbol holeSymbol (fresh (h::vars_of_to_l2r c)) (fresh (h:: (fresh (h :: vars_of_to_l2r c)) :: vars_of_to_l2r c)) iV c h scs ∈ Γ).
            {
                rewrite elem_of_list_lookup in H.
                destruct H as [ir Hir].
                apply take_drop_middle in Hir.
                ltac1:(unfold Γ in IHHH).
                ltac1:(unfold Γ).
                ltac1:(rewrite - Hir).
                unfold compile.
                simpl.
                ltac1:(rewrite map_app).
                ltac1:(rewrite map_cons).
                simpl.
                ltac1:(rewrite concat_app).
                ltac1:(rewrite concat_cons).
                ltac1:(unfold Γ).
                clear.
                rewrite elem_of_app. right.
                rewrite elem_of_app. left.
                rewrite elem_of_cons. left.
                reflexivity.
            }

            assert (ctx_cool invisible_act topSymbol cseqSymbol holeSymbol (fresh (h::vars_of_to_l2r c)) (fresh (h:: (fresh (h::vars_of_to_l2r c)) :: vars_of_to_l2r c)) iV c h ∈ Γ).
            {
                rewrite elem_of_list_lookup in H.
                destruct H as [ir Hir].
                apply take_drop_middle in Hir.
                ltac1:(unfold Γ in IHHH).
                ltac1:(unfold Γ).
                ltac1:(rewrite - Hir).
                unfold compile.
                simpl.
                ltac1:(rewrite map_app).
                ltac1:(rewrite map_cons).
                simpl.
                ltac1:(rewrite concat_app).
                ltac1:(rewrite concat_cons).
                ltac1:(unfold Γ).
                clear.
                rewrite elem_of_app. right.
                rewrite elem_of_app. left.
                rewrite elem_of_cons. right.
                rewrite elem_of_cons. left.
                reflexivity.
            }

            (* (4) Use the heating rule. *)
            assert (Htmp := @frto_step Σ Act Γ).
            specialize (Htmp (downC topSymbol cseqSymbol G1 state1 continuation)).
            (* There should not be G1, but something like G1, but G1 contains F1, and we want to have holeSymbol instead of F1 in that modified G1.
            *)
            remember (TermOverBuiltin_subst G1 F1 (t_term holeSymbol [])) as G1'.
            specialize (Htmp (downC topSymbol cseqSymbol F1 state1 (t_term cseqSymbol [G1'; continuation]))).
            specialize (Htmp (downC topSymbol cseqSymbol F2 state2 (t_term cseqSymbol [G2; continuation]))).
            specialize (Htmp ((filter (λ x : Act, x ≠ invisible_act) w))).
            specialize (Htmp invisible_act).
            specialize (Htmp _ H4).
            ltac1:(ospecialize (Htmp _)).
            {
                clear Htmp.
                unfold flattened_rewrites_to.
                remember ((<[h:=uglify' F1]> ρ)) as ρ'.
                remember ((<[(fresh (h::vars_of_to_l2r c)):=uglify' continuation]>ρ')) as ρ''.
                remember (<[(fresh (h:: (fresh (h::vars_of_to_l2r c)) :: vars_of_to_l2r c)):=(uglify' state1)]>ρ'') as ρ'''.
                exists (ρ''').
                unfold flattened_rewrites_in_valuation_under_to.
                split.
                {
                    clear Htmp'.
                    apply satisfies_top_bov.
                    split.
                    {
                        apply satisfies_top_bov.
                        split.
                        {
                            unfold satisfies in HB1; simpl in HB1.
                            unfold satisfies; simpl.
                            erewrite satisfies_Term'_vars_of.
                            { eapply HB1. }
                            {
                                intros.
                                subst ρ'''.
                                subst ρ'.
                                ltac1:(rewrite lookup_insert_ne).
                                {
                                    rewrite <- vars_of_uglify in H6.
                                    intros HContra. subst x.
                                    assert (Htmp: fresh (h:: (fresh (h:: vars_of_to_l2r c)) :: vars_of_to_l2r c) ∉ (h:: fresh (h:: vars_of_to_l2r c) :: vars_of_to_l2r c)).
                                    {
                                        intros HContra'.
                                        eapply infinite_is_fresh; apply HContra'.
                                    }
                                    apply Htmp. clear Htmp.
                                    rewrite elem_of_cons.
                                    right.
                                    rewrite elem_of_cons.
                                    right.
                                    assumption.
                                }
                                subst ρ''.
                                ltac1:(rewrite lookup_insert_ne).
                                {
                                    intros HContra. subst x.
                                    rewrite <- vars_of_uglify in H6.
                                    assert (Htmp : fresh (h :: vars_of_to_l2r c) ∉ h :: vars_of_to_l2r c).
                                    {
                                        apply infinite_is_fresh.
                                    }
                                    apply Htmp. clear Htmp.
                                    rewrite elem_of_cons. right. assumption.
                                }
                                reflexivity.
                            }
                        }
                        {
                            subst ρ'''.
                            subst ρ''.
                            unfold Valuation in *.
                            rewrite insert_commute.
                            {
                                apply satisfies_var.
                                unfold Valuation in *.
                                apply lookup_insert.
                            }
                            {
                                intros HContra.
                                assert (Htmp : fresh (h:: (fresh (h :: vars_of_to_l2r c)) :: vars_of_to_l2r c) ∉ (h :: (fresh (h :: vars_of_to_l2r c)) :: vars_of_to_l2r c)).
                                {
                                    intros HContra'.
                                    eapply infinite_is_fresh;apply HContra'.
                                }
                                rewrite HContra in Htmp.
                                apply Htmp. clear HContra Htmp.
                                rewrite elem_of_cons.
                                right. rewrite elem_of_cons.
                                left. reflexivity.
                            }
                        }
                    }
                    {
                        subst ρ'''.
                        apply satisfies_var.
                        unfold Valuation in *.
                        apply lookup_insert.
                    }
                }
                split.
                {
                    clear Htmp'.
                    apply satisfies_top_expr.
                    split.
                    {
                        apply satisfies_top_expr.
                        split.
                        {
                            subst ρ'''.
                            subst ρ''.
                            subst ρ'.
                            unfold Valuation in *.
                            apply satisfies_var_expr.
                            unfold Valuation in *.
                            rewrite lookup_insert_ne.
                            {
                                rewrite lookup_insert_ne.
                                {
                                    apply lookup_insert.
                                }
                                {
                                    intros HContra.
                                    assert (Htmp: fresh (h :: vars_of_to_l2r c) ∉ (h :: vars_of_to_l2r c)).
                                    {
                                        apply infinite_is_fresh.
                                    }
                                    apply Htmp. clear Htmp.
                                    clear -HContra. ltac1:(set_solver).
                                }
                            }
                            {
                                intros HContra.
                                assert (Htmp: fresh (h :: fresh (h :: vars_of_to_l2r c) :: vars_of_to_l2r c) ∉ (h :: fresh (h :: vars_of_to_l2r c) :: vars_of_to_l2r c)).
                                {
                                    apply infinite_is_fresh.
                                }
                                apply Htmp. clear Htmp.
                                ltac1:(set_solver).
                            }
                        }
                        {
                            apply satisfies_top_expr.
                            split.
                            {
                                subst ρ'''.
                                subst G1'.
                                rewrite satisfies_TermOverBoV_to_TermOverExpr.
                                remember (fresh (h :: vars_of_to_l2r c)) as X0.
                                remember (fresh (h :: X0 :: vars_of_to_l2r c)) as X1.
                                assert (F1 = r).
                                {
                                    (* TODO by HA1 *)
                                    admit.
                                }
                                assert (F2 = v).
                                {
                                    (* TODO by HA2 *)
                                    admit.
                                }
                                subst F1 F2.
                                subst ρ' ρ''.
                                (* How many times can `r` occur in `G1`? *)
                                (*
                                    Also, `r` should use only the original symbol set.
                                    In particular, it does not contain the `holeSymbol`.
                                    The original formulas (`c`) do not contain `holeSymbol` either.
                                *)
                                (* HERE *)
                            }
                            {

                            }
                        }
                    }
                    {

                    }
                }
            }
            specialize (Htmp IHHH).








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
                        (* TODO something goes here *)                        
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