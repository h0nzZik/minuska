
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    syntax_properties
    semantics_properties
    spec_interpreter
    basic_matching
    try_match
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Logic.FunctionalExtensionality.

Definition evaluate_sc
    {Σ : StaticModel}
    (ρ : Valuation)
    (sc : SideCondition)
    : bool :=
match sc with
| sc_constraint c =>
    matchesb ρ () c
end.


Fixpoint PreTerm'_symbol_A_to_SymbolicTermB
    {Σ : StaticModel}
    {A B : Type}
    (A_to_SymbolicTermB : A ->
        ((Term' symbol B))
    )
    (x : PreTerm' symbol A)
    : ((PreTerm' symbol B))
:=
match x with
| pt_operator a => (pt_operator a)
| pt_app_operand x' a =>
    let t1 : (PreTerm' symbol B)
        := PreTerm'_symbol_A_to_SymbolicTermB A_to_SymbolicTermB x' in
    match A_to_SymbolicTermB a with
    | (term_preterm t2) => (pt_app_ao t1 t2)
    | (term_operand t2) => (pt_app_operand t1 t2)
    end
| pt_app_ao x1 x2 =>
    let t1 : (PreTerm' symbol B)
        := PreTerm'_symbol_A_to_SymbolicTermB A_to_SymbolicTermB x1 in
    let t2 : (PreTerm' symbol B)
        := PreTerm'_symbol_A_to_SymbolicTermB A_to_SymbolicTermB x2 in
    pt_app_ao t1 t2
end.

Definition Term'_symbol_A_to_SymbolicTermB
    {Σ : StaticModel}
    {A B : Type}
    (A_to_SymbolicTermB : A ->
        ((Term' symbol B))
    )
    (x : Term' symbol A)
    : ((Term' symbol B))
:=
match x with
| term_preterm app => term_preterm (PreTerm'_symbol_A_to_SymbolicTermB A_to_SymbolicTermB app)
| term_operand operand => A_to_SymbolicTermB operand
end.


Definition evaluate_rhs_pattern
    {Σ : StaticModel}
    (ρ : Valuation)
    (φ : Term' symbol Expression)
    : option GroundTerm :=
    let f : Expression -> option GroundTerm
        := (Expression_evaluate ρ) in
    let fφ  : Term' symbol (option GroundTerm)
        := f <$> φ in 
    let cfφ : option (Term' symbol GroundTerm)
        := Term'_collapse_option fφ in
    cfφ' ← cfφ;
    let flat := Term'_symbol_A_to_SymbolicTermB id cfφ' in
    Some flat
.

Definition rewrite_with
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    (g : GroundTerm)
    : option GroundTerm
:=
    ρ ← try_match g (fr_from r);
    if (forallb (evaluate_sc ρ) (fr_scs r)) then
        evaluate_rhs_pattern ρ (fr_to r)
    else None
.

Lemma evaluate_rhs_pattern_correct
    {Σ : StaticModel}
    
    (φ : ExpressionTerm)
    (ρ : Valuation)
    (g : GroundTerm)
    :
    evaluate_rhs_pattern ρ φ = Some g <->
    matchesb ρ g φ = true
.
Proof.
    unfold evaluate_rhs_pattern.
    rewrite bind_Some.
    
    ltac1:(
        under [fun e => _]functional_extensionality => e
    ).
    {
        ltac1:(rewrite inj_iff).
        ltac1:(over).
    }
    destruct φ; cbn.
    {
        cbn.
        ltac1:(
            under [fun e => _]functional_extensionality => e
        ).
        {
            ltac1:(rewrite bind_Some).
            ltac1:(
                under [fun e' => _]functional_extensionality => e'
            ).
            {
                ltac1:(rewrite inj_iff).
                ltac1:(over).
            }
            ltac1:(over).
        }
        destruct g; cbn.
        {
            unfold matchesb; simpl.
            cbn.

            split; intros H.
            {
                destruct H as [e H].
                destruct H as [H1 H2].
                destruct H1 as [e' [H11 H12]].
                cbn in *.
                subst.
                cbn in *.
                inversion H2; subst; clear H2.
                cbn in *.
                inversion H11; subst; clear H11.
                revert e' H0.
                induction ao; intros e' H0.
                {
                    cbn in *.
                    inversion H0; subst; clear H0.
                    simpl. unfold matchesb; simpl.
                    apply bool_decide_eq_true.
                    reflexivity.
                }
                {
                    cbn in *.
                    rewrite bind_Some in H0.
                    destruct H0 as [x [H1 H2]].
                    rewrite bind_Some in H2.
                    destruct H2 as [x0 H2].
                    destruct H2 as [H2 H3].
                    inversion H3; subst; clear H3.
                    cbn.
                    destruct x0.
                    {
                        unfold matchesb; simpl.
                        rewrite andb_true_iff.
                        unfold matchesb in IHao; simpl in IHao.
                        rewrite IHao.
                        {
                            split>[reflexivity|].
                            unfold matchesb; simpl.
                            apply bool_decide_eq_true.
                            assumption.
                        }
                        {
                            assumption.
                        }
                    }
                    {
                        unfold matchesb; simpl.
                        rewrite andb_true_iff.
                        unfold matchesb in IHao; simpl in IHao.
                        split.
                        {
                            apply IHao.
                            exact H1.
                        }
                        {
                            unfold matchesb; simpl.
                            apply bool_decide_eq_true.
                            assumption.
                        }
                    }
                }
                {
                    cbn in *.
                    rewrite bind_Some in H0.
                    destruct H0 as [x [H1 H2]].
                    rewrite bind_Some in H2.
                    destruct H2 as [x0 H2].
                    destruct H2 as [H2 H3].
                    inversion H3; subst; clear H3.
                    specialize (IHao1 _ H1).
                    specialize (IHao2 _ H2).
                    cbn.
                    unfold matchesb; simpl.
                    rewrite andb_true_iff.
                    split; assumption.
                }
            }
            {
                
                remember (fun (v:builtin_value) (e':Expression) =>
                    match Expression_evaluate ρ e' with
                    | Some v' => v'
                    | None => term_operand v
                    end
                ) as zipper.
                remember (fun (s1 s2 : symbol) => s1) as symleft.
                remember (fun (g : PreTerm' symbol builtin_value) (e' : Expression) =>
                    (term_preterm g)
                ) as f1.
                remember (fun (b : builtin_value) (et : PreTerm' symbol Expression) =>
                    (@term_operand symbol _ b)
                ) as f2.
                remember (PreTerm'_zipWith symleft zipper f1 f2 ao0 ao) as zipped.
                exists (term_preterm zipped).
                cbn.
                split.
                {
                    exists zipped.
                    subst.
                    repeat constructor.
                    clear -H.
                    apply matchesb_satisfies in H.

                    induction H.
                    {
                        simpl.
                        cbn.
                        reflexivity.
                    }
                    {
                        cbn in s.
                        cbn.
                        rewrite bind_Some.
                        cbn.
                        ltac1:(
                            under [fun e => _]functional_extensionality => e
                        ).
                        {
                            ltac1:(rewrite bind_Some).
                            ltac1:(
                                under [fun e' => _]functional_extensionality => e'
                            ).
                            {
                                ltac1:(rewrite inj_iff).
                                ltac1:(over).
                            }
                            ltac1:(over).
                        }
                        cbn in *.
                        eexists.
                        split>[apply IHaoxy_satisfies_aoxz|].
                        eexists.
                        split>[apply s|].
                        apply f_equal.
                        rewrite s.
                        reflexivity.
                    }
                    {
                        cbn in s.
                        cbn.
                        rewrite bind_Some.
                        cbn in *.
                        ltac1:(
                            under [fun e => _]functional_extensionality => e
                        ).
                        {
                            ltac1:(rewrite bind_Some).
                            ltac1:(
                                under [fun e' => _]functional_extensionality => e'
                            ).
                            {
                                ltac1:(rewrite inj_iff).
                                ltac1:(over).
                            }
                            ltac1:(over).
                        }
                        cbn in *.
                        eexists.
                        split>[apply IHaoxy_satisfies_aoxz|].
                        eexists.
                        split>[apply s|].
                        reflexivity.
                    }
                    {
                        unfold satisfies in s; simpl in s.
                        inversion s.
                    }
                    {
                        cbn in H0.
                        cbn.
                        rewrite bind_Some.
                        cbn in *.
                        ltac1:(
                            under [fun e => _]functional_extensionality => e
                        ).
                        {
                            ltac1:(rewrite bind_Some).
                            ltac1:(
                                under [fun e' => _]functional_extensionality => e'
                            ).
                            {
                                ltac1:(rewrite inj_iff).
                                ltac1:(over).
                            }
                            ltac1:(over).
                        }
                        cbn in *.
                        eexists.
                        split>[apply IHaoxy_satisfies_aoxz1|].
                        eexists.
                        split>[apply IHaoxy_satisfies_aoxz2|].
                        reflexivity.
                    }
                }
                {
                    subst. cbn.
                    apply f_equal.
                    apply matchesb_satisfies in H.
                    induction H.
                    {
                        cbn. reflexivity.
                    }
                    {
                        cbn in *.
                        rewrite s.
                        rewrite IHaoxy_satisfies_aoxz.
                        reflexivity.
                    }
                    {
                        cbn in *.
                        rewrite IHaoxy_satisfies_aoxz.
                        reflexivity.
                    }
                    {
                        unfold satisfies in s; simpl in s.
                        inversion s.
                    }
                    {
                        cbn in *.
                        rewrite IHaoxy_satisfies_aoxz1.
                        rewrite IHaoxy_satisfies_aoxz2.
                        reflexivity.
                    }
                }
            }
        }
        {
            cbn.
            split; intros H.
            {
                destruct H as [e H].
                destruct H as [H1 H2].
                destruct H1 as [e' [H11 H12]].
                subst. cbn in *.
                inversion H2.
            }
            {
                inversion H.
            }
        }
    }
    {
        ltac1:(
            under [fun e => _]functional_extensionality => e
        ).
        {
            ltac1:(rewrite bind_Some).
            ltac1:(
                under [fun e' => _]functional_extensionality => e'
            ).
            {
                ltac1:(rewrite inj_iff).
                ltac1:(over).
            }
            ltac1:(over).
        }
        cbn.
        destruct g; cbn.
        {
            split; intros H.
            {
                destruct H as [e H].
                destruct H as [[e' [H'1 H'2]] H].
                subst.
                cbn in H.
                subst.
                unfold matchesb; simpl.
                unfold matchesb; simpl.
                apply bool_decide_eq_true.
                assumption.
            }
            {
                eexists.
                split.
                {
                    unfold matchesb in H; simpl in H.
                    unfold matchesb in H; simpl in H.
                    apply bool_decide_eq_true in H.
                    eexists. split>[|reflexivity].
                    apply H.
                }
                {
                    cbn. reflexivity.
                }
            }
        }
        {
            split; intros H.
            {
                destruct H as [e H].
                destruct H as [[e' [H'1 H'2]] H].
                subst.
                cbn in H.
                subst.
                do 2 (unfold matchesb; simpl).
                apply bool_decide_eq_true.
                assumption.
            }
            {
                eexists.
                split.
                {
                    do 2 (unfold matchesb in H; simpl in H).
                    apply bool_decide_eq_true in H.
                    eexists. split>[|reflexivity].
                    apply H.
                }
                {
                    cbn. reflexivity.
                }
            }
        }
    }
Qed.

Definition try_match_lhs_with_sc
    {Σ : StaticModel}
    {Act : Set}
    (g : GroundTerm)
    (r : RewritingRule Act)
    : option Valuation
:=
    ρ ← try_match g (fr_from r);
    let validates := matchesb ρ () (fr_scs r) in
    if validates then Some ρ else None
.

(*
#[global]
Instance VarsOf_list_SideCondition
    {Σ : StaticModel}
    :
    VarsOf (list SideCondition) variable
:= {|
    vars_of := fun scs => union_list (vars_of <$> scs) ;
|}.
*)

Lemma bind_Some_T_1
    (A B : Type)
    (f : A -> option B)
    (mx : option A)
    (y : B)
    :
    (mbind f mx) = Some y ->
    {x : A & mx = Some x /\ f x = Some y}
.
Proof.
    intros HH.
    destruct mx; simpl in *.
    {
        exists a.
        split>[reflexivity|exact HH].
    }
    { inversion HH. }
Qed.

Lemma bind_Some_T_2
    (A B : Type)
    (f : A -> option B)
    (mx : option A)
    (y : B)
    :
    {x : A & mx = Some x /\ f x = Some y} ->
    (mbind f mx) = Some y
.
Proof.
    intros HH.
    destruct HH as [x HH].
    destruct HH as [H1 H2].
    destruct mx; simpl in *.
    {
        inversion H1; subst; clear H1.
        exact H2.
    }
    {
        inversion H1.
    }
Qed.

Lemma bind_None_T_1 (A B : Type) (f : A → option B) (mx : option A):
  mbind f mx = None ->
  (mx = None) +
  ({ x : A & mx = Some x ∧ f x = None })
.
Proof.
    intros H.
    destruct mx; simpl in *.
    {
        right. exists a. split>[reflexivity|]. exact H.
    }
    {
        left. reflexivity.
    }
Qed.

Lemma try_match_lhs_with_sc_complete
    {Σ : StaticModel}
    {Act : Set}
    (g : GroundTerm)
    (r : RewritingRule Act)
    (ρ : gmap variable GroundTerm)
    :
    vars_of (fr_scs r) ⊆ vars_of (fr_from r) ->
    matchesb ρ g (fr_from r) = true ->
    matchesb ρ () (fr_scs r) = true ->
    {
        ρ' : (gmap variable GroundTerm) &
        vars_of ρ' = vars_of (fr_from r) ∧
        ρ' ⊆ ρ ∧
        try_match_lhs_with_sc g r = Some ρ'
    }   
.
Proof.
    (*
        If a side condition `sc` contains a variable
        that is not in the 'from' part `fr` of the rule,
        then the side condition evaluates to `false`.
        Why?
        Because if it evaluated to `true`,
        then `vars_of sc ⊆ vars_of ρ `.
        But vars_of ρ = vars_of fr, because of
        the NOOTA property.
    *)
    intros Hn H1 H2.
    (*
    assert (H10 := H1).
    assert (H20 := H2).*)
    apply try_match_complete in H1.
    destruct H1 as [ρ1 [H1ρ1 H2ρ1]].
    destruct H2ρ1 as [H2ρ1 H3ρ2].
    (*destruct (matchesb ρ1 () (fr_scs r)) eqn:Hm.*)
    {
        
        unfold try_match_lhs_with_sc.
        (* ltac1:(setoid_rewrite bind_Some). *)
        exists ρ1.
        split.
        {
            unfold Valuation in *.
            rewrite H1ρ1.
            reflexivity.
        }
        split.
        {
            assumption.
        }
        apply bind_Some_T_2.
        exists ρ1.
        split>[apply H3ρ2|].
        unfold matchesb in *; simpl in *.
        ltac1:(case_match).
        { reflexivity. }
        rewrite forallb_forall in H2.
        assert (HH : ~ (forallb [eta matchesb ρ1 ()] (fr_scs r) = true)).
        {
            intros HContra.
            unfold matchesb in *; simpl in *.
            rewrite HContra in H. inversion H.
        }
        clear H.
        rewrite forallb_forall in HH.
        ltac1:(exfalso).
        apply HH. clear HH.
        intros x Hx.
        specialize (H2 x Hx).
        erewrite matchesb_insensitive in H2. apply H2.
        unfold valuation_restrict.
        rewrite map_eq_iff.
        intros i.
        do 2 (rewrite map_lookup_filter).
        unfold Valuation in *.
        
        destruct (ρ!!i) eqn:Hρi, (ρ1!!i) eqn:Hρ1i; simpl in *.
        {
            ltac1:(repeat case_guard; simpl in *; simplify_eq/=; try reflexivity).
            ltac1:(rewrite map_subseteq_spec in H2ρ1).
            specialize (H2ρ1 i).
            specialize (H2ρ1 g1 Hρ1i).
            ltac1:(simplify_eq/=).
            reflexivity.
        }
        {
            ltac1:(repeat case_guard; simpl in *; simplify_eq/=; try reflexivity).
            ltac1:(exfalso).

            ltac1:(cut(i ∈ vars_of ρ1)).
            {
                intros HHH. unfold vars_of in HHH; simpl in HHH.
                rewrite elem_of_dom in HHH.
                destruct HHH as [s Hs].
                rewrite Hs in Hρ1i.
                inversion Hρ1i.
            }
            clear H2ρ1.
            rewrite H1ρ1.
            clear H1ρ1.
            eapply elem_of_weaken>[|apply Hn].
            clear Hn.
            rewrite <- elem_of_list_In in Hx.
            unfold vars_of; simpl.
            rewrite elem_of_union_list.
            exists (vars_of x).
            split>[|assumption].
            rewrite elem_of_list_fmap.
            exists x.
            split>[reflexivity|].
            exact Hx.
        }
        {
            ltac1:(exfalso).
            eapply lookup_weaken in Hρ1i>[|apply H2ρ1].
            rewrite Hρi in Hρ1i.
            inversion Hρ1i.
        }
        {
            reflexivity.
        }
    }
Qed.

Lemma valuation_restrict_vars_of_self
    {Σ : StaticModel}
    (ρ' ρ : gmap variable GroundTerm)
    :
    ρ' ⊆ ρ  ->
    valuation_restrict ρ' (vars_of ρ') = valuation_restrict ρ (vars_of ρ')
.
Proof.
    intros H.
    rewrite map_eq_iff.
    unfold valuation_restrict.
    intros i.
    rewrite map_lookup_filter.
    rewrite map_lookup_filter.
    destruct (ρ' !! i) eqn:Hρ'i.
    {
        simpl.
        ltac1:(repeat case_guard; simpl in *; simplify_eq/=).
        {
            assert (Hρi: ρ !! i = Some g).
            {
                eapply lookup_weaken>[|apply H].
                assumption.
            }
            rewrite Hρi.
            simpl.
            reflexivity.
        }
        {
            destruct (ρ !! i); reflexivity.
        }
    }
    {
        simpl.
        destruct (ρ!!i) eqn:Hρi; simpl.
        {
            ltac1:(repeat case_guard; simpl in *; simplify_eq/=; try reflexivity; exfalso).
            unfold vars_of in *; simpl in *.
            rewrite elem_of_dom in H0.
            destruct H0 as [g' Hg'].
            rewrite Hρ'i in Hg'.
            inversion Hg'.
        }
        {
            reflexivity.
        }
    }
Qed.

Definition thy_lhs_match_one
    {Σ : StaticModel}
    {Act : Set}
    (e : GroundTerm)
    (Γ : list (RewritingRule Act))
    : option (RewritingRule Act * Valuation * nat)%type
:=
    let froms : list SymbolicTerm
        := fr_from <$> Γ
    in
    let vs : list (option Valuation)
        := (try_match_lhs_with_sc e) <$> Γ
    in
    let found : option (nat * option Valuation)
        := list_find isSome vs
    in
    nov ← found;
    let idx : nat := nov.1 in
    let ov : option Valuation := nov.2 in
    v ← ov;
    r ← Γ !! idx;
    Some (r, v, idx)
.

Lemma thy_lhs_match_one_None
    {Σ : StaticModel}
    {Act : Set}
    (e : GroundTerm)
    (Γ : RewritingTheory Act)
    (wfΓ : RewritingTheory_wf Γ)
    :
    thy_lhs_match_one e Γ = None ->
    notT { r : RewritingRule Act & { ρ : Valuation &
        ((r ∈ Γ) * (satisfies ρ e (fr_from r)) * (satisfies ρ tt (fr_scs r)))%type
    } }
        
.
Proof.
    unfold thy_lhs_match_one.
    intros H [r [ρ [[Hin HContra1] HContra2]]].
    destruct (list_find isSome (try_match_lhs_with_sc e <$> Γ)) eqn:Heqfound.
    {
        destruct p as [n oρ].
        rewrite list_find_Some in Heqfound.
        rewrite bind_None in H.
        ltac1:(destruct H as [H|H];[inversion H|]).
        destruct H as [[idx ρ2][H1 H2]].
        simpl in H2.
        inversion H1; subst; clear H1.
        ltac1:(destruct Heqfound as [Hfound [HSome HFirst]]).
        apply bind_None_T_1 in H2.
        destruct H2 as [H2|H2].
        {
            rewrite H2 in HSome. inversion HSome.
        }
        {
            destruct H2 as [x [H21 H22]].
            apply bind_None_T_1 in H22.
            destruct H22 as [H22|H22].
            {
                rewrite list_lookup_fmap in Hfound.
                rewrite H22 in Hfound.
                simpl in Hfound. inversion Hfound.
            }
            {
                subst ρ2.
                destruct H22 as [x0 [H221 HContra]].
                inversion HContra.
            }
        }
    }
    {
        clear H.
        rewrite list_find_None in Heqfound.
        rewrite Forall_forall in Heqfound.
        ltac1:(rename HContra1 into Hsat1).
        ltac1:(rename HContra2 into Hsat2).
        apply satisfies_matchesb in Hsat1.
        apply satisfies_matchesb in Hsat2.
        apply try_match_complete in Hsat1.
        destruct Hsat1 as [ρ' [H1 [H2 H3]]].

        assert (Hc := try_match_lhs_with_sc_complete e r).
        specialize (Hc ρ').
        ltac1:(ospecialize (Hc _)).
        {
            unfold RewritingTheory_wf in wfΓ.
            unfold is_true in wfΓ.
            specialize (wfΓ r).
            unfold RewritingRule_wf in wfΓ.
            specialize (wfΓ Hin).
            apply wfΓ.
        }
        assert (H3' := H3).
        apply try_match_correct in H3'.
        specialize (Hc H3').
        ltac1:(ospecialize (Hc _)).
        {
            erewrite matchesb_insensitive.
            apply Hsat2.
            unfold RewritingTheory_wf in wfΓ.
            unfold is_true in wfΓ.
            specialize (wfΓ r).
            unfold RewritingRule_wf in wfΓ.
            specialize (wfΓ Hin).
            eapply valuation_restrict_eq_subseteq.
            { apply wfΓ. }
            rewrite <- H1.
            clear -H2.
            apply valuation_restrict_vars_of_self.
            assumption.
        }
        destruct Hc as [ρ'' [H1ρ'' [H2ρ'' H3ρ'']]].

        specialize (Heqfound (Some ρ'')).
        ltac1:(ospecialize (Heqfound _)).
        {
            clear Heqfound.
            
            unfold Valuation in *.
            rewrite elem_of_list_fmap.
            exists (r).
            split.
            {
                symmetry.
                exact H3ρ''.
            }
            {
                exact Hin.
            }
        }
        apply Heqfound.
        unfold isSome.
        reflexivity.
    }
Qed.


Lemma fmap_Some_T_1 (A B : Type) (f : A → B) (mx : option A) (y : B):
  f <$> mx = Some y ->
  {x : A & mx = Some x ∧ y = f x }
.
Proof.
    intros H.
    destruct mx; simpl in *.
    {
        inversion H; subst; clear H.
        exists a.
        split;reflexivity.
    }
    {
        inversion H.
    }
Qed.

Lemma thy_lhs_match_one_Some
    {Σ : StaticModel}
    {Act : Set}
    (e : GroundTerm)
    (Γ : list (RewritingRule Act))
    (r : RewritingRule Act)
    (ρ : Valuation)
    (rule_idx : nat)
    :
    thy_lhs_match_one e Γ = Some (r, ρ, rule_idx) ->
    ((r ∈ Γ) * (satisfies ρ e (fr_from r)) * (satisfies ρ tt (fr_scs r)))%type
.
Proof.
    intros H.
    unfold thy_lhs_match_one in H.
    unfold is_Some in H.
    (repeat ltac1:(case_match)); subst.
    {
        apply bind_Some_T_1 in H.
        destruct H as [[idx oρ][H1 H2]].
        simpl in *.
        rewrite list_find_Some in H1.
        destruct H1 as [H11 H12].
        rewrite list_lookup_fmap in H11.
        apply fmap_Some_T_1 in H11.
        destruct H11 as [ot [Hot1 Hot2]].
        subst.
        apply bind_Some_T_1 in H2.
        destruct H2 as [ρ' [H1ρ' H2ρ']].
        apply bind_Some_T_1 in H2ρ'.
        destruct H2ρ' as [r' [H1r' H2r']].
        inversion H2r'; subst; clear H2r'.
        rewrite Hot1 in H1r'.
        inversion H1r'; subst; clear H1r'.
        split.
        {
            split.
            {
                rewrite elem_of_list_lookup.
                exists rule_idx. apply Hot1.
            }
            {
                destruct H12 as [H1 H2].
                unfold is_true, isSome in H1.
                destruct (try_match_lhs_with_sc e r) eqn:HTM>[|inversion H1].
                clear H1.
                inversion H1ρ'; subst; clear H1ρ'.
                unfold try_match_lhs_with_sc in HTM.
                apply bind_Some_T_1 in HTM.
                destruct HTM as [x [H1x H2x]].
                destruct (matchesb x () (fr_scs r)) eqn:Heq.
                {
                    inversion H2x; subst; clear H2x.
                    apply try_match_correct in H1x.
                    apply matchesb_satisfies in Heq.
                    apply matchesb_satisfies in H1x.
                    assumption.
                }
                {
                    inversion H2x.
                }         
            }
        }
        {
            destruct H12 as [H1 H2].
            unfold is_true, isSome in H1.
            destruct (try_match_lhs_with_sc e r) eqn:HTM>[|inversion H1].
            clear H1.
            inversion H1ρ'; subst; clear H1ρ'.
            unfold try_match_lhs_with_sc in HTM.
            apply bind_Some_T_1 in HTM.
            destruct HTM as [x [H1x H2x]].
            destruct (matchesb x () (fr_scs r)) eqn:Heq.
            {
                inversion H2x; subst; clear H2x.
                apply try_match_correct in H1x.
                apply matchesb_satisfies in Heq.
                apply matchesb_satisfies in H1x.
                assumption.
            }
            {
                inversion H2x.
            }
        }
    }
Qed.


Definition flat_naive_interpreter_ext
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule Act))
    (e : GroundTerm)
    : option (GroundTerm*nat)
:=
    let oρ : option ((RewritingRule Act)*Valuation*nat)
        := thy_lhs_match_one e Γ in
    match oρ with
    | None => None
    | Some (r,ρ,idx) =>
        e' ← (evaluate_rhs_pattern ρ (fr_to r));
        Some (e',idx)
    end
.

Definition flat_naive_interpreter
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    (e : GroundTerm)
    : option (GroundTerm)
:=
    ei ← flat_naive_interpreter_ext Γ e;
    Some ei.1
.




Lemma flat_naive_interpreter_sound
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    : FlatInterpreter_sound Γ (flat_naive_interpreter Γ).
Proof.
    unfold FlatInterpreter_sound.
    intros wfΓ.
    unfold flat_naive_interpreter.
    unfold FlatInterpreter_sound.
    unfold flat_stuck,not_stuck_flat.
    unfold flat_naive_interpreter_ext.
    repeat split.
    {
        intros e1 e2.
        intros Hbind.
        apply bind_Some_T_1 in Hbind.
        destruct Hbind as [x [H1x H2x]].
        destruct (thy_lhs_match_one e1 Γ) eqn:Hmatch.
        {
            destruct p as [[r ρ] idx].
            apply thy_lhs_match_one_Some in Hmatch.
            inversion H2x; subst; clear H2x.
            apply bind_Some_T_1 in H1x.
            destruct H1x as [y [H1y H2y]].
            inversion H2y; subst; clear H2y.
            simpl.
            unfold rewriting_relation_flat.
            exists r.
            destruct Hmatch as [[Hin Hm1] Hm2].
            exists (fr_act r).
            split>[apply Hin|].
            unfold flattened_rewrites_to.
            exists ρ.
            unfold flattened_rewrites_in_valuation_under_to.
            repeat split; try assumption.
            apply evaluate_rhs_pattern_correct in H1y.
            apply matchesb_satisfies in H1y.
            exact H1y.
        }
        {
            inversion H1x.
        }
    }
    {
        intros e Hstuck.
        destruct (thy_lhs_match_one e Γ) eqn:Hmatch>[|reflexivity].
        {
            destruct p as [[r ρ] rule_idx].
            {
                apply thy_lhs_match_one_Some in Hmatch.
                destruct Hmatch as [Hin Hsat].
                assert (Hts := @thy_lhs_match_one_Some Σ).
                unfold rewriting_relation_flat in Hstuck.
                unfold flattened_rewrites_to in Hstuck.
                unfold flattened_rewrites_in_valuation_under_to in Hstuck.
                assert (Hev := evaluate_rhs_pattern_correct (fr_to r) ρ).
                ltac1:(cut (~ ∃ g', evaluate_rhs_pattern ρ (fr_to r) = Some g')).
                {
                    intros HContra. clear -HContra.
                    rewrite <- eq_None_ne_Some.
                    intros x HC.
                    rewrite bind_Some in HC.
                    destruct HC as [x0 [HC1 HC2]].
                    inversion HC2; subst; clear HC2.
                    rewrite bind_Some in HC1.
                    ltac1:(naive_solver).
                }
                intros HContra.
                destruct HContra as [pg' Hg'].
                rewrite Hev in Hg'.
                clear Hev.
                apply matchesb_satisfies in Hg'.
                apply Hstuck. clear Hstuck.
                exists pg'. exists r.
                exists (fr_act r).
                destruct Hin.
                split>[assumption|].
                exists ρ.
                repeat split; try assumption.
            }
        }
    }
    {
        intros e Hnotstuck.
        unfold flat_naive_interpreter.

        destruct Hnotstuck as [e' He'].
        unfold rewriting_relation_flat in He'.
        destruct He' as [r' [a [H1r' H2r']]].
        unfold flattened_rewrites_to in H2r'.
        destruct H2r' as [ρ' Hρ'].
        unfold flattened_rewrites_in_valuation_under_to in Hρ'.

        
        destruct (thy_lhs_match_one e Γ) eqn:Hmatch.
        {
            destruct p as [[r ρ] rule_idx]; cbn in *.
            apply thy_lhs_match_one_Some in Hmatch.
            destruct Hmatch as [Hin Hsat].
            
            
            destruct (evaluate_rhs_pattern ρ (fr_to r)) eqn:Heval.
            {
                eexists. reflexivity.
            }
            {
                ltac1:(exfalso).
                unfold RewritingTheory_wf in wfΓ.
                unfold RewritingRule_wf in wfΓ.
                specialize (wfΓ r).
                destruct Hin.
                specialize (wfΓ ltac:(assumption)).
                destruct wfΓ as [wf1 wf2].
                unfold RewritingRule_wf2 in wf2.
                specialize (wf2 e ρ).
                specialize (wf2 ltac:(assumption) ltac:(assumption)).
                destruct wf2 as [g' Hg'].
                apply satisfies_matchesb in Hg'.
                assert (Hn : notT { g : _ & evaluate_rhs_pattern ρ (fr_to r) = Some g } ).
                {
                    intros HContra.
                    destruct HContra as [g HContra].
                    rewrite Heval in HContra.
                    inversion HContra.
                }
                apply Hn. clear Hn.
                exists g'.
                rewrite evaluate_rhs_pattern_correct.
                apply Hg'.
            }
        }
        {
            ltac1:(exfalso).
            destruct Hρ' as [[[H1 H2] H3] H4].
            apply thy_lhs_match_one_None in Hmatch.
            apply Hmatch.
            exists r'. exists ρ'.
            (repeat split); try assumption.
            assumption.
        }
    }
Qed.


Definition naive_interpreter
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (e : TermOver builtin_value)
    : option (TermOver builtin_value)
:=
    ei ← flat_naive_interpreter_ext (fmap r_to_fr Γ) (uglify' e);
    Some (prettify ei.1)
.

Lemma vars_of_E2conv
    {Σ : StaticModel}
    (e : Expression2)
    :
    vars_of (Expression2_to_Expression e) = vars_of e
.
Proof.
    induction e; unfold vars_of in *; simpl in *;
        (ltac1:(set_solver)).
Qed.

Lemma vars_of_sc2_to_sc
    {Σ : StaticModel}
    {Act : Set}
    (r2 : RewritingRule2 Act)
    :
    vars_of (sc2_to_sc <$> r_scs r2) ⊆ vars_of (r_scs r2)
.
Proof.
    clear Hwf1.
    unfold vars_of in *; simpl in *.
    unfold vars_of in *; simpl in *.
    unfold vars_of_SideCondition.
    rewrite elem_of_subseteq.
    intros x Hx.
    rewrite elem_of_union_list in Hx.
    rewrite elem_of_union_list.
    destruct Hx as [X [H1X H2x]].
    rewrite elem_of_list_fmap in H1X.
    destruct H1X as [y [H1y H2y]].
    subst X.
    destruct y; simpl in *.
    rewrite elem_of_list_fmap in H2y.
    destruct H2y as [y [H1'y H2'y]].
    destruct c; simpl in *.
    destruct y; simpl in *.
    inversion H1'y; subst; clear H1'y.
    ltac1:(exists (vars_of
        (apeq (Expression2_to_Expression sc_left)
        (Expression2_to_Expression sc_right)))).
    split>[|assumption].
    destruct r2; simpl in *.
    rewrite elem_of_list_fmap.
    eexists;split>[|exact H2'y].
    unfold vars_of; simpl.
    rewrite vars_of_E2conv.
    rewrite vars_of_E2conv.
    reflexivity.
Qed.

Lemma compose_prettify_uglify
    {Σ : StaticModel}
    (A : Type)
    :
    (@prettify Σ A) ∘ uglify' = id
.
Proof.
    apply functional_extensionality.
    intros x.
    unfold compose.
    rewrite (cancel prettify uglify').
    reflexivity.
Qed.

Lemma compose_uglify_prettify
    {Σ : StaticModel}
    (A : Type)
    :
    uglify' ∘ (@prettify Σ A) = id
.
Proof.
    apply functional_extensionality.
    intros x.
    unfold compose.
    rewrite (cancel uglify' prettify).
    reflexivity.
Qed.

Lemma fmap_prettify_uglify_val
    {Σ : StaticModel}
    (ρ : Valuation2)
    :
    (prettify <$> (uglify' <$> ρ)) = ρ
.
Proof.
    unfold Valuation2 in *.
    rewrite <- map_fmap_compose.
    rewrite compose_prettify_uglify.
    rewrite map_fmap_id.
    reflexivity.
Qed.

Lemma fmap_uglify_prettify_val
    {Σ : StaticModel}
    (ρ : Valuation)
    :
    uglify' <$> (prettify <$> (ρ)) = ρ
.
Proof.
    unfold Valuation2 in *.
    rewrite <- map_fmap_compose.
    rewrite compose_uglify_prettify.
    rewrite map_fmap_id.
    reflexivity.
Qed.


#[export]
Instance cancel_fr_r
    {Σ : StaticModel}
    {Act : Set}
    : Cancel eq (@fr_to_r _ Act) r_to_fr
.
Proof.
    intros r. destruct r. simpl.
    rewrite (cancel prettify uglify').
    rewrite (cancel prettify uglify').
    rewrite (cancel (TermOver_map Expression_to_Expression2) (TermOver_map Expression2_to_Expression)).
    f_equal.
    induction r_scs; simpl.
    { reflexivity. }
    {
        do 2 (rewrite (cancel Expression_to_Expression2 Expression2_to_Expression)).
        f_equal.
        {
            destruct a; reflexivity.
        }
        apply IHr_scs.
    }
Qed.

Lemma naive_interpreter_sound
    {Σ : StaticModel}
    {Act : Set}
    {_eA : EqDecision Act}
    (Γ : list (RewritingRule2 Act))
    : Interpreter_sound Γ (naive_interpreter Γ).
Proof.
    intros Hwf.
    assert(Hsound := flat_naive_interpreter_sound (fmap r_to_fr Γ)).
    ltac1:(ospecialize (Hsound _)).
    {
        clear -Hwf _eA.
        unfold RewritingTheory_wf.
        unfold RewritingTheory2_wf in Hwf.
        intros r Hr.
        apply elem_of_list_fmap_T_1 in Hr.
        destruct Hr as [r2 [H1r2 H2r2]].
        subst r.
        specialize (Hwf _ H2r2). clear H2r2.
        unfold RewritingRule_wf.
        unfold RewritingRule2_wf in Hwf.
        destruct Hwf as [Hwf1 Hwf2].
        split.
        {
            unfold RewritingRule_wf1.
            unfold RewritingRule2_wf1 in Hwf1.
            simpl.
            ltac1:(rewrite vars_of_uglify').
            eapply transitivity>[|apply Hwf1].
            apply vars_of_sc2_to_sc.
        }
        {
            unfold RewritingRule_wf2.
            unfold RewritingRule2_wf2 in Hwf2.
            intros g ρ.
            specialize (Hwf2 (prettify g) (fmap prettify ρ)).
            intros H1 H2.
            ltac1:(ospecialize (Hwf2 _ _)).
            {
                unfold satisfies; simpl.
                apply uglify_sat2B.
                rewrite fmap_uglify_prettify_val.
                rewrite (cancel uglify' prettify).
                apply H1.
            }
            {
                unfold satisfies; simpl.
                unfold satisfies in H2; simpl in H2.
                intros x Hx.
                specialize (H2 (sc2_to_sc x)).
                ltac1:(ospecialize (H2 _)).
                {
                    clear H2.
                    rewrite elem_of_list_fmap.
                    exists x.
                    split>[reflexivity|exact Hx].
                }
                unfold satisfies; simpl.
                unfold satisfies in H2; simpl in H2.
                unfold satisfies in H2; simpl in H2.
                do 2 (rewrite Expression2_Expression_evaluate).
                rewrite (fmap_uglify_prettify_val).
                destruct H2 as [H21 H22].
                rewrite H21. reflexivity.
            }
            destruct Hwf2 as [g' H3].
            exists (uglify' g').
            unfold satisfies in H3; simpl in H3.
            apply sat2E_uglify in H3.
            rewrite fmap_uglify_prettify_val in H3.
            apply H3.
        }
    }
    unfold Interpreter_sound'.
    unfold FlatInterpreter_sound' in Hsound.
    destruct Hsound as [[Hsound1 Hsound2] Hsound3].
    repeat split.
    {
        intros e1 e2 HH.
        specialize (Hsound1 (uglify' e1) (uglify' e2)).
        unfold naive_interpreter in HH.
        apply bind_Some_T_1 in HH.
        destruct HH as [[t n] [HH1 HH2]].
        simpl in *.
        injection HH2 as HH2. subst e2.
        ltac1:(ospecialize (Hsound1 _)).
        {
            apply bind_Some_T_2.
            exists (t, n).
            rewrite HH1.
            split>[reflexivity|].
            simpl.
            rewrite (cancel uglify' prettify).
            reflexivity.
        }
        rewrite (cancel uglify' prettify) in Hsound1.
        unfold rewriting_relation_flat in Hsound1.
        destruct Hsound1 as [r [a [HH2 HH3]]].
        unfold rewriting_relation.
        exists (fr_to_r r).
        exists a.
        split.
        {
            rewrite elem_of_list_fmap in HH2.
            destruct HH2 as [y [HH2 HH2']].
            subst r.
            rewrite (cancel fr_to_r r_to_fr).
            exact HH2'.
        }
        unfold rewrites_to.
        unfold flattened_rewrites_to in HH3.
        destruct HH3 as [ρ Hρ].
        exists (fmap prettify ρ).
        unfold rewrites_in_valuation_under_to.
        unfold flattened_rewrites_in_valuation_under_to in Hρ.
        destruct Hρ as [[[HH4 HH5] HH6] HH7].
        unfold satisfies; simpl.
        (repeat split).
        {
            apply uglify_sat2B.
            rewrite fmap_uglify_prettify_val.
            destruct r;  simpl in *.
            rewrite (cancel uglify' prettify).
            exact HH4.
        }
        {
            apply uglify_sat2E.
            rewrite fmap_uglify_prettify_val.
            destruct r;  simpl in *.
            rewrite (cancel (TermOver_map Expression2_to_Expression) (TermOver_map Expression_to_Expression2)).
            unfold satisfies; simpl.
            do 2 (rewrite (cancel uglify' prettify)).
            exact HH5.
        }
        {
            intros x Hx.
            unfold satisfies in HH6; simpl in HH6.
            specialize (HH6 (sc2_to_sc x)).
            ltac1:(ospecialize (HH6 _)).
            {
                destruct r; simpl in *.
                rewrite elem_of_list_fmap in Hx.
                destruct Hx as [y [H1y H2y]].
                subst x.
                rewrite (cancel sc2_to_sc sc_to_sc2).
                exact H2y.
            }
            unfold satisfies; simpl.
            unfold satisfies in HH6; simpl in HH6.
            rewrite Expression2_Expression_evaluate.
            rewrite Expression2_Expression_evaluate.
            rewrite (fmap_uglify_prettify_val).
            apply f_equal.
            apply HH6.
        }
        {
            destruct r; simpl in *.
            apply HH7.
        }
    }
    {
        intros e Hstuck.
        specialize (Hsound2 (uglify' e)).
        ltac1:(ospecialize (Hsound2 _)).
        {
            unfold stuck in Hstuck.
            unfold flat_stuck.
            intros HContra. apply Hstuck. clear Hstuck.
            unfold not_stuck. unfold not_stuck_flat in HContra.
            destruct HContra as [e' He'].
            exists (prettify e').
            unfold rewriting_relation.
            unfold rewriting_relation_flat in He'.
            destruct He' as [r [a [Hrewr1 Hrewr2]]].
            exists (fr_to_r r).
            exists a.
            split.
            {
                rewrite elem_of_list_fmap in Hrewr1.
                destruct Hrewr1 as [y [H1y H2y]].
                subst r.
                rewrite (cancel fr_to_r r_to_fr).
                exact H2y.
            }
            {
                unfold rewrites_to.
                unfold flattened_rewrites_to in Hrewr2.
                destruct Hrewr2 as [ρ Hρ].
                exists (fmap prettify ρ).
                unfold flattened_rewrites_in_valuation_under_to in Hρ.
                unfold rewrites_in_valuation_under_to.


                (* TODO this is a duplication *)
                destruct Hρ as [[[HH4 HH5] HH6] HH7].
                unfold satisfies; simpl.
                (repeat split).
                {
                    apply uglify_sat2B.
                    rewrite fmap_uglify_prettify_val.
                    destruct r;  simpl in *.
                    rewrite (cancel uglify' prettify).
                    exact HH4.
                }
                {
                    apply uglify_sat2E.
                    rewrite fmap_uglify_prettify_val.
                    destruct r;  simpl in *.
                    rewrite (cancel (TermOver_map Expression2_to_Expression) (TermOver_map Expression_to_Expression2)).
                    unfold satisfies; simpl.
                    do 2 (rewrite (cancel uglify' prettify)).
                    exact HH5.
                }
                {
                    intros x Hx.
                    unfold satisfies in HH6; simpl in HH6.
                    specialize (HH6 (sc2_to_sc x)).
                    ltac1:(ospecialize (HH6 _)).
                    {
                        destruct r; simpl in *.
                        rewrite elem_of_list_fmap in Hx.
                        destruct Hx as [y [H1y H2y]].
                        subst x.
                        rewrite (cancel sc2_to_sc sc_to_sc2).
                        exact H2y.
                    }
                    unfold satisfies; simpl.
                    unfold satisfies in HH6; simpl in HH6.
                    rewrite Expression2_Expression_evaluate.
                    rewrite Expression2_Expression_evaluate.
                    rewrite (fmap_uglify_prettify_val).
                    apply f_equal.
                    apply HH6.
                }
                {
                    destruct r; simpl in *.
                    apply HH7.
                }
            }
        }
        unfold naive_interpreter.
        unfold flat_naive_interpreter in Hsound2.
        rewrite bind_None in Hsound2.
        rewrite bind_None.
        destruct Hsound2 as [Hsound2|Hsound2].
        {
            left. exact Hsound2.
        }
        {
            right.
            destruct Hsound2 as [[g n] [HH1 HH2]].
            inversion HH2.
        }
    }
    {
        intros e Hns.
        specialize (Hsound3 (uglify' e)).
        ltac1:(ospecialize (Hsound3 _)).
        {
            unfold not_stuck in Hns.
            unfold not_stuck_flat.
            destruct Hns as [e' He'].
            exists (uglify' e').
            unfold rewriting_relation in He'.
            unfold rewriting_relation_flat.
            destruct He' as [r [a [HH1 HH2]]].
            exists (r_to_fr r).
            exists a.
            repeat split.
            {
                rewrite elem_of_list_fmap.
                exists r.
                split>[reflexivity|exact HH1].
            }
            {
                unfold flattened_rewrites_to.
                unfold rewrites_to in HH2.
                destruct HH2 as [ρ Hρ].
                exists (fmap uglify' ρ).
                unfold rewrites_in_valuation_under_to in Hρ.
                destruct Hρ as [[[HH1' HH2] HH3] HH4].
                repeat split.
                {
                    unfold satisfies in *|-; simpl in *|-.
                    apply sat2B_uglify in HH1'.
                    destruct r; simpl in *. apply HH1'.
                }
                {
                    unfold satisfies in *|-; simpl in *|-.
                    apply sat2E_uglify in HH2.
                    destruct r; simpl in *. apply HH2.
                }
                {
                    unfold satisfies in *|-; simpl in *|-.
                    intros x.
                    specialize (HH3 (sc_to_sc2 x)).
                    intros Hx.
                    ltac1:(ospecialize (HH3 _)).
                    {
                        destruct r; simpl in *.
                        rewrite elem_of_list_fmap in Hx.
                        destruct Hx as [y [H1y H2y]].
                        subst x.
                        rewrite (cancel sc_to_sc2 sc2_to_sc).
                        exact H2y.
                    }
                    unfold satisfies in HH3; simpl in HH3.
                    unfold satisfies; simpl.
                    destruct x; simpl in *.
                    destruct c; simpl in *.
                    unfold satisfies; simpl.
                    (* FIXME the definition of constraint - when it holds. *)
                }
                {
                    subst a.
                    destruct r; simpl in *. exact HH4.
                }
            }
        }
    }
Qed.