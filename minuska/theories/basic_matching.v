
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    syntax_properties
    semantics_properties
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.


Definition valuation_restrict
    {Σ : StaticModel}
    {var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    (ρ : (gmap var GroundTerm))
    (r : gset var)
    : gmap var GroundTerm
:=
    filter
        (λ x : var * GroundTerm, x.1 ∈ r)
        ρ
.

Lemma valuation_restrict_eq_subseteq
    {Σ : StaticModel}
    {var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    (ρ1 ρ2 : (gmap var GroundTerm))
    (r r' : gset var)
:
    r ⊆ r' ->
    valuation_restrict ρ1 r' = valuation_restrict ρ2 r' ->
    valuation_restrict ρ1 r = valuation_restrict ρ2 r
.
Proof.
    intros H1 H2.
    unfold valuation_restrict in *.
    rewrite map_eq_iff.
    rewrite map_eq_iff in H2.
    intros x.
    specialize (H2 x).
    do 2 (rewrite map_lookup_filter in H2).
    do 2 (rewrite map_lookup_filter).
    simpl in *.
    rewrite elem_of_subseteq in H1.
    specialize (H1 x).
    unfold mbind,option_bind,mguard,option_guard in *; simpl in *.
    ltac1:(repeat case_match); try reflexivity;
        ltac1:(simplify_eq/=).
    { reflexivity. }
    { ltac1:(exfalso; naive_solver). }
    { ltac1:(exfalso; naive_solver). }
    { ltac1:(exfalso; naive_solver). }
Qed.

Lemma valuation_restrict_eq_impl_lookup
    {Σ : StaticModel}
    {var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    (ρ1 ρ2 : (gmap var GroundTerm))
    (r : gset var)
    (x : var)
    :
    x ∈ r ->
    valuation_restrict ρ1 r = valuation_restrict ρ2 r ->
    ρ1 !! x = ρ2 !! x
.
Proof.
    intros H1 H2.
    unfold valuation_restrict in H2.
    rewrite map_eq_iff in H2.
    specialize (H2 x).
    do 2 (rewrite map_lookup_filter in H2).
    unfold mguard,option_guard in H2.
    simpl in H2.
    destruct (decide_rel elem_of x r) eqn:Heq,
        (ρ1 !! x) eqn:Heq2,
        (ρ2 !! x) eqn:Heq3;
        simpl in *;
        try reflexivity;
        ltac1:(simplify_eq/=).
    {
        reflexivity.
    }
    {
        ltac1:(contradiction).
    }
    {
        ltac1:(contradiction).
    }
    {
        ltac1:(contradiction).
    }
Qed.

Class Matches
    {Σ : StaticModel}
    (A B var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VA : VarsOf B var}
    {_SAB : Satisfies (gmap var GroundTerm) A B var} :=
{
    matchesb:
        (gmap var GroundTerm) -> A -> B -> bool ;

    satisfies_matchesb :
        ∀ (v : (gmap var GroundTerm)) (a : A) (b : B),
            (satisfies v a b) -> (matchesb v a b = true) ;

    matchesb_satisfies :
        ∀ (v : (gmap var GroundTerm)) (a : A) (b : B),
            (matchesb v a b = true) -> (satisfies v a b) ;

    matchesb_vars_of :
        ∀ (v : (gmap var GroundTerm)) (a : A) (b : B),
            matchesb v a b = true ->
            vars_of b ⊆ vars_of v ;

    matchesb_insensitive :
        ∀ (v1 v2 : (gmap var GroundTerm)) (a : A) (b : B),
            valuation_restrict v1 (vars_of b) = valuation_restrict v2 (vars_of b) ->
            matchesb v1 a b = matchesb v2 a b ;            
}.
(* Set Typeclasses Debug. *)
Arguments satisfies : simpl never.
Arguments matchesb : simpl never.

Lemma matchesb_ext
    {Σ : StaticModel}
    (A B var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VA : VarsOf B var}
    {_SAB : Satisfies (gmap var GroundTerm) A B var}
    {_SPAB : SatisfiesProperties (gmap var GroundTerm) A B var}
    {_MAB : Matches A B var}
    :
    forall (v1 v2 : (gmap var GroundTerm)),
        v1 ⊆ v2 ->
        forall (a : A) (b : B),
            matchesb v1 a b = true ->
            matchesb v2 a b = true
.
Proof.
    intros.
    apply matchesb_satisfies in H0.
    apply satisfies_matchesb.
    eapply satisfies_ext.
    { exact H. }
    { assumption. }
Qed.

Section with_signature.
    Context
        {Σ : StaticModel}
    .

    Fixpoint ApppliedOperator'_matches_PreTerm'
        {Operand1 Operand2 var : Type}
        {_varED : EqDecision var}
        {_varCnt : Countable var}
        {_S1 : Satisfies (gmap var GroundTerm) (symbol) Operand2 var}
        {_S2 : Satisfies (gmap var GroundTerm) (Operand1) Operand2 var}
        {_S3 : Satisfies (gmap var GroundTerm) (Operand1) (PreTerm' symbol Operand2) var}
        {_S4 : Satisfies (gmap var GroundTerm) (PreTerm' symbol Operand1) Operand2 var}
        {_V1 : VarsOf Operand1 var}
        {_V2 : VarsOf Operand2 var}
        {_M1 : Matches (symbol) Operand2 var}
        {_M2 : Matches (Operand1) Operand2 var}
        {_M3 : Matches (Operand1) (PreTerm' symbol Operand2) var}
        {_M4 : Matches (PreTerm' symbol Operand1) Operand2 var}
        (ρ : (gmap var GroundTerm))
        (x : (PreTerm' symbol Operand1))
        (y : PreTerm' symbol Operand2)
        : bool :=
    match x, y with
    | pt_operator a1, pt_operator a2 =>
        bool_decide (a1 = a2)
    | pt_operator _, pt_app_operand _ _ => false
    | pt_operator _, pt_app_ao _ _ => false
    | pt_app_operand _ _ , pt_operator _ => false
    | pt_app_operand app1 o1, pt_app_operand app2 o2 =>
        ApppliedOperator'_matches_PreTerm' 
            ρ (app1)
            app2
        && matchesb ρ (o1) o2
    | pt_app_operand app1 o1, pt_app_ao app2 o2 =>
        ApppliedOperator'_matches_PreTerm' ρ app1 app2
        && matchesb ρ o1 o2
    | pt_app_ao app1 o1, pt_operator _ => false
    | pt_app_ao app1 o1, pt_app_operand app2 o2 =>
        ApppliedOperator'_matches_PreTerm' 
            ρ app1
            app2
        && matchesb ρ o1 o2
    | pt_app_ao app1 o1, pt_app_ao app2 o2 =>
        ApppliedOperator'_matches_PreTerm' 
            ρ app1
            app2
        &&
        ApppliedOperator'_matches_PreTerm' 
            ρ o1
            o2
    end.

    Lemma vars_of_filter
        {var B : Type}
        {_EV : EqDecision var}
        {_CV : Countable var}
        {_VB : VarsOf B var}
        (b' : B)
        (v1 : gmap var GroundTerm)
        :
        vars_of (filter (λ x : var * GroundTerm, x.1 ∈ vars_of b') v1)
        ⊆ vars_of b'
    .
    Proof.
        rewrite elem_of_subseteq.
        intros v Hv.
        unfold vars_of in Hv; simpl in Hv.
        rewrite elem_of_dom in Hv.
        destruct Hv as [w Hw].
        rewrite map_lookup_filter in Hw.
        rewrite bind_Some in Hw.
        destruct Hw as [g [H1g H2g]].
        unfold mguard,option_guard in H2g.
        simpl in *.
        ltac1:(case_match); inversion H2g;
            subst; clear H2g.
        assumption.
    Qed.



     Lemma vars_of_filter_2
        {var B : Type}
        {_EV : EqDecision var}
        {_CV : Countable var}
        {_VB : VarsOf B var}
        (b' : B)
        (v1 : gmap var GroundTerm)
        :
        vars_of (filter (λ x : var * GroundTerm, x.1 ∈ vars_of b') v1)
        ⊆ vars_of v1
    .
    Proof.
        rewrite elem_of_subseteq.
        intros v Hv.
        unfold vars_of in Hv at 1; simpl in Hv.
        rewrite elem_of_dom in Hv.
        destruct Hv as [w Hw].
        rewrite map_lookup_filter in Hw.
        rewrite bind_Some in Hw.
        destruct Hw as [g [H1g H2g]].
        unfold mguard,option_guard in H2g.
        simpl in *.
        ltac1:(case_match); inversion H2g;
            subst; clear H2g.
        unfold vars_of; simpl.
        rewrite elem_of_dom.
        exists w. assumption.
    Qed.


    #[export]
    Program Instance reflect__satisfies__ApppliedOperator'_matches_PreTerm'
        {Operand1 Operand2 var : Type}
        {_varED : EqDecision var}
        {_varCnt : Countable var}
        {_V1v : VarsOf Operand1 var}
        {_V2v : VarsOf Operand2 var}
        {_S1 : Satisfies (gmap var GroundTerm) (symbol) Operand2 var}
        {_S2 : Satisfies (gmap var GroundTerm) (Operand1) Operand2 var}
        {_S3 : Satisfies (gmap var GroundTerm) (Operand1) (PreTerm' symbol Operand2) var}
        {_S4 : Satisfies (gmap var GroundTerm) (PreTerm' symbol Operand1) Operand2 var}
        {_M1 : Matches (symbol) Operand2 var}
        {_M2 : Matches (Operand1) Operand2 var}
        {_M3 : Matches (Operand1) (PreTerm' symbol Operand2) var}
        {_M4 : Matches (PreTerm' symbol Operand1) Operand2 var}
        :
        Matches
            ((PreTerm' symbol Operand1))
            (PreTerm' symbol Operand2)
            var
        := {|
            matchesb :=
                ApppliedOperator'_matches_PreTerm' ;
            matchesb_satisfies := _;
            satisfies_matchesb := _;
        |}.
    Next Obligation.
        simpl.
        ltac1:(rename v into ρ).
        ltac1:(rename a into x).
        ltac1:(rename b into y).
        revert y X.
        induction x; intros y X; destruct y.
        {
            simpl.
            unfold bool_decide.
            ltac1:(case_match).
            {
                subst.
                constructor.
            }
            {
                inversion X; subst.
                ltac1:(congruence).
            }
        }
        {
            inversion X; subst; clear X.
        }
        {
            inversion X; subst; clear X.
        }
        {
            inversion X; subst; clear X.
        }
        {
            inversion X; subst; clear X.
            simpl.
            unfold is_true.
            rewrite andb_true_iff.
            split.
            {
                apply IHx. apply X0.
            }
            {
                apply satisfies_matchesb in X1.
                apply X1.
            }
        }
        {
            inversion X; subst; clear X.
            simpl.
            unfold is_true.
            rewrite andb_true_iff.
            split.
            {
                apply IHx. apply X0.
            }
            {
                apply satisfies_matchesb in X1.
                apply X1.
            }
        }
        {
            inversion X; subst; clear X.
        }
        {
            inversion X; subst; clear X.
            simpl.
            unfold is_true.
            rewrite andb_true_iff.
            split.
            {
                apply IHx1. apply X0.
            }
            {
                apply satisfies_matchesb in X1.
                apply X1.
            }
        }
        {
            inversion X; subst; clear X.
            simpl.
            unfold is_true.
            rewrite andb_true_iff.
            split.
            {
                apply IHx1. apply X0.
            }
            {
                apply IHx2. apply X1.
            }
        }
    Qed.
    Next Obligation.
        simpl.
        ltac1:(rename v into ρ).
        ltac1:(rename a into x).
        ltac1:(rename b into y).
        revert y H.
        induction x; intros y H; destruct y.
        {
            simpl in H.
            apply bool_decide_eq_true in H.
            subst.
            constructor.
        }
        {
            simpl in H. inversion H.
        }
        {
            simpl in H. inversion H.
        }
        {
            simpl in H. inversion H.
        }
        {
            simpl in H.
            unfold is_true in H.
            rewrite andb_true_iff in H.
            destruct H as [H1 H2].
            constructor; try ltac1:(naive_solver).
            apply matchesb_satisfies in H2.
            exact H2.
        }
        {
            simpl in H.
            unfold is_true in H.
            rewrite andb_true_iff in H.
            destruct H as [H1 H2].
            constructor; try ltac1:(naive_solver).
            apply matchesb_satisfies in H2.
            exact H2.
        }
        {
            simpl in H. inversion H.
        }
        {
            simpl in H.
            unfold is_true in H.
            rewrite andb_true_iff in H.
            destruct H as [H1 H2].
            constructor; try ltac1:(naive_solver).
            apply matchesb_satisfies in H2.
            exact H2.
        }
        {
            simpl in H.
            unfold is_true in H.
            rewrite andb_true_iff in H.
            destruct H as [H1 H2].
            constructor; try ltac1:(naive_solver).
        }
    Qed.
    Next Obligation.
        revert b H.
        unfold vars_of; simpl.
        induction a; simpl; intros b' H.
        { 
            destruct b'; simpl in *.
            { ltac1:(set_solver). }
            { inversion H. }
            { inversion H. }
        }
        {
            destruct b'.
            { inversion H. }
            {
                rewrite andb_true_iff in H.
                destruct H as [H1 H2].
                specialize (IHa b' H1).
                apply matchesb_vars_of in H2.
                clear -IHa H2.
                ltac1:(set_solver).
            }
            {
                rewrite andb_true_iff in H.
                destruct H as [H1 H2].
                assert (IH1 := IHa b'1 H1).
                apply matchesb_vars_of in H2.
                clear -IH1 H2.
                ltac1:(set_solver).
            }
        }
        {
            destruct b'.
            { inversion H. }
            {
                rewrite andb_true_iff in H.
                destruct H as [H1 H2].
                specialize (IHa1 b' H1).
                apply matchesb_vars_of in H2.
                clear -IHa1 H2.
                ltac1:(set_solver).
            }
            {
                rewrite andb_true_iff in H.
                destruct H as [H1 H2].
                specialize (IHa1 b'1 H1).
                specialize (IHa2 b'2 H2).
                clear - IHa1 IHa2.
                ltac1:(set_solver).
            }
        }
    Qed.
    Next Obligation.
        revert b v1 v2 H.
        induction a; intros b' v1 v2 H'; destruct b';
            simpl in *;
            try reflexivity.
        {
            
            unfold vars_of in H'; simpl in H'.

            erewrite IHa.
            erewrite matchesb_insensitive.
            reflexivity.
            {
                eapply valuation_restrict_eq_subseteq>[|apply H'].
                clear.
                ltac1:(set_solver).
            }
            {
                eapply valuation_restrict_eq_subseteq>[|apply H'].
                clear.
                unfold vars_of at 1; simpl.
                ltac1:(set_solver).
            }
        }
        {
            
            unfold vars_of in H'; simpl in H'.

            erewrite IHa.
            erewrite matchesb_insensitive.
            reflexivity.
            {
                eapply valuation_restrict_eq_subseteq>[|apply H'].
                clear.
                ltac1:(set_solver).
            }
            {
                eapply valuation_restrict_eq_subseteq>[|apply H'].
                clear.
                unfold vars_of at 1; simpl.
                ltac1:(set_solver).
            }
        }
        {
            
            unfold vars_of in H'; simpl in H'.

            erewrite IHa1.
            erewrite matchesb_insensitive.
            reflexivity.
            {
                eapply valuation_restrict_eq_subseteq>[|apply H'].
                clear.
                ltac1:(set_solver).
            }
            {
                eapply valuation_restrict_eq_subseteq>[|apply H'].
                clear.
                unfold vars_of at 1; simpl.
                ltac1:(set_solver).
            }
        }
        {
            
            unfold vars_of in H'; simpl in H'.

            erewrite IHa1.
            erewrite IHa2.
            reflexivity.
            {
                eapply valuation_restrict_eq_subseteq>[|apply H'].
                clear.
                ltac1:(set_solver).
            }
            {
                eapply valuation_restrict_eq_subseteq>[|apply H'].
                clear.
                unfold vars_of at 1; simpl.
                ltac1:(set_solver).
            }
        }
    Qed.
    Fail Next Obligation.

    Definition ApppliedOperatorOr'_matches_Term'
        {Operand1 Operand2 var : Type}
        {_EDv : EqDecision var}
        {_Cv : Countable var}
        {_V1 : VarsOf Operand1 var}
        {_V2 : VarsOf Operand2 var}
        {_S1 : Satisfies (gmap var GroundTerm) (symbol) Operand2 var}
        {_S2 : Satisfies (gmap var GroundTerm) (Operand1) Operand2 var}
        {_S3 : Satisfies (gmap var GroundTerm) (Operand1) (PreTerm' symbol Operand2) var}
        {_S4 : Satisfies (gmap var GroundTerm) ((PreTerm' symbol Operand1)) Operand2 var}
        {_M1 : Matches (symbol) Operand2 var}
        {_M2 : Matches (Operand1) Operand2 var}
        {_M3 : Matches (Operand1) (PreTerm' symbol Operand2) var}
        {_M4 : Matches ((PreTerm' symbol Operand1)) Operand2 var}
        (ρ : (gmap var GroundTerm))
        (x : (Term' symbol Operand1))
        (y : Term' symbol Operand2)
        : bool :=
    match x, y with
    | term_preterm app1, term_preterm app2 =>
        matchesb ρ app1 app2
    | term_preterm app1, term_operand o2 =>
        matchesb ρ app1 o2
    | term_operand o1, term_preterm app2 =>
        false (*matchesb (ρ, o1) app2*)
    | term_operand o1, term_operand o2 =>
        matchesb ρ o1 o2
    end.

    #[export]
    Program Instance
        reflect__satisfies__ApppliedOperatorOr'_matches_Term'
        {Operand1 Operand2 var : Type}
        {_EDv : EqDecision var}
        {_Cv : Countable var}
        {_V1 : VarsOf Operand1 var}
        {_V2 : VarsOf Operand2 var}
        {_S1 : Satisfies (gmap var GroundTerm) (symbol) Operand2 var}
        {_S2 : Satisfies (gmap var GroundTerm) (Operand1) Operand2 var}
        {_S3 : Satisfies (gmap var GroundTerm) (Operand1) (PreTerm' symbol Operand2) var}
        {_S4 : Satisfies (gmap var GroundTerm) ((PreTerm' symbol Operand1)) Operand2 var}
        {_M1 : Matches (symbol) Operand2 var}
        {_M2 : Matches (Operand1) Operand2 var}
        {_M3 : Matches (Operand1) (PreTerm' symbol Operand2) var}
        {_M4 : Matches ((PreTerm' symbol Operand1)) Operand2 var}
        :
        Matches
            (Term' symbol Operand1)
            (Term' symbol Operand2)
            var
        := {|
            matchesb := 
                ApppliedOperatorOr'_matches_Term';
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        destruct a,b; simpl.
        {
            inversion X; subst; clear X.
            apply satisfies_matchesb.
            assumption.
        }
        {
            inversion X; subst; clear X.
            apply satisfies_matchesb.
            assumption.
        }
        {
            inversion X.
        }
        {
            inversion X; subst; clear X.
            apply satisfies_matchesb.
            assumption.
        }
    Qed.
    Next Obligation.
        destruct a,b; simpl in H.
        {
            constructor. apply matchesb_satisfies. assumption.
        }
        {
            constructor. apply matchesb_satisfies. assumption.
        }
        {
            inversion H.
        }
        {
            constructor. apply matchesb_satisfies. assumption.
        }
    Qed.
    Next Obligation.
        destruct a,b; simpl in *.
        {
            apply matchesb_vars_of in H.
            assumption.
        }
        {
            apply matchesb_vars_of in H.
            assumption.
        }
        { inversion H. }
        {
            apply matchesb_vars_of in H.
            assumption.
        }
    Qed.
    Next Obligation.
        destruct a,b; unfold vars_of in H; simpl in *.
        {
            apply matchesb_insensitive.
            apply H.
        }
        {
            apply matchesb_insensitive.
            apply H.
        }
        { reflexivity. }
        {
            apply matchesb_insensitive.
            apply H.
        }
    Qed.
    Fail Next Obligation.

    Definition builtin_value_matches_BuiltinOrVar
        : Valuation -> builtin_value -> BuiltinOrVar -> bool :=
    fun ρ b bv =>
    match bv with
    | bov_builtin b' => bool_decide (b = b')
    | bov_variable x =>
        match ρ !! x with
        | None => false
        | Some (term_preterm _) => false
        | Some (term_operand b') => bool_decide (b = b')
        end
    end.

    #[export]
    Program Instance
        reflect__matches__builtin_value__BuiltinOrVar
        :
        Matches
            (builtin_value)
            BuiltinOrVar
            variable
        := {|
            matchesb := 
                builtin_value_matches_BuiltinOrVar;
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        destruct b; simpl.
        {
            inversion X; subst; clear X.
            unfold is_true.
            rewrite bool_decide_eq_true.
            reflexivity.
        }
        {
            inversion X; subst; clear X.
            rewrite H1.
            unfold is_true.
            rewrite bool_decide_eq_true.
            reflexivity.
        }
    Qed.
    Next Obligation.
        destruct b; simpl in H.
        {
            unfold is_true in H.
            rewrite bool_decide_eq_true in H.
            subst.
            constructor.
        }
        {
            unfold Valuation in *.
            destruct (v !! x) eqn:Hvx.
            {
                destruct t.
                {
                    inversion H.
                }
                {
                    unfold is_true in H.
                    rewrite bool_decide_eq_true in H.
                    subst a.
                    constructor.
                    exact Hvx.
                }
            }
            {
                inversion H.
            }
        }
    Qed.
    Next Obligation.
        unfold vars_of; destruct b; simpl.
        { ltac1:(clear; set_solver). }
        {
            simpl in H.
            unfold Valuation in *.
            destruct (v !! x) as [a0|] eqn:Hvx.
            {
                rewrite elem_of_subseteq.
                intros x0 Hx0.
                rewrite elem_of_singleton in Hx0.
                subst.
                rewrite elem_of_dom.
                exists a0. assumption.
            }
            {
                inversion H.
            }
        }
    Qed.
    Next Obligation.
        destruct b; unfold vars_of in H; simpl in *.
        {
            reflexivity.
        }
        {
            unfold valuation_restrict in H.
            rewrite map_eq_iff in H.
            specialize (H x).
            rewrite map_lookup_filter in H.
            rewrite map_lookup_filter in H.
            ltac1:(repeat case_match); try reflexivity;
                subst.
            {
                symmetry. apply bool_decide_eq_false.
                intros HContra. subst.

                unfold Valuation in *.
                ltac1:(rewrite H0 in H).
                ltac1:(rewrite H2 in H).
                simpl in H.
                unfold mguard,option_guard in H.
                ltac1:(case_match);
                    inversion H; subst; clear H.
                clear -n.
                rewrite elem_of_singleton in n.
                ltac1:(contradiction n).
                reflexivity.
            }
            {
                apply bool_decide_eq_false.
                intros HContra. subst.

                unfold Valuation in *.
                ltac1:(rewrite H0 in H).
                ltac1:(rewrite H2 in H).
                simpl in H.
                unfold mguard,option_guard in H.
                ltac1:(case_match);
                    inversion H; subst; clear H.
                clear -n.
                rewrite elem_of_singleton in n.
                ltac1:(contradiction n).
                reflexivity.
            }
            {
                unfold bool_decide.
                unfold Valuation in *.
                ltac1:(rewrite H0 in H).
                ltac1:(rewrite H2 in H).
                simpl in H.
                unfold mguard,option_guard in H.
                ltac1:(case_match);
                    inversion H; subst; clear H.
                { reflexivity. }
                clear -n.
                ltac1:(contradiction n).
                rewrite elem_of_singleton.
                reflexivity.
            }
            {
                apply bool_decide_eq_false.
                intros HContra.
                subst.

                unfold Valuation in *.
                ltac1:(rewrite H0 in H).
                ltac1:(rewrite H2 in H).
                simpl in H.
                unfold mguard,option_guard in H.
                ltac1:(case_match);
                    inversion H; subst; clear H.
                clear -n.
                apply n.
                rewrite elem_of_singleton.
                reflexivity.
            }
            {
                symmetry.
                apply bool_decide_eq_false.
                intros HContra.
                subst.

                unfold Valuation in *.
                ltac1:(rewrite H0 in H).
                ltac1:(rewrite H1 in H).
                simpl in H.
                unfold mguard,option_guard in H.
                ltac1:(case_match);
                    inversion H; subst; clear H.
                clear -n.
                apply n.
                rewrite elem_of_singleton.
                reflexivity.
            }
        }
    Qed.
    Fail Next Obligation.

    (* Can this be simplified? *)
    Definition builtin_value_matches_SymbolicTerm
        : Valuation -> builtin_value -> SymbolicTerm -> bool :=
    fun ρ b t =>
    match t with
    | term_preterm _ => false
    | term_operand (bov_variable x) =>
        match ρ !! x with
        | None => false
        | Some (term_preterm _) => false
        | Some (term_operand b') => bool_decide (b = b')
        end
    | term_operand (bov_builtin b') =>
        bool_decide (b = b')
    end.

    #[export]
    Program Instance
        reflect__matches__builtin_value__SymbolicTerm
        :
        Matches
            (builtin_value)
            SymbolicTerm
            variable
        := {|
            matchesb := builtin_value_matches_SymbolicTerm;
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        destruct b; simpl in *.
        {
            inversion X.
        }
        {
            destruct operand.
            {
                inversion X; subst; clear X.
                unfold is_true.
                rewrite bool_decide_eq_true.
                reflexivity.
            }
            {
                inversion X; subst; clear X.
                rewrite H1.
                unfold is_true.
                rewrite bool_decide_eq_true.
                reflexivity.
            }
        }
    Qed.
    Next Obligation.
        destruct b; simpl in *.
        { inversion H. }
        {
            destruct operand.
            {
                unfold is_true in H.
                rewrite bool_decide_eq_true in H.
                subst.
                constructor.
            }
            {
                unfold Valuation in *.
                destruct (v !! x) eqn:Hvx.
                {
                    destruct t.
                    {
                        inversion H.
                    }
                    {
                        unfold is_true in H.
                        rewrite bool_decide_eq_true in H.
                        subst.
                        constructor.
                        exact Hvx.
                    }
                }
                {
                    inversion H.
                }
            }
        }
    Qed.
    Next Obligation.
        destruct b; unfold vars_of at 1; simpl in *.
        {
            inversion H.
        }
        {
            ltac1:(repeat case_match); subst; unfold vars_of; simpl.
            { ltac1:(set_solver). }
            { inversion H. }
            {
                rewrite elem_of_subseteq.
                intros x0 Hx0.
                rewrite elem_of_singleton in Hx0.
                subst.
                unfold Valuation in *.
                rewrite elem_of_dom.
                eexists. ltac1:(eassumption).
            }
            { inversion H. }
        }
    Qed.
    Next Obligation.
        destruct b; simpl in *.
        { reflexivity. }

        unfold vars_of in *; simpl in *.
        unfold vars_of in *; simpl in *.
        ltac1:(repeat case_match);
            try reflexivity.
        {
            symmetry.
            apply bool_decide_eq_false.
            intros HContra.
            subst.
            simpl in *.
            apply valuation_restrict_eq_impl_lookup with (x := x) in H.
            {
                ltac1:(rewrite H in H1).
                ltac1:(rewrite H3 in H1).
                ltac1:(congruence).
            }
            {
                ltac1:(set_solver).
            }
        }
        {
            subst.
            apply bool_decide_eq_false.
            intros HContra.
            subst.
            simpl in *.
            apply valuation_restrict_eq_impl_lookup with (x := x) in H.
            {
                ltac1:(rewrite H in H1).
                ltac1:(rewrite H3 in H1).
                ltac1:(congruence).
            }
            {
                ltac1:(set_solver).
            }
        }
        {
            subst.
            simpl in *.
            apply valuation_restrict_eq_impl_lookup with (x := x) in H.
            {
                ltac1:(rewrite H in H1).
                ltac1:(rewrite H3 in H1).
                inversion H1; subst; clear H1.
                ltac1:(congruence).
            }
            {
                ltac1:(set_solver).
            }
        }
        {
            subst.
            apply bool_decide_eq_false.
            intros HContra.
            subst.
            simpl in *.
            apply valuation_restrict_eq_impl_lookup with (x := x) in H.
            {
                ltac1:(rewrite H in H1).
                ltac1:(rewrite H3 in H1).
                ltac1:(congruence).
            }
            {
                ltac1:(set_solver).
            }
        }
        {
            subst.
            symmetry.
            apply bool_decide_eq_false.
            intros HContra.
            subst.
            simpl in *.
            apply valuation_restrict_eq_impl_lookup with (x := x) in H.
            {
                ltac1:(rewrite H in H1).
                ltac1:(rewrite H1 in H2).
                ltac1:(congruence).
            }
            {
                ltac1:(set_solver).
            }
        }
    Qed.
    Fail Next Obligation.

    Definition Term'_matches_BuiltinOrVar
        : Valuation -> (PreTerm' symbol builtin_value) ->
            BuiltinOrVar ->
            bool
    := fun ρ t bov =>
    match bov with
    | bov_builtin b => false
    | bov_variable x =>
        bool_decide (ρ !! x = Some (term_preterm t))
    end.

    #[export]
    Program Instance
        matches__builtin_value__SymbolicTerm
        :
        Matches
            (PreTerm' symbol builtin_value)
            BuiltinOrVar
            variable
        := {|
            matchesb := Term'_matches_BuiltinOrVar;
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        destruct b; simpl in *.
        {
            inversion X.
        }
        {
            inversion X; subst; clear X.
            unfold is_true.
            rewrite bool_decide_eq_true.
            reflexivity.
        }
    Qed.
    Next Obligation.
        destruct b; simpl in *.
        { inversion H. }
        {
            unfold satisfies; simpl.
            unfold is_true in H.
            rewrite bool_decide_eq_true in H.
            apply H.
        }
    Qed.
    Next Obligation.
        destruct b; simpl in *.
        { inversion H. }
        {
            rewrite bool_decide_eq_true in H.
            unfold vars_of; simpl.
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            rewrite elem_of_singleton in Hx0.
            subst.
            unfold Valuation in *.
            rewrite elem_of_dom.
            eexists. ltac1:(eassumption).
        }
    Qed.
    Next Obligation.
        destruct b; simpl in *.
        { reflexivity. }
        unfold bool_decide.
        ltac1:(repeat case_match); try reflexivity.
        {
            clear H0 H1.
            ltac1:(exfalso).
            apply n.
            eapply valuation_restrict_eq_impl_lookup in H.
            {
                rewrite H in e.
                ltac1:(rewrite e in n).
                ltac1:(contradiction).
            }
            {
                unfold vars_of; simpl.
                rewrite elem_of_singleton.
                reflexivity.
            }
        }
        {
            eapply valuation_restrict_eq_impl_lookup in H.
            {
                clear H0 H1.
                rewrite H in n.
                ltac1:(rewrite e in n).
                ltac1:(contradiction).
            }
            {
                unfold vars_of; simpl.
                rewrite elem_of_singleton.
                reflexivity.
            }
        }
    Qed.
    Fail Next Obligation.

    #[export]
    Program Instance Matches_bv_ao'
        {B var : Type}
        {_EDv : EqDecision var}
        {_Cv : Countable var}
        {_VB : VarsOf B var}
        :
        Matches
            builtin_value
            (PreTerm' symbol B)
            var
    := {|
        matchesb := fun _ _ _ => false ;
    |}.
    Fail Next Obligation.

    #[export]
    Instance VarsOf_LeftRight
        {_VO : VarsOf Valuation (LeftRight * variable)}
        :
        VarsOf (Valuation * LeftRight) variable
    := {|
        vars_of := fun ρd =>
            let ρ := ρd.1 in
            let d := ρd.2 in
            let vs : gset (LeftRight * variable) := vars_of ρ in
            let vs' := filter (fun x => x.1 = d) vs in
            set_map (fun x : LeftRight * variable => x.2) vs'
    |}.

    (*
    #[export]
    Program Instance Matches_vlrblrootob
        :
        Matches
            (Valuation * LeftRight)
            (builtin_value)
            (PreTerm' symbol LocalRewriteOrSymbolicTermOrBOV)
            (variable)
    := {|
        matchesb := fun _ _ _ => false ;
    |}.
    Next Obligation.
        unfold satisfies; simpl.
        apply ReflectF. ltac1:(tauto).
    Qed.
    Fail Next Obligation.
    *)


    #[export]
    Program Instance
        Matches_symbol_B
        {B var : Type}
        {_VarED : EqDecision var}
        {_VarCnt : Countable var}
        {_VB : VarsOf B var}
        :
        Matches symbol B var
    := {|
        matchesb := fun _ _ _ => false
    |}.
    Fail Next Obligation.
    
    #[export]
    Instance
        matches__GroundTerm__SymbolicTerm
        :
        Matches
            GroundTerm
            SymbolicTerm
            variable
    .
    Proof.
        unfold GroundTerm.
        unfold SymbolicTerm.
        ltac1:(unshelve(eapply reflect__satisfies__ApppliedOperatorOr'_matches_Term')).
    Defined.

End with_signature.

Definition val_satisfies_ap_bool
    {Σ : StaticModel}
    
    (ρ : Valuation)
    (ap : AtomicProposition)
    : bool :=
match ap with
| apeq e1 e2 => 
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    bool_decide (v1 = v2) && isSome v1
end
.

Lemma expression_evaluate_some_valuation
    {Σ : StaticModel} ρ e x
    :
    Expression_evaluate ρ e = Some x ->
    vars_of e ⊆ vars_of ρ.
Proof.
    revert x.
    induction e; unfold vars_of; simpl; intros x' H.
    {
        ltac1:(set_solver).
    }
    {
        rewrite elem_of_subseteq.
        intros x1 Hx1.
        rewrite elem_of_singleton in Hx1.
        subst.
        unfold Valuation in *.
        rewrite elem_of_dom.
        exists x'. assumption.
    }
    {
        ltac1:(set_solver).
    }
    {
        rewrite bind_Some in H.
        destruct H as [x0 [H1x0 H2x0]].
        inversion H2x0; subst; clear H2x0.
        rewrite H1x0 in IHe. simpl in IHe.
        specialize (IHe x0 eq_refl).
        apply IHe.
    }
    {
        rewrite bind_Some in H.
        destruct H as [x0 [H1x0 H2x0]].
        inversion H2x0; subst; clear H2x0.

        rewrite bind_Some in H0.
        destruct H0 as [x1 [H1x1 H2x1]].
        inversion H2x1; subst; clear H2x1.
        specialize (IHe1 _ H1x0).
        specialize (IHe2 _ H1x1).
        rewrite union_subseteq.
        split; assumption.
    }
    {
        rewrite bind_Some in H.
        destruct H as [x0 [H1x0 H2x0]].
        inversion H2x0; subst; clear H2x0.

        rewrite bind_Some in H0.
        destruct H0 as [x1 [H1x1 H2x1]].
        inversion H2x1; subst; clear H2x1.


        rewrite bind_Some in H0.
        destruct H0 as [x2 [H1x2 H2x2]].
        inversion H2x2; subst; clear H2x2.

        specialize (IHe1 _ H1x0).
        specialize (IHe2 _ H1x1).
        specialize (IHe3 _ H1x2).
        repeat (rewrite union_subseteq).
        (repeat split); assumption.
    }
Qed.

Lemma Expression_evaluate_val_restrict:
    ∀ {Σ : StaticModel}
        (ρ1 ρ2 : gmap variable GroundTerm)
        (t : Expression),
            valuation_restrict ρ1 (vars_of t) = valuation_restrict ρ2 (vars_of t) →
            Expression_evaluate ρ1 t = Expression_evaluate ρ2 t
.
Proof.
    intros Σ ρ1 ρ2 t.
    revert ρ1 ρ2.
    induction t; intros ρ1 ρ2; unfold vars_of in *; simpl in *.
    { solve[auto]. }
    {
        intros H1.
        unfold is_true, isSome in *.
        unfold valuation_restrict in H1.
        rewrite map_eq_iff in H1.
        specialize (H1 x).
        do 2 (rewrite map_lookup_filter in H1).
        destruct (ρ1!!x),(ρ2!!x); simpl in *; try reflexivity.
        {
            unfold mguard,option_guard in H1.
            ltac1:(repeat case_match).
            {
                assumption.
            }
            {
                ltac1:(contradiction n).
                rewrite elem_of_singleton.
                reflexivity.
            }
        }
        {
            unfold mguard,option_guard in H1.
            ltac1:(repeat case_match).
            {
                assumption.
            }
            {
                ltac1:(contradiction n).
                rewrite elem_of_singleton.
                reflexivity. 
            }
        }
        {
            unfold mguard,option_guard in H1.
            ltac1:(repeat case_match).
            {
                assumption.
            }
            {
                ltac1:(contradiction n).
                rewrite elem_of_singleton.
                reflexivity. 
            }
        }
    }
    {
        intros ?. reflexivity.
    }
    {
        intros H1.
        specialize (IHt _ _ H1).
        rewrite IHt.
        reflexivity.
    }
    {
        intros H1.
        assert (H2 : valuation_restrict ρ1 (vars_of_Expression t1) = valuation_restrict ρ2 (vars_of_Expression t1)).
        {
            eapply valuation_restrict_eq_subseteq>[|apply H1].
            ltac1:(set_solver).
        }
        assert (H3 : valuation_restrict ρ1 (vars_of_Expression t2) = valuation_restrict ρ2 (vars_of_Expression t2)).
        {
            eapply valuation_restrict_eq_subseteq>[|apply H1].
            ltac1:(set_solver).
        }
        specialize (IHt1 _ _ H2).
        specialize (IHt2 _ _ H3).
        rewrite IHt1.
        rewrite IHt2.
        reflexivity.
    }
    {
        intros H1.
        assert (H2 : valuation_restrict ρ1 (vars_of_Expression t1) = valuation_restrict ρ2 (vars_of_Expression t1)).
        {
            eapply valuation_restrict_eq_subseteq>[|apply H1].
            ltac1:(set_solver).
        }
        assert (H3 : valuation_restrict ρ1 (vars_of_Expression t2) = valuation_restrict ρ2 (vars_of_Expression t2)).
        {
            eapply valuation_restrict_eq_subseteq>[|apply H1].
            ltac1:(set_solver).
        }
        assert (H4 : valuation_restrict ρ1 (vars_of_Expression t3) = valuation_restrict ρ2 (vars_of_Expression t3)).
        {
            eapply valuation_restrict_eq_subseteq>[|apply H1].
            ltac1:(set_solver).
        }
        specialize (IHt1 _ _ H2).
        specialize (IHt2 _ _ H3).
        specialize (IHt3 _ _ H4).
        rewrite IHt1.
        rewrite IHt2.
        rewrite IHt3.
        reflexivity.
    }
Qed.

#[export]
Program Instance Matches_val_ap
    {Σ : StaticModel}
    
    : Matches unit AtomicProposition variable
:= {|
    matchesb := fun a b c => val_satisfies_ap_bool a c;
|}.
Next Obligation.
    destruct b.
    unfold satisfies in X; simpl in X.
    destruct X as [H1 H2].
    unfold val_satisfies_ap_bool.
    unfold is_true.
    rewrite andb_true_iff.
    rewrite bool_decide_eq_true.
    split>[exact H1|].
    unfold isSome in H2.
    destruct (Expression_evaluate v e1) eqn:H2'>[|inversion H2].
    unfold isSome.
    reflexivity.
Qed.
Next Obligation.
    destruct b; simpl in *.
    unfold is_true in H.
    rewrite andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite bool_decide_eq_true in H1.
    constructor.
    { exact H1. }
    {
        unfold isSome in H2.
        unfold is_Some.
        destruct (Expression_evaluate v e1).
        { reflexivity. }
        { inversion H2. }
    }
Qed.
Next Obligation.
    destruct b; unfold vars_of in *; simpl in *.
    {
        rewrite andb_true_iff in H.
        rewrite bool_decide_eq_true in H.
        destruct H as [H1 H2].
        unfold isSome in *.
        destruct (Expression_evaluate v e1) eqn:Heq2>[|inversion H2].
        clear H2. symmetry in H1.
        unfold vars_of. simpl.
        apply expression_evaluate_some_valuation in Heq2.
        apply expression_evaluate_some_valuation in H1.
        rewrite union_subseteq.
        split; assumption.
    }
Qed.
Next Obligation.
    revert v1 v2 H.
    induction b; intros v1 v2 HH; simpl in *.
    {
        unfold vars_of in HH; simpl in *.
        rewrite Expression_evaluate_val_restrict with (ρ1 := v1) (ρ2 := v2).
        rewrite Expression_evaluate_val_restrict with (ρ1 := v1) (ρ2 := v2).
        reflexivity.
        {
            eapply valuation_restrict_eq_subseteq>[|apply HH].
            ltac1:(set_solver).
        }
        {
            eapply valuation_restrict_eq_subseteq>[|apply HH].
            ltac1:(set_solver).
        }
    }
Qed.
Fail Next Obligation.


Definition valuation_satisfies_sc_bool
    {Σ : StaticModel}
    
    (ρ : Valuation)
    (sc : SideCondition) : bool :=
match sc with
| sc_constraint c => matchesb ρ () c
end.

#[export]
Program Instance Matches_valuation_sc
    {Σ : StaticModel}
    
    :
    Matches unit SideCondition variable
:= {|
    matchesb := fun a b c => valuation_satisfies_sc_bool a c;
|}.
Next Obligation.
    destruct b; simpl in *.
    unfold satisfies in X; simpl in X.
    apply satisfies_matchesb.
    assumption.
Qed.
Next Obligation.
    destruct b; simpl in *.
    apply matchesb_satisfies in H.
    apply H.
Qed.
Next Obligation.
    destruct b; unfold vars_of; simpl in *.
    {
        apply matchesb_vars_of in H.
        exact H.
    }
Qed.
Next Obligation.
    destruct b; unfold vars_of in H; simpl in *.
    {
        apply matchesb_insensitive.
        exact H.
    }
Qed.
Fail Next Obligation.

#[export]
Program Instance Matches_valuation_scs
    {Σ : StaticModel}
    :
    Matches unit (list SideCondition) variable
:= {|
    matchesb := fun ρ b c => forallb (matchesb ρ ()) c;
|}.
Next Obligation.
    unfold satisfies in X; simpl in X.
    unfold is_true.
    rewrite forallb_forall.
    intros x Hx.
    rewrite <- elem_of_list_In in Hx.
    specialize (X x Hx).
    apply satisfies_matchesb.
    assumption.
Qed.
Next Obligation.
    unfold is_true in H.
    rewrite forallb_forall in H.
    unfold satisfies; simpl.
    intros x Hx.
    rewrite elem_of_list_In in Hx.
    specialize (H x Hx).
    apply matchesb_satisfies.
    assumption.
Qed.
Next Obligation.
    unfold vars_of; simpl.
    rewrite forallb_forall in H.
    rewrite elem_of_subseteq.
    intros x Hx. 
    rewrite elem_of_union_list in Hx.
    destruct Hx as [X [H1X H2X]].
    unfold Valuation in *.
    rewrite elem_of_list_fmap in H1X.
    destruct H1X as [y [H1y H2y]].
    subst.
    
    specialize (H y).
    rewrite <- elem_of_list_In in H.
    specialize (H ltac:(assumption)).
    apply matchesb_vars_of in H.
    
    rewrite elem_of_subseteq in H.
    specialize (H x H2X).
    exact H.
Qed.
Next Obligation.
    revert H.
    induction b; simpl; intros HH.
    { reflexivity. }
    {
        unfold vars_of in HH; simpl in HH.
        ltac1:(ospecialize (IHb _)).
        {
            eapply valuation_restrict_eq_subseteq>[|apply HH].
            unfold vars_of at 1; simpl.
            unfold fmap; simpl.
            ltac1:(set_solver).
        }
        rewrite IHb.
        erewrite matchesb_insensitive.
        reflexivity.
        eapply valuation_restrict_eq_subseteq>[|apply HH].
        ltac1:(set_solver).
    }
Qed.
Fail Next Obligation.



#[export]
Program Instance Matches__builtin__Expr
    {Σ : StaticModel}
    
    :
    Matches builtin_value (Expression) variable
:= {|
    matchesb := (fun ρ b e =>
        bool_decide (Expression_evaluate ρ e = Some (term_operand b))
    ) ;
|}.
Next Obligation.
    unfold satisfies. simpl.
    unfold is_true.
    rewrite bool_decide_eq_true.
    unfold satisfies in X; simpl in X.
    exact X.
Qed.
Next Obligation.
    unfold is_true in H.
    rewrite bool_decide_eq_true in H.
    apply H.
Qed.
Next Obligation.
    apply bool_decide_eq_true in H.
    apply expression_evaluate_some_valuation in H.
    assumption.
Qed.
Next Obligation.
    erewrite Expression_evaluate_val_restrict.
    reflexivity.
    exact H.
Qed.
Fail Next Obligation.

#[export]
Program Instance Matches_asb_expr
    {Σ : StaticModel}:
    Matches
        ((PreTerm' symbol builtin_value))
        Expression
        variable
:= {|
    matchesb := (fun ρ x e =>
        bool_decide (Expression_evaluate ρ e = Some (term_preterm x))   ) ;
|}.
Next Obligation.
    unfold is_true.
    rewrite bool_decide_eq_true.
    apply X.
Qed.
Next Obligation.
    unfold is_true in H.
    rewrite bool_decide_eq_true in H.
    apply H.
Qed.
Next Obligation.
    apply bool_decide_eq_true in H.
    apply expression_evaluate_some_valuation in H.
    assumption.
Qed.
Next Obligation.
    erewrite Expression_evaluate_val_restrict.
    reflexivity.
    exact H.
Qed.
Fail Next Obligation.

