From Minuska Require Import
    prelude
.

Class Signature := {
    Constructor : Type ;
    Constructor_eqdec :: EqDecision Constructor ;
    arity : Constructor -> nat;
}.

Unset Elimination Schemes.
Inductive Pattern {Σ : Signature} : Type :=
| p_wildcard
| p_cpat (c : Constructor) (l : list Pattern)
.
Inductive Value {Σ : Signature} : Type :=
| v_cval (c : Constructor) (l : list Value)
.
Set Elimination Schemes.

Section custom_induction_principle.

    Context
        {Σ : Signature}
        (P : Pattern -> Prop)
        (true_for_wildcard : P p_wildcard)
        (preserved_by_cpat :
            forall
                (c : Constructor)
                (l : list Pattern),
                Forall P l ->
                P (p_cpat c l)
        )
    .

    Fixpoint Pattern_ind (p : Pattern) : P p :=
    match p with
    | p_wildcard => true_for_wildcard
    | p_cpat c l => preserved_by_cpat c l (Forall_true P l Pattern_ind)
    end.

End custom_induction_principle.

Section custom_induction_principle.

    Context
        {Σ : Signature}
        (P : Value -> Prop)
        (preserved_by_cval :
            forall
                (c : Constructor)
                (l : list Value),
                Forall P l ->
                P (v_cval c l)
        )
    .

    Fixpoint Value_ind (v : Value) : P v :=
    match v with
    | v_cval c l => preserved_by_cval c l (Forall_true P l Value_ind)
    end.

End custom_induction_principle.

Definition PatternVector {Σ : Signature} : Type :=
    list Pattern
.

Definition PatternMatrice {Σ : Signature} : Type :=
    list PatternVector
.

Definition ClauseMatrix {Σ : Signature} (A : Type) : Type :=
    list (PatternVector*A)
.

Definition ValueVector {Σ : Signature} : Type :=
    list Value
.

Inductive pvmatch {Σ : Signature} : Pattern -> Value -> Prop :=
| pvm_wildcard: forall v, pvmatch p_wildcard v
| pvm_ctor: forall c ps vs,
    (
        forall i p v, ps !! i = Some p -> vs !! i = Some v ->
        pvmatch p v
    ) ->
    pvmatch (p_cpat c ps) (v_cval c vs)
.

Definition pvvecmatch {Σ : Signature}
: PatternVector -> ValueVector -> Prop :=
    fun ps vs => (
        forall i p v, ps !! i = Some p -> vs !! i = Some v ->
        pvmatch p v
    )
.

Inductive notinstance {Σ : Signature} : Pattern -> Value -> Prop :=
| ni_ctor_diferent: forall c c' ps vs, c <> c' -> notinstance (p_cpat c ps) (v_cval c' vs)
| ni_list_different : forall c c' ps vs,
    (exists i p v, ps !! i = Some p -> vs !! i = Some v -> notinstance p v) ->
    notinstance (p_cpat c ps) (v_cval c' vs)
.

Definition cmmatch {Σ : Signature} {A : Type}
    : ValueVector -> ClauseMatrix A -> A -> Prop
:=
    fun vs cm a =>
    ∃ (j : nat) (pv : PatternVector),
        cm !! j = Some (pv,a)
        /\ pvvecmatch pv vs
        /\ (length pv) = (length vs)
.

Definition Simplify_step {Σ : Signature} {A : Type}
    (c : Constructor) (row : (PatternVector * A))
: list ((PatternVector * A))
:=
match head row.1 with
| None => []
| Some v1 =>
    match v1 with
    | p_wildcard => [((replicate (arity c) (p_wildcard)) ++ (tail row.1), row.2)]
    | p_cpat c' qs =>
        if (decide (c' = c)) then [((qs ++ tail row.1), row.2)] else []
    end
end.

Definition Simplify {Σ : Signature} {A : Type} : Constructor -> ClauseMatrix A -> ClauseMatrix A :=
fun c cm =>
    concat (map (Simplify_step c) cm)
.

Definition row_matches_ctor
    {Σ : Signature}
    {A : Type}
    (c : Constructor)
    : (PatternVector*A) -> Prop
:= fun row => match row.1 with
| nil => False
| (p_cpat c' _)::_ => c = c'
| p_wildcard::_ => True
end.

#[local]
Instance row_matches_ctor_dec
    {Σ : Signature}
    {A : Type}
    (c : Constructor)
    (row : PatternVector*A)
    : Decision (row_matches_ctor c row)
.
Proof.
    unfold row_matches_ctor.
    destruct (row.1) eqn:Heq.
    { apply _. }
    {
        destruct p.
        { apply _. }
        {
            destruct p0.
            {
                apply _.
            }
            {
                apply _.
            }
        }
    }
Defined.

Lemma simplify_correct_helper_1
    {Σ : Signature} (A : Type) cm pv (a : A) (c : Constructor):
    ∀ j : nat,
    cm !! j = Some (p_wildcard :: pv, a)
    → concat (map (Simplify_step c) cm)
    !! length (filter (row_matches_ctor c) (take j cm)) =
    Some (replicate (arity c) p_wildcard ++ pv, a)
.
Proof.
    induction cm; intros j H1pv.
    {
        simpl. ltac1:(rewrite lookup_nil in H1pv). inversion H1pv.
    }
    {
        simpl.
        destruct j.
        {
            simpl in H1pv. inversion H1pv; subst; clear H1pv.
            simpl. reflexivity.
        }
        {
            simpl in H1pv. simpl.
            destruct a0 as [pv' a0].
            rewrite filter_cons. unfold decide; simpl.
            destruct pv' as [|p' pv'].
            {
                simpl.
                specialize (IHcm j H1pv).
                rewrite IHcm.
                reflexivity.
            }
            {
                destruct p'; simpl.
                {
                    specialize (IHcm j H1pv).
                    apply IHcm.
                }
                {
                    destruct pv'; simpl.
                    {
                        unfold row_matches_ctor_dec. simpl.
                        destruct (decide_rel eq c c0).
                        {
                            subst c0.
                            specialize (IHcm j H1pv).
                            simpl.
                            unfold Simplify_step. simpl.
                            destruct (decide (c = c)).
                            {
                                simpl.
                                clear e.
                                unfold Simplify_step in *.
                                apply IHcm.
                            }
                            {
                                ltac1:(contradiction n). reflexivity.
                            }
                        }
                        {
                            unfold Simplify_step. simpl.
                            destruct (decide (c0 = c)).
                            {
                                ltac1:(subst; contradiction).
                            }
                            {
                                simpl.
                                specialize (IHcm j H1pv).
                                apply IHcm.
                            }
                        }
                    }
                    {
                        unfold Simplify_step. simpl.
                        destruct (decide (c0 = c)).
                        {
                            subst. simpl.
                            specialize (IHcm j H1pv).
                            unfold row_matches_ctor_dec. simpl.
                            destruct (decide_rel eq c c).
                            {
                                simpl. clear e. apply IHcm.
                            }
                            {
                                ltac1:(contradiction).
                            }
                        }
                        {
                            simpl.
                            specialize (IHcm j H1pv).
                            unfold row_matches_ctor_dec. simpl.
                            destruct (decide_rel eq c c0).
                            {
                                subst.
                                ltac1:(contradiction).
                            }
                            {
                                apply IHcm.
                            }
                        }
                    }
                }
            }
        }
    }
Qed.

Lemma simplify_correct {Σ : Signature} (A : Type):
    forall
        (cm : ClauseMatrix A)
        (c : Constructor)
        (vs ws : list Value)
        (a : A),
    arity c = length ws ->
    (
    cmmatch ([(v_cval c ws)] ++ vs) cm a
    <->
    cmmatch (ws ++ vs) (Simplify c cm) a
    )
.
Proof.
    intros cm c vs ws a.
    intros Harity.
    intros. simpl. split.
    {
        intros H. unfold cmmatch in H.
        destruct H as [j pf].
        destruct pf as [pv [H1pv [H2pv H3pv]]].
        unfold cmmatch.
        unfold pvvecmatch in H2pv.
        simpl in H3pv.
        destruct pv; simpl in H3pv; inversion H3pv; clear H3pv.
        assert(H2'pv := H2pv).
        specialize (H2pv 0 p (v_cval c ws)).
        simpl in H2pv.
        specialize (H2pv eq_refl eq_refl).
        unfold Simplify.
        remember (length (filter (row_matches_ctor c) (firstn j cm))) as myj.
        exists myj.
        inversion H2pv.
        {    
            subst p v.
            exists ((replicate (arity c) (p_wildcard)) ++ (pv)).
            split.
            {
                subst myj.
                revert j H1pv.
                apply simplify_correct_helper_1.
            }
            {
                split.
                {
                    subst.
                    unfold pvvecmatch.
                    intros i p v Hrep Hlookup.
                    destruct (decide (i < length ws)) as [Hlt|Hgeq].
                    {
                        ltac1:(rewrite lookup_app_l in Hlookup).
                        { assumption. }
                        rewrite Harity in Hrep.
                        ltac1:(rewrite lookup_app_l in Hrep).
                        {
                            rewrite replicate_length.
                            assumption.
                        }
                        rewrite lookup_replicate in Hrep.
                        destruct Hrep as [Hrep1 Hrep2]. subst.
                        constructor.
                    }
                    {
                        ltac1:(rewrite lookup_app_r in Hlookup).
                        { ltac1:(lia). }
                        rewrite Harity in Hrep.
                        ltac1:(rewrite lookup_app_r in Hrep).
                        {
                            rewrite replicate_length.
                            ltac1:(lia).
                        }
                        rewrite replicate_length in Hrep.
                        eapply H2'pv with (i := S((i - length ws))); assumption.
                    }
                }
                {
                    rewrite (app_length).
                    rewrite (app_length).
                    ltac1:(rewrite replicate_length).
                    ltac1:(congruence).
                }
            }
        }
        {
            subst.
            exists (((ps ++ pv))).
            split.
            {
                revert j H1pv.
                induction cm; intros j H1pv.
                {
                    simpl in *.
                    ltac1:(rewrite lookup_nil in H1pv).
                    inversion H1pv.
                }
                {
                    simpl in *.
                    destruct j.
                    {
                        simpl in *.
                        inversion H1pv; subst; clear H1pv.
                        unfold Simplify_step; simpl.
                        destruct (decide (c = c))>[|ltac1:(contradiction)].
                        simpl.
                        clear e.
                        reflexivity.
                    }
                    {
                        simpl in *.
                        unfold Simplify_step; simpl.
                        rewrite filter_cons.
                        ltac1:(repeat case_match).
                        {
                            subst. simpl.
                            specialize (IHcm _ H1pv).
                            apply IHcm.
                        }
                        {
                            subst. simpl.
                            specialize (IHcm _ H1pv).
                            apply IHcm.
                        }
                        {
                            subst. simpl in *.
                            unfold row_matches_ctor in *.
                            destruct a0; simpl in *.
                            {
                                destruct p; simpl in *.
                                {
                                    inversion H1.
                                }
                                {
                                    destruct p; simpl in *.
                                    {
                                        inversion H1.
                                    }
                                    {
                                        subst. inversion H1; subst; clear H1.
                                        ltac1:(exfalso; clear -H4).
                                        unfold decide,decide_rel in H4.
                                        destruct (Constructor_eqdec c0 c0).
                                        {
                                            inversion H4.
                                        }
                                        {
                                            apply n. reflexivity.
                                        }
                                    }
                                }
                            }
                        }
                        {
                            simpl.
                            ltac1:(exfalso).
                            destruct a0; simpl in *.
                            {
                                destruct p; simpl in *.
                                {
                                    unfold row_matches_ctor in *.
                                    simpl in *.
                                    ltac1:(contradiction).
                                }
                                {
                                    inversion H1.
                                }
                            }
                        }
                        {
                            subst. simpl in *.
                            specialize (IHcm _ H1pv).
                            destruct a0; simpl in *.
                            {
                                destruct p; simpl in *.
                                {
                                    inversion H1.
                                }
                                {
                                    inversion H1; subst. clear H1.
                                    simpl in *.
                                    unfold row_matches_ctor in *.
                                    simpl in *.
                                    ltac1:(contradiction).
                                }
                            }
                        }
                        {
                            subst. simpl in *.
                            destruct a0; simpl in *.
                            destruct p.
                            { inversion H1. }
                            inversion H1; subst; clear H1.
                            unfold row_matches_ctor in *.
                            simpl in *.
                            unfold is_left in H4.
                            ltac1:(repeat case_match).
                            {
                                subst. ltac1:(contradiction).
                            }
                            {
                                inversion H4.
                            }
                        }
                        {
                            simpl. apply IHcm. apply H1pv.
                        }
                        {
                            simpl. apply IHcm. apply H1pv.
                        }
                    }
                }
                
            }
        }
        unfold Simplify_step.


    }
Qed.