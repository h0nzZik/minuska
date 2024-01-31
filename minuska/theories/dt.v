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
    length ps = length vs ->
    (
        forall i p v, ps !! i = Some p -> vs !! i = Some v ->
        pvmatch p v
    ) ->
    pvmatch (p_cpat c ps) (v_cval c vs)
.

Definition pvvecmatch {Σ : Signature}
: PatternVector -> ValueVector -> Prop :=
    fun ps vs => (*length ps = length vs /\ *) (
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
    Forall (fun rowa => let row := rowa.1 in length row = S (length vs)) cm ->
    (
    cmmatch ([(v_cval c ws)] ++ vs) cm a
    <->
    cmmatch (ws ++ vs) (Simplify c cm) a
    )
.
Proof.
    intros cm c vs ws a.
    intros Harity Hnicematrix.
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
        simpl in H2pv.
        (*destruct H2pv as [? H2pv].*)
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
                    (*
                    split.
                    {
                        rewrite app_length.
                        rewrite app_length.
                        rewrite replicate_length.
                        ltac1:(lia).
                    }
                    *)
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
                revert j H1pv Hnicematrix.
                induction cm; intros j H1pv Hnicematrix.
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
                            inversion Hnicematrix. assumption.
                        }
                        {
                            subst. simpl.
                            specialize (IHcm _ H1pv).
                            apply IHcm.
                            inversion Hnicematrix. assumption.
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
                                        ltac1:(exfalso; clear -H5).
                                        unfold decide,decide_rel in H5.
                                        destruct (Constructor_eqdec c0 c0).
                                        {
                                            inversion H5.
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
                            unfold is_left in H5.
                            ltac1:(repeat case_match).
                            {
                                subst. ltac1:(contradiction).
                            }
                            {
                                inversion H5.
                            }
                        }
                        {
                            simpl. apply IHcm. apply H1pv.
                            inversion Hnicematrix. assumption.
                        }
                        {
                            simpl. apply IHcm. apply H1pv.
                            inversion Hnicematrix. assumption.
                        }
                    }
                }
            }
            {
                split.
                {
                    unfold pvvecmatch.
                    (*
                    split.
                    {
                        rewrite app_length.
                        rewrite app_length.
                        rewrite H4.
                        rewrite H0.
                        reflexivity.
                    }
                    *)
                    intros i p v HH1 HH2.
                    ltac1:(rewrite lookup_app in HH1).
                    ltac1:(rewrite lookup_app in HH2).
                    ltac1:(repeat case_match; simplify_eq /=).
                    {
                        eapply H4 with (i := i); simpl; assumption.
                    }
                    {
                        apply lookup_ge_None_1 in H1.
                        apply lookup_lt_Some in H.
                        ltac1:(lia).
                    }
                    {
                        apply lookup_ge_None_1 in H.
                        apply lookup_lt_Some in H1.
                        ltac1:(lia).
                    }
                    {
                        eapply H2'pv with (i := S (i - length ps)); simpl.
                        {
                            apply HH1.
                        }
                        {
                            rewrite H3. assumption.
                        }
                    }
                }
                {
                    rewrite app_length.
                    rewrite app_length.
                    ltac1:(congruence).
                }
            }
        }
    }
    {
        intros H.
        unfold cmmatch in *.
        destruct H as [j [pv [H1 [H2 H3]]]].
        unfold pvvecmatch in *.
        unfold Simplify in H1.
        rewrite <- flat_map_concat_map in H1.
        apply elem_of_list_lookup_2 in H1.
        rewrite elem_of_list_In in H1.
        apply in_flat_map in H1.
        destruct H1 as [[pv' a'][HH1 HH2]].
        rewrite <- elem_of_list_In in HH1.
        apply elem_of_list_lookup_1 in HH1.
        destruct HH1 as [i Hi].
        unfold Simplify_step in HH2. simpl in HH2.
        destruct (head pv') eqn:Heq.
        {
            destruct p.
            {
                inversion HH2; subst; clear HH2.
                inversion H; subst; clear H.
                exists i. exists pv'.
                split>[apply Hi|].
                split.
                {
                    (*
                    split.
                    {
                        simpl.
                        destruct pv'; simpl in *.
                        {
                            inversion Heq.
                        }
                        inversion Heq; subst; clear Heq.
                        rewrite app_length in H3.
                        rewrite app_length in H3.
                        rewrite replicate_length in H3.
                        ltac1:(lia).
                    }
                    *)
                    intros i0 p v HH1 HH2.
                    destruct i0.
                    {
                        inversion HH2; subst; clear HH2.
                        ltac1:(rewrite -head_lookup in HH1).
                        rewrite HH1 in Heq. inversion Heq. subst; clear Heq.
                        constructor.
                    }
                    {
                        simpl in HH2.

                        rewrite app_length in H3.
                        rewrite app_length in H3.
                        rewrite replicate_length in H3.
                        simpl in H3. simpl in Heq.
                        destruct pv'.
                        {
                            simpl in HH1. inversion HH1.
                        }
                        simpl in HH1. simpl in *.
                        (*destruct H2 as [H'2 H2].*)
                        specialize (H2 (i0 + (arity c)) p v).
                        ltac1:(rewrite lookup_app_r in H2).
                        {
                            rewrite replicate_length.
                            ltac1:(lia).
                        }
                        rewrite replicate_length in H2.
                        ltac1:(ospecialize (H2 _)).
                        {
                            ltac1:(cut (i0 = i0 + arity c - arity c)).
                            {
                                intros H. rewrite <- H. assumption. 
                            }
                            {
                                ltac1:(lia).
                            }
                        }
                        apply H2.
                        rewrite Harity.
                        ltac1:(rewrite lookup_app_r).
                        { ltac1:(lia). }
                        ltac1:(cut (i0 = i0 + length ws - length ws)).
                        {
                                intros H. rewrite <- H. assumption. 
                        }
                        {
                                ltac1:(lia).
                        }
                    }
                }
                {
                    simpl.
                    rewrite app_length in H3.
                    rewrite app_length in H3.
                    rewrite replicate_length in H3.
                    simpl in H3.
                    destruct pv'.
                    {
                        simpl in Heq. inversion Heq.
                    }
                    simpl in *.
                    inversion Heq; subst; clear Heq.
                    ltac1:(lia).
                }
                {
                    inversion H.
                }
            }
            {
                unfold is_left in HH2.
                destruct (decide (c0 = c)).
                {
                    subst.
                    inversion HH2; subst; clear HH2.
                    inversion H; subst; clear H.
                    simpl in *.
                    destruct pv'; simpl in *.
                    {
                        inversion Heq.
                    }
                    exists i. exists (p::pv').
                    split>[apply Hi|].
                    split.
                    {
                        inversion Heq; subst; clear Heq.
                        rewrite app_length in H3.
                        rewrite app_length in H3.
                        assert ((length pv') = (length vs)).
                        {
                            simpl.
                            rewrite Forall_forall in Hnicematrix.
                            specialize (Hnicematrix (p_cpat c l :: pv', a)).
                            simpl in Hnicematrix.
                            rewrite elem_of_list_lookup in Hnicematrix.
                            ltac1:(ospecialize (Hnicematrix _)).
                            {
                                eexists. apply Hi.
                            }
                            ltac1:(lia).
                        }
                        (*
                        split.
                        {
                            simpl.
                            ltac1:(lia).
                        }
                        *)
                        intros i0 p0 v HH1 HH2.
                        destruct i0; simpl in *.
                        {
                            inversion HH1. subst; clear HH1.
                            inversion HH2. subst; clear HH2.
                            constructor.
                            ltac1:(lia).
                            intros i0 p0 v HH1 HH2.
                            (*destruct H2 as [_ H2].*)
                            apply H2 with (i := i0).
                            {
                                ltac1:(rewrite lookup_app_l).
                                {
                                    apply lookup_lt_Some in HH1.
                                    apply HH1.
                                }
                                {
                                    apply HH1.
                                }
                            }
                            {
                                ltac1:(rewrite lookup_app_l).
                                {
                                    apply lookup_lt_Some in HH2.
                                    apply HH2.
                                }
                                {
                                    apply HH2.
                                }
                            }
                        }
                        {
                            (*destruct H2 as [_ H2].*)
                            apply H2 with (i := i0 + length l).
                            {
                                ltac1:(rewrite lookup_app_r).
                                {
                                    apply lookup_lt_Some in HH1.
                                    ltac1:(lia).
                                }
                                {
                                    ltac1:(replace (i0 + length l - length l) with (i0) by (lia)).
                                    apply HH1.
                                }
                            }
                            {
                                ltac1:(rewrite lookup_app_r).
                                {
                                    apply lookup_lt_Some in HH1.
                                    ltac1:(lia).
                                }
                                {
                                    ltac1:(replace (i0 + length l - length ws) with (i0) by (lia)).
                                    apply HH2.
                                }
                            }
                        }
                    }
                    {
                        simpl.

                        rewrite Forall_forall in Hnicematrix.
                        specialize (Hnicematrix (p :: pv', a)).
                        simpl in Hnicematrix.
                        rewrite elem_of_list_lookup in Hnicematrix.
                        ltac1:(ospecialize (Hnicematrix _)).
                        {
                            eexists. apply Hi.
                        }
                        ltac1:(lia).
                    }
                    {
                        inversion H.
                    }
                }
                {
                    inversion HH2.
                }
            }
        }
        {
            inversion HH2.
        }
    }
Qed.

Definition row_startswith_wildcard
    {Σ : Signature}
    {A : Type}
    : (PatternVector*A) -> Prop
:= fun row => match row.1 with
| p_wildcard::_ => True
| _ => False
end.

#[local]
Instance row_startswith_wildcard_dec
    {Σ : Signature}
    {A : Type}
    (row : PatternVector*A)
    : Decision (row_startswith_wildcard row)
.
Proof.
    destruct row. destruct p; unfold row_startswith_wildcard; simpl.
    {
        apply _.
    }
    {
        destruct p; apply _.
    }
Defined.

Definition Default {Σ : Signature} {A : Type}
    : Constructor -> ClauseMatrix A -> ClauseMatrix A
:=
    fun c cm => 
    let tmp := filter row_startswith_wildcard cm in
    fmap (fun x => (tail x.1, x.2)) tmp
.

Definition row_startswith_ctor
    {Σ : Signature}
    {A : Type}
    (c : Constructor)
    : (PatternVector*A) -> Prop
:= fun row => match row.1 with
| (p_cpat c' _)::_ => c' = c
| _ => False
end.

#[local]
Instance row_startswith_ctor_dec
    {Σ : Signature}
    {A : Type}
    (c : Constructor)
    (row : PatternVector*A)
    : Decision (row_startswith_ctor c row)
.
Proof.
    unfold row_startswith_ctor.
    destruct row.
    destruct p; simpl.
    { apply _. }
    {
        destruct p; apply _.
    }
Defined.


Definition isHeadInFirstColumn
    {Σ : Signature} {A : Type}
    : Constructor -> ClauseMatrix A -> Prop
:=
    fun c cm => Exists (row_startswith_ctor c) cm
.

Lemma Default_correct
    {Σ : Signature} {A : Type}
    (c : Constructor)
    (vs ws : ValueVector)
    (cm : ClauseMatrix A)
    (a : A)
    :
    (not (isHeadInFirstColumn c cm)) -> 
    (arity c = length ws) ->
    cmmatch ([(v_cval c ws)] ++ vs) cm a
    <->
    cmmatch (vs) (Default c cm) a
.
Proof.
    intros Hnothead Harity.
    unfold Default.
    unfold isHeadInFirstColumn in Hnothead.
    simpl.
    unfold cmmatch.
    split; intros H.
    {
        destruct H as [j [pv [H1 [H2 H3]]]].
        (*inversion H2; subst; clear H2.*)
        simpl in *.
        destruct pv.
        {
            simpl in H3. inversion H3.
        }
        assert (H2' := H2).
        unfold pvvecmatch in H2'.
        specialize (H2' 0 p (v_cval c ws)).
        simpl in H2'.
        specialize (H2' eq_refl eq_refl).
        rewrite <- Forall_Exists_neg in Hnothead.
        inversion H2'; subst; clear H2'.
        {
            assert (HH:(p_wildcard::pv, a) ∈ filter row_startswith_wildcard cm).
            {
                rewrite elem_of_list_filter.
                split.
                {
                    unfold row_startswith_wildcard. simpl. exact I.
                }
                {
                    rewrite elem_of_list_lookup.
                    exists j. exact H1.
                }
            }
            rewrite elem_of_list_lookup in HH.
            destruct HH as [i HHi].
            simpl in H3.
            exists i. exists (pv).
            split.
            {
                ltac1:(rewrite list_lookup_fmap).
                rewrite HHi. simpl. reflexivity.
            }
            split.
            {
                apply elem_of_list_lookup_2 in HHi.
                apply elem_of_list_filter in HHi.
                destruct HHi as [HH1 HH2].
                unfold pvvecmatch.
                simpl.
                intros i0 p v.
                intros HHH1 HHH2. simpl in *.
                apply H2 with (i := S i0).
                { apply HHH1. }
                { apply HHH2. }
            }
            { ltac1:(lia). }
        }
        {
            rewrite Forall_forall in Hnothead.
            specialize (Hnothead (p_cpat c ps::pv, a)).
            rewrite elem_of_list_lookup in Hnothead.
            ltac1:(ospecialize (Hnothead _)).
            {
                exists j. apply H1.
            }
            ltac1:(exfalso).
            apply Hnothead. clear Hnothead.
            unfold row_startswith_ctor. simpl. reflexivity.
        }
    }
    {
        destruct H as [j [pv [H1 [H2 H3]]]].
        ltac1:(rewrite list_lookup_fmap in H1).
        unfold fmap,option_fmap,option_map in H1.
        ltac1:(case_match).
        {
            inversion H1; subst; clear H1.
            apply elem_of_list_lookup_2 in H.
            apply elem_of_list_filter in H.
            destruct H as [HH1 HH2].
            rewrite elem_of_list_lookup in HH2.
            destruct HH2 as [i Hi].
            destruct p as [ps a]. simpl.
            simpl in *.
            exists i. exists ps.
            split>[apply Hi|].
            split.
            {
                simpl in *.
                unfold pvvecmatch.
                intros i0 p0 v0 Hp0 Hv0.
                destruct i0.
                {
                    simpl in *. inversion Hv0. subst. clear Hv0.
                    unfold row_startswith_wildcard in HH1. simpl in HH1.
                    destruct ps.
                    {
                        simpl in *. inversion Hp0.
                    }
                    {
                        simpl in *. inversion Hp0. subst. clear Hp0.
                        destruct p0.
                        {
                            constructor.
                        }
                        {
                            inversion HH1.
                        }
                    }
                }
                simpl in *.
                apply H2 with (i := i0).
                {
                    destruct ps.
                    {
                        simpl in Hp0. inversion Hp0.
                    }
                    simpl in Hp0. simpl. exact Hp0.
                }
                {
                    exact Hv0.
                }
            }
            {
                destruct ps; simpl in *.
                {
                    unfold row_startswith_wildcard in HH1. simpl in HH1.
                    inversion HH1.
                }
                ltac1:(lia).
            }
        }
        {
            inversion H1.
        }
    }
Qed.



