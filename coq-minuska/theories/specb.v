From Minuska Require Import
    prelude
    spec
    basic_properties
.

Definition Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar_b
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (bv : BuiltinOrVar)
    : bool
:= match bv with
    | bov_builtin b => bool_decide (t = t_over b)
    | bov_variable x => bool_decide (ρ !! x = Some t)
    end
.

Lemma Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar_reflect
    {Σ : StaticModel}
    : forall ρ t bv,
        reflect
            (Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar ρ t bv)
            (Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar_b ρ t bv)
.
Proof.
    intros.
    unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar_b.
    unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar.
    destruct bv; simpl.
    {
        apply bool_decide_reflect.
    }
    {
        apply bool_decide_reflect.
    }
Qed.

Fixpoint forallbin
    {A : Type}
    (l : list A)
    (P : forall (i : nat) (x : A), l !! i = Some x -> bool) : bool
:=
    match l as l0 return ((forall (i : nat) (x : A), l0 !! i = Some x -> bool)) -> bool with
    | nil => fun P' => true
    | (y::l') => fun P' =>
        let b1 := P' 0 y eq_refl in
        let b2 := forallbin l' (fun i' x' pf' => P' (S i') x' pf') in
        b1 && b2
    end P
.

Equations? sat2Bb
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    : bool
    by wf (TermOver_size φ) lt
:=
    sat2Bb ρ t (t_over bv) := Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar_b ρ t bv ;
    sat2Bb ρ (t_over _) (t_term s l) := false ;
    sat2Bb ρ (t_term s' l') (t_term s l) :=
        bool_decide (s' = s) &&
        match (decide (length l' = length l)) with
        | right _ => false
        | left _ => 
            forallbin (zip l l') (fun i xx' pf => let x := xx'.1 in let x' := xx'.2 in
            sat2Bb ρ x' x
        )
        end
    ;
.
Proof.
    abstract(
        ltac1:(replace l with (fst <$> zip l l'))>[
            ()|(apply fst_zip; ltac1:(lia))
        ];
        apply take_drop_middle in pf as pf';
        rewrite <- pf';
        rewrite fmap_app;
        rewrite fmap_cons;
        simpl;
        rewrite sum_list_with_app;
        simpl;
        ltac1:(unfold x);
        ltac1:(lia)
    ).
Defined.

Lemma sat2B_refl
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    :
    reflect (sat2B ρ t φ) (sat2Bb ρ t φ)
.
Proof.
    revert φ.
    unfold TermOver in *.
    ltac1:(induction t using TermOver_rect); intros φ; destruct φ;
        ltac1:(simp sat2B); ltac1:(simp sat2Bb).
    {
        apply Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar_reflect.    
    }
    {
        apply ReflectF.
        ltac1:(tauto).
    }
    {
        apply Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar_reflect.
    }
    {
        ltac1:(rename b into s').
        ltac1:(rename l into l').
        ltac1:(rename l0 into l).
        destruct (decide (s' = s)) as [Hy|Hn].
        {
            destruct (decide (length l' = length l)) as [Hy2|Hn2].
            {
                subst.
                simpl.
                rewrite bool_decide_eq_true_2>[|reflexivity].
                simpl.
                revert X l Hy2.
                induction l'; intros X l Hy2; destruct l; simpl.
                {
                    apply ReflectT.
                    ltac1:(naive_solver).
                }
                {
                    simpl in Hy2.
                    inversion Hy2.
                }
                {
                    simpl in Hy2.
                    inversion Hy2.
                }
                {
                    simpl in Hy2.
                    apply (inj S) in Hy2.
                    simpl in *.
                    ltac1:(ospecialize (IHl' _)).
                    {
                        intros x Hx.
                        specialize (X x).
                        intros φ.
                        ltac1:(ospecialize (X _)).
                        {
                            rewrite elem_of_cons.
                            right.
                            exact Hx.
                        }
                        apply X.
                    }
                    specialize (IHl' l Hy2).
                    (* apply IHl'. *)
                    destruct IHl' as [IHl'|IHl'].
                    {
                        destruct IHl' as [H1 [H2 H3]].
                        clear H1 H2.
                        rewrite andb_comm.
                        simpl.
                        specialize (X a ).
                        ltac1:(ospecialize (X _)).
                        {
                            rewrite elem_of_cons.
                            left.
                            reflexivity.
                        }
                        specialize (X t).
                        destruct X as [X|X].
                        {
                            apply ReflectT.
                            split>[reflexivity|].
                            split>[ltac1:(lia)|].
                            intros i t' φ' HH1 HH2.
                            destruct i.
                            {
                                simpl in *.
                                ltac1:(simplify_eq/=).
                                exact X.
                            }
                            {
                                simpl in *.
                                specialize (H3 _ _ _ HH1 HH2).
                                apply H3.
                            }
                        }
                        {
                            apply ReflectF.
                            intros [HH1 [HH2 HH3]].
                            apply X. clear X.
                            specialize (HH3 0 a t).
                            simpl in HH3.
                            specialize (HH3 eq_refl eq_refl).
                            exact HH3.
                        }
                    }
                    {
                        rewrite andb_comm.
                        simpl.
                        apply ReflectF.
                        intros [HH1 [HH2 HH3]].
                        apply IHl'.
                        clear IHl'.
                        split>[assumption|].
                        split>[assumption|].
                        intros i t' φ' HH4 HH5.
                        specialize (HH3 (S i) _ _ HH4 HH5).
                        exact HH3.
                    }
                }
            }
            {
                subst.
                rewrite bool_decide_eq_true_2>[|reflexivity].
                simpl.
                apply ReflectF.
                ltac1:(tauto).
            }
        }
        {
            rewrite bool_decide_eq_false_2.
            {
                simpl.
                apply ReflectF.
                ltac1:(tauto).
            }
            {
                apply Hn.
            }
        }
    }
Qed.

