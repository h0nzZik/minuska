From Minuska Require Import
    prelude
    spec_syntax
    syntax_properties
.

Section sec.

    Context
        {symbol : Set}
        {symbols : Symbols symbol}
    .

    Inductive BuiltinValue0 :=
    | bv_error
    | bv_bool (b : bool)
    | bv_nat (n : nat)
    | bv_Z (z : Z)
    | bv_sym (s : symbol)
    | bv_str (s : string)
    | bv_list (m : list (AppliedOperatorOr' symbol BuiltinValue0))
    | bv_pmap (m : Pmap (AppliedOperatorOr' symbol BuiltinValue0))
    .

    Fixpoint BVsize (r : BuiltinValue0) : nat :=
    match r with
    | bv_list m =>
        let my_list_size := (fix my_list_size (l : list (AppliedOperatorOr' symbol BuiltinValue0)) : nat :=
        match l with
        | nil => 1
        | (cons (aoo_operand o) xs) => S ((BVsize o) + (my_list_size xs))
        | (cons (aoo_app ao) xs) =>
            let myaosize := (fix myaosize (ao : AppliedOperator' symbol BuiltinValue0) : nat :=
            match ao with
            | (ao_operator _) => 1
            | (ao_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
            | (ao_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
            end) in
            S ((myaosize ao) + (my_list_size xs))
        end) in
        S (my_list_size m)
    | bv_pmap (PNodes m) =>
        let my_pmapne_size := (fix my_pmapne_size (m : Pmap_ne (AppliedOperatorOr' symbol BuiltinValue0)) : nat :=
    match m with
    | (PNode001 n) => S (my_pmapne_size n)
    | (PNode010 (aoo_operand o)) => S (BVsize o)
    | (PNode010 (aoo_app a)) =>
        let myaosize := (fix myaosize (ao : AppliedOperator' symbol BuiltinValue0) : nat :=
        match ao with
        | (ao_operator _) => 1
        | (ao_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
        | (ao_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
        end) in
        S (myaosize a)
    | (PNode011 (aoo_operand o) n) => S ((BVsize o) + (my_pmapne_size n))
    | (PNode011 (aoo_app a) n) =>
        let myaosize := (fix myaosize (ao : AppliedOperator' symbol BuiltinValue0) : nat :=
        match ao with
        | (ao_operator _) => 1
        | (ao_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
        | (ao_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
        end) in
        S ((myaosize a) + (my_pmapne_size n))
    | (PNode100 n) => S (my_pmapne_size n)
    | (PNode101 n1 n2) => S ((my_pmapne_size n1) + (my_pmapne_size n2))
    | (PNode110 n (aoo_operand o)) => S ((BVsize o) + (my_pmapne_size n))
    | (PNode110 n (aoo_app a)) =>
        let myaosize := (fix myaosize (ao : AppliedOperator' symbol BuiltinValue0) : nat :=
        match ao with
        | (ao_operator _) => 1
        | (ao_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
        | (ao_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
        end) in
        S ((myaosize a) + (my_pmapne_size n))
    | (PNode111 n1 (aoo_app a) n2) =>
        let myaosize := (fix myaosize (ao : AppliedOperator' symbol BuiltinValue0) : nat :=
        match ao with
        | (ao_operator _) => 1
        | (ao_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
        | (ao_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
        end) in
        S ((myaosize a) + (my_pmapne_size n1) + (my_pmapne_size n2))
    | (PNode111 n1 (aoo_operand o) n2) => S ((BVsize o) + (my_pmapne_size n1) + (my_pmapne_size n2))
    end) in
        S (my_pmapne_size m)
    | bv_pmap (PEmpty) => 1
    | bv_error => 1
    | bv_bool _ => 1
    | bv_nat _ => 1
    | bv_sym _ => 1
    | bv_str _ => 1
    | bv_Z _ => 1
    end
    .

    Lemma BuiltinValue0_eqdec_helper_0 (sz : nat):
        ∀ x y : BuiltinValue0, BVsize x <= sz ->
            {x = y} + {x ≠ y}
    .
    Proof.
        intros x y Hsz.
        revert x Hsz y.
        induction sz; intros x Hsz y.
        {
            destruct x; simpl in Hsz; try ltac1:(lia).
            destruct m; simpl in Hsz; try ltac1:(lia).
        }
        {
            destruct x.
            {
                destruct y;
                try (solve [left; reflexivity]);
                right; ltac1:(discriminate).
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (b = b0)).
                {
                    subst; left. reflexivity.
                }
                {
                    right; ltac1:(congruence).
                }
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (n = n0)).
                {
                    subst; left. reflexivity.
                }
                {
                    right; ltac1:(congruence).
                }
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (z = z0)).
                {
                    subst; left. reflexivity.
                }
                {
                    right; ltac1:(congruence).
                }
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (s = s0)).
                {
                    subst; left. reflexivity.
                }
                {
                    right; ltac1:(congruence).
                }
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (s = s0)).
                {
                    subst; left. reflexivity.
                }
                {
                    right; ltac1:(congruence).
                }
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                revert m0.
                induction m; intros m0.
                {
                    destruct m0.
                    {
                        left. reflexivity.
                    }
                    {
                        right. ltac1:(congruence).
                    }
                }
                {
                    destruct m0.
                    {
                        right; ltac1:(congruence).
                    }
                    {
                        destruct a, a0.
                        {
                            assert (IH1 := IHm ltac:(simpl in *; lia) m0).
                            destruct IH1 as [IH1|IH1].
                            {
                                inversion IH1; subst; clear IH1.
                                revert ao0.
                                induction ao; intros ao0.
                                {
                                    destruct ao0.
                                    {
                                        destruct (decide (s = s0)).
                                        {
                                            subst; left. reflexivity.
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        assert (IH1 := IHao ltac:(simpl in *; lia) ao0).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            inversion IH1; subst; clear IH1.
                                            assert(IH2 := IHsz b ltac:(simpl in *; lia) b0).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                subst.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        assert (IH1 := IHao1 ltac:(simpl in *; lia) ao0_1).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            inversion IH1; subst; clear IH1.
                                            assert(IH2 := IHao2 ltac:(simpl in *; lia) ao0_2).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                inversion IH2; subst; clear IH2.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                }
                            }
                            {
                                right; ltac1:(congruence).
                            }
                        }
                        {
                            right; ltac1:(congruence).
                        }
                        {
                            right; ltac1:(congruence).
                        }
                        {
                            specialize (IHsz operand ltac:(simpl in *; lia) operand0).
                            specialize (IHm ltac:(simpl in *; lia) m0).

                            destruct IHsz as [IHsz|IHsz], IHm as [IHm|IHm].
                            {
                                inversion IHm; subst; left. reflexivity.
                            }
                            {
                                right; ltac1:(congruence).
                            }
                            {
                                right; ltac1:(congruence).
                            }
                            {
                                right; ltac1:(congruence).
                            }
                        }
                    }
                }
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct m, m0.
                {
                    left. reflexivity.
                }
                {
                    right; ltac1:(congruence).
                }
                {
                    right; ltac1:(congruence).
                }
                {
                    revert p0.
                    induction p; intros p0.
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).
                        assert (IH1 := IHp ltac:(simpl in *; lia) p0).
                        destruct IH1 as [IH1|IH1].
                        {
                            inversion IH1; subst; left; reflexivity.
                        }
                        {
                            right; ltac1:(congruence).
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        destruct a,a0.
                        {
                            revert ao0.
                            induction ao; intros ao0.
                            {
                                destruct ao0.
                                {
                                    destruct (decide (s = s0)).
                                    {
                                        subst; left. reflexivity.
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    right; ltac1:(congruence).
                                }
                                {
                                    right; ltac1:(congruence).
                                }
                            }
                            {
                                destruct ao0.
                                {
                                    right; ltac1:(congruence).
                                }
                                {
                                    assert (IH1 := IHao ltac:(simpl in *; lia) ao0).
                                    destruct IH1 as [IH1|IH1].
                                    {
                                        inversion IH1; subst; clear IH1.
                                        assert(IH2 := IHsz b ltac:(simpl in *; lia) b0).
                                        destruct IH2 as [IH2|IH2].
                                        {
                                            subst.
                                            left; reflexivity.
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    right; ltac1:(congruence).
                                }
                            }
                            {
                                destruct ao0.
                                {
                                    right; ltac1:(congruence).
                                }
                                {
                                    right; ltac1:(congruence).
                                }
                                {
                                    assert (IH1 := IHao1 ltac:(simpl in *; lia) ao0_1).
                                    destruct IH1 as [IH1|IH1].
                                    {
                                        inversion IH1; subst; clear IH1.
                                        assert(IH2 := IHao2 ltac:(simpl in *; lia) ao0_2).
                                        destruct IH2 as [IH2|IH2].
                                        {
                                            inversion IH2; subst; clear IH2.
                                            left; reflexivity.
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                            }
                        }
                        {
                            right; ltac1:(congruence).
                        }
                        {
                            right; ltac1:(congruence).
                        }
                        {
                            assert (IH1 := IHsz operand ltac:(simpl in *; lia) operand0).
                            destruct IH1 as [IH1|IH1].
                            {
                                subst; left; reflexivity.
                            }
                            {
                                right; ltac1:(congruence).
                            }
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(congruence)]).

                        destruct a,a0.
                        {

                            assert (IH1 := IHp ltac:(simpl in *; lia) p0).
                            destruct IH1 as [IH1|IH1].
                            {
                                inversion IH1; subst; clear IH1.
                                revert ao0.
                                induction ao; intros ao0.
                                {
                                    destruct ao0.
                                    {
                                        destruct (decide (s = s0)).
                                        {
                                            subst; left. reflexivity.
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        assert (IH1 := IHao ltac:(simpl in *; lia) ao0).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            inversion IH1; subst; clear IH1.
                                            assert(IH2 := IHsz b ltac:(simpl in *; lia) b0).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                subst.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        assert (IH1 := IHao1 ltac:(simpl in *; lia) ao0_1).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            inversion IH1; subst; clear IH1.
                                            assert(IH2 := IHao2 ltac:(simpl in *; lia) ao0_2).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                inversion IH2; subst; clear IH2.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                }
                            }
                            {
                                right; ltac1:(congruence).
                            }
                            
                        }
                        {
                            right; ltac1:(congruence).
                        }
                        {
                            right; ltac1:(congruence).
                        }
                        {
                            assert (IH1 := IHsz operand ltac:(simpl in *; lia) operand0).
                            destruct IH1 as [IH1|IH1].
                            {
                                subst.

                                assert (IH2 := IHp ltac:(simpl in *; lia) p0).
                                destruct IH2 as [IH2|IH2].
                                {
                                    inversion IH2; subst; clear IH2; left; reflexivity.
                                }
                                {
                                    right; ltac1:(congruence).
                                }
                            }
                            {
                                right; ltac1:(congruence).
                            }
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        assert (IH1 := IHp ltac:(simpl in *; lia) p0).
                        destruct IH1 as [IH1|IH1].
                        {
                            inversion IH1; subst; clear IH1.
                            left. reflexivity.
                        }
                        {
                            right; ltac1:(congruence).
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        assert (IH1 := IHp1 ltac:(simpl in *; lia) p0_1).
                        assert (IH2 := IHp2 ltac:(simpl in *; lia) p0_2).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                        {
                            inversion IH1; subst; clear IH1.
                            inversion IH2; subst; clear IH2.
                            left. reflexivity.
                        }
                        {
                            right; ltac1:(congruence).
                        }
                        {
                            right; ltac1:(congruence).
                        }
                        {
                            right; ltac1:(congruence).
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        destruct a,a0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(congruence)]).

                        {
                            assert (IH1 := IHp ltac:(simpl in *; lia) p0).
                            destruct IH1 as [IH1|IH1].
                            {
                                inversion IH1; subst; clear IH1.


                                revert ao0.
                                induction ao; intros ao0.
                                {
                                    destruct ao0.
                                    {
                                        destruct (decide (s = s0)).
                                        {
                                            subst; left. reflexivity.
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        assert (IH1 := IHao ltac:(simpl in *; lia) ao0).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            inversion IH1; subst; clear IH1.
                                            assert(IH2 := IHsz b ltac:(simpl in *; lia) b0).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                subst.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        assert (IH1 := IHao1 ltac:(simpl in *; lia) ao0_1).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            inversion IH1; subst; clear IH1.
                                            assert(IH2 := IHao2 ltac:(simpl in *; lia) ao0_2).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                inversion IH2; subst; clear IH2.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                }
                            }
                            {
                                right; ltac1:(congruence).
                            }
                        }
                        {
                            assert (IH1 := IHsz operand ltac:(simpl in *; lia) operand0).
                            destruct IH1 as [IH1|IH1].
                            {
                                subst.
                                assert (IH1 := IHp ltac:(simpl in *; lia) p0).
                                destruct IH1 as [IH1|IH1].
                                {
                                    inversion IH1; subst; clear IH1.
                                    left. reflexivity.
                                }
                                {
                                    right; ltac1:(congruence).
                                }
                            }
                            {
                                right; ltac1:(congruence).
                            }
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        destruct a,a0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(congruence)]).

                        {
                            assert (IH1 := IHp1 ltac:(simpl in *; lia) p0_1).
                            assert (IH2 := IHp2 ltac:(simpl in *; lia) p0_2).
                            destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                            {
                                inversion IH1; subst; clear IH1.
                                inversion IH2; subst; clear IH2.
                                
                                revert ao0.
                                induction ao; intros ao0.
                                {
                                    destruct ao0.
                                    {
                                        destruct (decide (s = s0)).
                                        {
                                            subst; left. reflexivity.
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        assert (IH1 := IHao ltac:(simpl in *; lia) ao0).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            inversion IH1; subst; clear IH1.
                                            assert(IH2 := IHsz b ltac:(simpl in *; lia) b0).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                subst.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        right; ltac1:(congruence).
                                    }
                                    {
                                        assert (IH1 := IHao1 ltac:(simpl in *; lia) ao0_1).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            inversion IH1; subst; clear IH1.
                                            assert(IH2 := IHao2 ltac:(simpl in *; lia) ao0_2).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                inversion IH2; subst; clear IH2.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(congruence).
                                        }
                                    }
                                }

                            }
                            {
                                right; ltac1:(congruence).
                            }
                            {
                                right; ltac1:(congruence).
                            }
                            {
                                right; ltac1:(congruence).
                            }
                        }
                        {
                            assert (IH1 := IHp1 ltac:(simpl in *; lia) p0_1).
                            assert (IH2 := IHp2 ltac:(simpl in *; lia) p0_2).
                            assert (IH3 := IHsz operand ltac:(simpl in *; lia) operand0).

                            destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                            {
                                inversion IH1; subst; clear IH1.
                                inversion IH2; subst; clear IH2.
                                destruct IH3 as [IH3|IH3].
                                {
                                    subst. left. reflexivity.
                                }
                                {
                                    right; ltac1:(congruence).
                                }
                            }
                            {
                                right; ltac1:(congruence).
                            }
                            {
                                right; ltac1:(congruence).
                            }
                            {
                                right; ltac1:(congruence).
                            }
                        }
                    }
                }
            }

        }
    Defined.

    #[export]
    Instance BuiltinValue0_eqdec : EqDecision BuiltinValue0.
    Proof.
        intros x y.
        unfold Decision.
        eapply BuiltinValue0_eqdec_helper_0.
        apply reflexivity.
    Defined.

    Inductive BVLeaf :=
    | bvl_error
    | bvl_bool (b : bool)
    | bvl_nat (n : nat)
    | bvl_Z (z : Z)
    | bvl_str (s : string)
    | bvl_sym (sym : symbol)
    .

    #[export]
    Instance BVLeaf_eqdec : EqDecision BVLeaf.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Fixpoint tree_to_bv
        (t : gen_tree BVLeaf) : (option BuiltinValue0)  :=
    match t with
    | ((GenNode 1 nil)) => Some (bv_pmap (PEmpty))
    | (GenLeaf bvl_error)      => Some (bv_error)  
    | (GenLeaf (bvl_bool b))   => Some (bv_bool b) 
    | (GenLeaf (bvl_nat n))    => Some (bv_nat n) 
    | (GenLeaf (bvl_Z z))      => Some (bv_Z z) 
    | (GenLeaf (bvl_str s))      => Some (bv_str s) 
    | (GenLeaf (bvl_sym s))      => Some (bv_sym s) 
    | (GenNode 0 l)            => (
            let tree_to_mylist := fix tree_to_mylist (l' : list (gen_tree BVLeaf)) :
                (option (list (AppliedOperatorOr' symbol BuiltinValue0))) := (
                match l' with
                | nil                             => Some nil
                | (cons (GenNode 1 [(o)]) (xs))   => (
                    o' ← (tree_to_bv o);
                    xs' ← (tree_to_mylist xs);
                    Some (cons (aoo_operand o') xs')
                )
                | (cons (GenNode 0 [(ao)]) (xs)) => (
                    let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (ao_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (ao_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (ao_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                    ao' ← (tree_to_myao ao);
                    xs' ← (tree_to_mylist xs);
                    Some (cons (aoo_app ao') xs') 
                )
                | _ => None
                end
            ) in
            l' ← tree_to_mylist l;
            Some (bv_list (l'))
        )
    | (GenNode 2 [(m)]) => (
            let tree_to_mypm := fix tree_to_mypm (p : (gen_tree BVLeaf)) : option (Pmap_ne (AppliedOperatorOr' symbol BuiltinValue0)) := (
            match p with
            | (GenNode 1 [(n)]) => (
                n' ← (tree_to_mypm n);
                Some (PNode001 n')
            )
            | (GenNode 2 [(GenNode 1 [(o)])]) => (
                o' ← (tree_to_bv o);
                Some (PNode010 (aoo_operand o')) 
            )
            | (GenNode 2 [(GenNode 0 [(ao')])]) => (
                let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (ao_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (ao_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (ao_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                ao'' ← (tree_to_myao ao');
                Some (PNode010 (aoo_app ao''))
            )
            
            | (GenNode 3 [(GenNode 1 [(o)]);(y')])  => (
                o' ← (tree_to_bv o);
                y'' ← (tree_to_mypm y');
                Some (PNode011 (aoo_operand o') y'')
            )
            | (GenNode 3 [(GenNode 0 [(ao')]);(y')]) => (
                let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (ao_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (ao_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (ao_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                ao'' ← (tree_to_myao ao');
                y'' ← (tree_to_mypm y');
                Some (PNode011 (aoo_app ao'') y'')
            )
            | (GenNode 4 [(x')]) => (
                x'' ← (tree_to_mypm x');
                Some (PNode100 x'') 
            )
            | (GenNode 5 [(x'); (y')]) => (
                x'' ← (tree_to_mypm x');
                y'' ← (tree_to_mypm y');
                Some (PNode101 x'' y'') 
            )
            | (GenNode 6 [(x'); (GenNode 1 [(o')])]) => (
                x'' ← (tree_to_mypm x');
                o'' ← (tree_to_bv o');
                Some (PNode110 x'' (aoo_operand o''))
                )
            | (GenNode 6 [(x'); (GenNode 0 [(ao')])]) => (
                let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (ao_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (ao_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (ao_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                x'' ← (tree_to_mypm x');
                ao'' ← (tree_to_myao ao');
                Some (PNode110 x'' (aoo_app ao''))
            )
            | (GenNode 7%nat  [(x'); (GenNode 1 [(o)]); (z')]) => (
                x'' ← (tree_to_mypm x');
                o' ← (tree_to_bv o);
                z'' ← (tree_to_mypm z');
                Some (PNode111 x'' (aoo_operand o') z'')
            )
            | (GenNode 7%nat  [(x'); (GenNode 0 [(ao')]); (z')]) => (
                let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (ao_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (ao_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (ao_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                ao'' ← (tree_to_myao ao');
                z'' ← (tree_to_mypm z');
                x'' ← (tree_to_mypm x');
                Some (PNode111 x'' (aoo_app ao'') z'')
            )
            | _ => None
            end) in
            m' ← (tree_to_mypm m);
            Some (bv_pmap (PNodes m'))
        )
        | _ => None
    end.
        
    Fixpoint bv_to_tree
        (r : BuiltinValue0) : (gen_tree BVLeaf) :=
    match r with
    | (bv_pmap (PEmpty)) => (GenNode 1 nil)
    | (bv_error)         => (GenLeaf bvl_error)
    | (bv_bool b)        => (GenLeaf (bvl_bool b))
    | (bv_nat n)         => (GenLeaf (bvl_nat n))
    | (bv_Z z)           => (GenLeaf (bvl_Z z))
    | (bv_sym s)           => (GenLeaf (bvl_sym s))
    | (bv_str s)           => (GenLeaf (bvl_str s))
    | (bv_list l)        =>
        let mylist_to_tree := (
            fix mylist_to_tree
                (l' : list (AppliedOperatorOr' symbol BuiltinValue0)) : list (gen_tree BVLeaf) := (
            match l' with
            | nil => nil
            | (cons (aoo_operand o) xs) => cons (GenNode 1 [(bv_to_tree o)]) (mylist_to_tree xs)
            | (cons (aoo_app ao) xs) => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (ao_operator o) => GenLeaf (bvl_sym o)
                    | (ao_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (ao_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
                    end
                    )
                ) in
                cons (GenNode 0 [(myao_to_tree ao)]) (mylist_to_tree xs)
                )
            end
            )
        ) in
        (GenNode 0 (mylist_to_tree l))       
    | (bv_pmap (PNodes m)) => (
        let mypm_to_tree := (
            fix mypm_to_tree (p : Pmap_ne (AppliedOperatorOr' symbol BuiltinValue0)) : gen_tree BVLeaf := (
            match p with
            | (PNode001 n)                     => GenNode 1 [(mypm_to_tree n)]
            | (PNode010 (aoo_operand o))       => GenNode 2 [(GenNode 1 [(bv_to_tree o)])]
            | (PNode010 (aoo_app ao'))         => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (ao_operator o) => GenLeaf (bvl_sym o)
                    | (ao_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (ao_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
                    end
                    )
                ) in
                GenNode 2 [(GenNode 0 [(myao_to_tree ao')])]
            )
            | (PNode011 (aoo_operand o) y')    => GenNode 3 [(GenNode 1 [(bv_to_tree o)]);(mypm_to_tree y')]
            | (PNode011 (aoo_app ao') y')      => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (ao_operator o) => GenLeaf (bvl_sym o)
                    | (ao_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (ao_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
                    end
                    )
                ) in
                GenNode 3 [(GenNode 0 [(myao_to_tree ao')]);(mypm_to_tree y')]
            )
            | (PNode100 x')                    => GenNode 4 [(mypm_to_tree x')]
            | (PNode101 x' y')                 => GenNode 5 [(mypm_to_tree x'); (mypm_to_tree y')]
            | (PNode110 x' (aoo_operand o'))   => GenNode 6 [(mypm_to_tree x'); (GenNode 1 [(bv_to_tree o')])]
            | (PNode110 x' (aoo_app ao'))      => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (ao_operator o) => GenLeaf (bvl_sym o)
                    | (ao_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (ao_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
                    end
                    )
                ) in
                GenNode 6 [(mypm_to_tree x'); (GenNode 0 [(myao_to_tree ao')])]
            )
            | (PNode111 x' (aoo_operand o) z') => GenNode 7%nat  [(mypm_to_tree x'); (GenNode 1 [(bv_to_tree o)]); (mypm_to_tree z')]
            | (PNode111 x' (aoo_app ao') z')   => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (ao_operator o) => GenLeaf (bvl_sym o)
                    | (ao_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (ao_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
                    end
                    )
                ) in
                GenNode 7%nat  [(mypm_to_tree x'); (GenNode 0 [(myao_to_tree ao')]); (mypm_to_tree z')]
            )
            end
            )
        ) in
        (GenNode 2 [(mypm_to_tree m)])
    )
    end
    .
    
    Lemma from_to_tree : forall r, tree_to_bv (bv_to_tree r) = Some r
    .
    Proof.
        intros r.
        remember (BVsize r) as sz.
        assert(BVsize r <= sz) by (ltac1:(lia)).
        clear Heqsz.
        revert r H.
        induction sz.
        {
            intros r Hr.
            destruct r; simpl in Hr; try ltac1:(lia).
            destruct m; simpl in Hr; try ltac1:(lia).
        }
        intros r Hr.
        destruct r; try reflexivity.
        {
            unfold bv_to_tree; fold bv_to_tree.
            induction m; try reflexivity.
            {
                destruct a; unfold bv_to_tree; fold bv_to_tree.
                {
                    ltac1:(specialize (IHm ltac:(simpl in *; lia))).
                    simpl in IHm.
                    rewrite bind_Some in IHm.
                    destruct IHm as [x [IHm1 IHm2]].
                    inversion IHm2; subst; clear IHm2.    
                    induction ao.
                    {
                        simpl.
                        rewrite bind_Some.
                        exists (aoo_app (ao_operator s) :: m).
                        split>[|reflexivity].
                        rewrite bind_Some.
                        exists m.
                        split>[|reflexivity].
                        apply IHm1.
                    }
                    {
                        simpl in IHao.
                        rewrite bind_Some in IHao.
                        ltac1:(ospecialize (IHao _)).
                        {
                            clear IHao.
                            simpl in Hr.
                            ltac1:(lia).
                        }
                        destruct IHao as [x [IHao1 IHao2]].
                        inversion IHao2; subst; clear IHao2.
                        rewrite bind_Some in IHao1.
                        destruct IHao1 as [x IHao1].
                        destruct IHao1 as [IHao1 IHao2].
                        rewrite bind_Some in IHao2.
                        destruct IHao2 as [y [IHao21 IHao22]].
                        inversion IHao22; subst; clear IHao22.

                        simpl.
                        rewrite bind_Some.
                        exists (aoo_app (ao_app_operand ao b) :: m).
                        split>[|reflexivity].
                        

                        rewrite bind_Some.
                        exists (ao_app_operand ao b).
                        split.
                        {
                            rewrite bind_Some.
                            ltac1:(setoid_rewrite bind_Some).
                            assert(IH := IHsz b).
                            ltac1:(ospecialize (IH _)).
                            {
                                simpl in Hr.
                                ltac1:(lia).
                            }
                            exists ao.
                            simpl.
                            split.
                            {
                                rewrite IHao1.
                                reflexivity.
                            }
                            {
                                exists b.
                                split>[apply IH|].
                                reflexivity.
                            }
                        }
                        {
                            rewrite bind_Some.
                            exists m.
                            split>[|reflexivity].
                            apply IHao21.
                        }
                    }
                    {
                        simpl.
                        rewrite bind_Some.
                        exists (aoo_app (ao_app_ao ao1 ao2) :: m).
                        split>[|reflexivity].
                        rewrite bind_Some.
                        exists ((ao_app_ao ao1 ao2)).

                        simpl in IHao1.
                        ltac1:(ospecialize (IHao1 _)).
                        {
                            simpl in Hr. ltac1:(lia).
                        }
                        rewrite bind_Some in IHao1.
                        destruct IHao1 as [x [IHao11 IHao12]].
                        inversion IHao12; subst; clear IHao12.
                        rewrite bind_Some in IHao11.
                        destruct IHao11 as [x [IHao111 IHao112]].
                        rewrite bind_Some in IHao112.
                        destruct IHao112 as [x' [IHao1121 IHao1122]].
                        inversion IHao1122; subst; clear IHao1122.

                        ltac1:(ospecialize (IHao2 _)).
                        {
                            simpl in Hr. ltac1:(simpl in *; lia).
                        }
                        simpl in IHao2.
                        rewrite bind_Some in IHao2.
                        destruct IHao2 as [x [IHao21 IHao22]].
                        inversion IHao22; subst; clear IHao22.
                        rewrite bind_Some in IHao21.
                        destruct IHao21 as [x [IHao211 IHao212]].
                        rewrite bind_Some in IHao212.
                        destruct IHao212 as [x' [IHao2121 IHao2122]].
                        inversion IHao2122; subst; clear IHao2122.

                        split.
                        {
                            rewrite bind_Some.
                            exists ao1.
                            rewrite bind_Some.
                            split.
                            {
                                apply IHao111.
                            }
                            {
                                exists ao2.
                                split>[|reflexivity].
                                apply IHao211.
                            }
                        }
                        {
                            rewrite bind_Some.
                            exists m.
                            split>[|reflexivity].
                            apply IHao2121.
                        }
                    }
                }
                {
                    simpl.
                    rewrite bind_Some.
                    exists ((aoo_operand operand :: m)).
                    split>[|reflexivity].
                    rewrite bind_Some.
                    exists operand.
                    rewrite bind_Some.
                    split.
                    {
                        apply IHsz.
                        simpl in Hr.
                        ltac1:(lia).
                    }
                    {
                        eexists.
                        split>[|reflexivity].
                        ltac1:(ospecialize (IHm _)).
                        {
                            simpl in Hr.
                            simpl.
                            ltac1:(lia).
                        }
                        simpl in IHm.
                        rewrite bind_Some in IHm.
                        destruct IHm as [x [IH1m IH2m]].
                        inversion IH2m; subst; clear IH2m.
                        apply IH1m.
                    }
                }
            }
        }
        {
            destruct m; simpl in *.
            {
                reflexivity.
            }
            {
                rewrite bind_Some.
                exists p.
                split>[|reflexivity].
                induction p; try reflexivity.
                {
                    rewrite bind_Some.
                    exists p.
                    split>[|reflexivity]. apply IHp. ltac1:(lia).
                }
                {
                    destruct a.
                    {
                        rewrite bind_Some.
                        exists ao.
                        split>[|reflexivity].
                        induction ao; try reflexivity.
                        {
                        rewrite bind_Some. exists ao. split.
                        {
                            apply IHao. ltac1:(lia).
                        } { rewrite bind_Some. exists b. split>[|reflexivity]. apply IHsz. ltac1:(lia). }
                        }
                        { rewrite bind_Some. exists ao1. split.
                        {
                            apply IHao1. ltac1:(lia).
                        }
                        {
                            rewrite bind_Some. exists ao2. split>[|reflexivity].
                            apply IHao2. ltac1:(lia).
                        }
                        }
                    }
                    {
                        rewrite bind_Some. exists operand. split>[|reflexivity]. apply IHsz. ltac1:(lia).
                    }
                }
{
                    destruct a.
                    {
                        rewrite bind_Some.
                        exists ao.
                        split.
                        {
                        induction ao; try reflexivity.
                        {
                        rewrite bind_Some. exists ao. split.
                        {
                            apply IHao. ltac1:(lia).
                        } { rewrite bind_Some. exists b. split>[|reflexivity]. apply IHsz. ltac1:(lia). }
                        }
{
                        rewrite bind_Some. 
                        exists ao1. split. { apply IHao1. ltac1:(lia). } { rewrite bind_Some. exists ao2. split>[|reflexivity]. apply IHao2. ltac1:(lia).  }
                    }
}
                        { rewrite bind_Some. exists p. split. { apply IHp. ltac1:(lia). }
                        { reflexivity. }
                        }
                    }
                    {
                        rewrite bind_Some. 
                        exists operand. split. { apply IHsz. ltac1:(lia). } { rewrite bind_Some. exists p. split>[|reflexivity]. apply IHp. ltac1:(lia).  }
                    }
                }
                {
                    rewrite bind_Some. exists p. split>[|reflexivity].
                    apply IHp. ltac1:(lia).
                }
                {
                    rewrite bind_Some. exists p1. split.
                    { apply IHp1. ltac1:(lia).
                    } { rewrite bind_Some. exists p2. split>[|reflexivity]. apply IHp2. ltac1:(lia). }  
                }
                { 
destruct a.
            {
            rewrite bind_Some. exists p. split. { apply IHp. ltac1:(lia). } { rewrite bind_Some. exists ao. split>[|reflexivity]. 

induction ao; try reflexivity.
                        {
                        rewrite bind_Some. exists ao. split.
                        {
                            apply IHao. ltac1:(lia).
                        } { rewrite bind_Some. exists b. split>[|reflexivity]. apply IHsz. ltac1:(lia). }
                        }
                        { rewrite bind_Some. exists ao1. split.
                        {
                            apply IHao1. ltac1:(lia).
                        }
                        {
                            rewrite bind_Some. exists ao2. split>[|reflexivity].
                            apply IHao2. ltac1:(lia).
                        }
                        }
}
            }
            {
                rewrite bind_Some. exists p. split.
                { apply IHp. ltac1:(lia). }
                {
                rewrite bind_Some. exists operand. split>[|reflexivity]. apply IHsz. ltac1:(lia).
                }

            }
            }
        {
            destruct a.
            {
            rewrite bind_Some.
            exists ao.
            split.
            { 
induction ao; try reflexivity.
                        {
                        rewrite bind_Some. exists ao. split.
                        {
                            apply IHao. ltac1:(lia).
                        } { rewrite bind_Some. exists b. split>[|reflexivity]. apply IHsz. ltac1:(lia). }
                        }
{
                        rewrite bind_Some. 
                        exists ao1. split. { apply IHao1. ltac1:(lia). } { rewrite bind_Some. exists ao2. split>[|reflexivity]. apply IHao2. ltac1:(lia).  }
                    }
}
            { rewrite bind_Some. exists p2. split. {  apply IHp2. ltac1:(lia). } { rewrite bind_Some. exists p1. split>[|reflexivity]. apply IHp1. ltac1:(lia). }  }
            }
            { rewrite bind_Some. exists p1. split. { apply IHp1. ltac1:(lia). } { rewrite bind_Some. exists operand. split. { apply IHsz. ltac1:(lia). }  { rewrite bind_Some. exists p2. split>[|reflexivity]. apply IHp2. ltac1:(lia). }  }
            }
}
}
}
    Qed.

    #[export]
    Instance BuiltinValue0_countable
        : Countable (BuiltinValue0)
    .
    Proof.
    ltac1:(unshelve(eapply inj_countable
    with
        (g := tree_to_bv)
        (f := bv_to_tree)
    )).
    {
        ltac1:(unshelve(eapply gen_tree_countable)).
        remember (unit+bool+nat+Z+string+symbol)%type as MyT.
        ltac1:(unshelve(eapply @inj_countable with (A := MyT))).
        {
            subst MyT. apply _.
        }
        {
            subst.
            intros bvl. destruct bvl.
            {
                left. left. left. left. left. exact ().
            }
            {
                left. left. left. left. right. exact b.
            }
            {
                left. left. left. right. exact n.
            }
            {
                left. left. right. exact z.
            }
            {
                left. right. exact s.
            }
            {
                right. exact sym.
            }
        }
        {
            subst.
            intros t.
            destruct t as [t1|t2].
            {
                destruct t1 as [t1|t2].
                {
                    destruct t1 as [t1|t2].
                    {
                        destruct t1 as [t1|t2].
                        {
                            destruct t1 as [t1|t2].
                            {
                                apply Some.
                                apply bvl_error.
                            }
                            {
                                apply Some.
                                apply bvl_bool.
                                apply t2.
                            }
                        }
                        {
                            apply Some.
                            apply bvl_nat.
                            apply t2.                                
                        }
                    }
                    {
                        apply Some.
                        apply bvl_Z.
                        apply t2.
                    }
                }
                {

                    apply Some.
                    apply bvl_str.
                    apply t2.
                }
            }
            {
                apply Some.
                apply bvl_sym.
                apply t2.
            }
        }
        {
            subst. apply _.
        }
        {
            subst. abstract(intros x; destruct x; unfold eq_rec_r; simpl; try reflexivity).
        }
    }
    {
        intros x. apply from_to_tree.
    }
    Defined.

End sec.