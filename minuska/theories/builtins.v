From Minuska Require Import
    prelude
    spec_syntax
    notations
.

From Coq Require Import ZArith.

Module empty_builtin.

    Inductive Emptyset : Set := .

    #[export]
    Instance emptyset_eqdec : EqDecision Emptyset.
    Proof.
        intros x y.
        destruct x, y.
    Defined.

    Section sec.

        Context
            {symbol : Set}
            {symbols : Symbols symbol}
        .

        #[export]
        Instance β
            : Builtin := {|
            builtin_value
                := Emptyset ;
            builtin_nullary_function
                := Emptyset ;
            builtin_unary_function
                := Emptyset ;
            builtin_binary_function
                := Emptyset ;
            builtin_nullary_function_interp
                := fun p => match p with end ;
            builtin_unary_function_interp
                := fun p v => match p with end ;
            builtin_binary_function_interp
                := fun p v1 v2 => match p with end ;
        |}.

    End sec.

End empty_builtin.

Module default_builtin.

    Inductive UnaryP : Set := .

    #[export]
    Instance UnaryP_eqdec : EqDecision UnaryP.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Inductive BinaryP : Set := .

    #[export]
    Instance BinaryP_eqdec : EqDecision BinaryP.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Inductive NullaryF : Set :=
    | b_false
    | b_true
    | b_zero
    .

    #[export]
    Instance NullaryF_eqDec : EqDecision NullaryF.
    Proof. ltac1:(solve_decision). Defined.

    Inductive UnaryF : Set :=
    | b_isBuiltin (* 'a -> bool *)
    | b_isError (* 'a -> bool *)
    | b_isBool  (* 'a -> bool *)
    | b_isNat   (* 'a -> bool *)

    | b_neg (* bool -> bool *)

    | b_nat_isZero  (* 'a -> bool *)
    | b_nat_isSucc  (* 'a -> bool *)
    | b_nat_succOf  (* nat -> nat *)
    | b_nat_predOf  (* nat -> nat *)
    .

    #[export]
    Instance UnaryF_eqdec : EqDecision UnaryF.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Inductive BinaryF : Set :=
    | b_eq    (* 'a -> 'b -> bool *)

    | b_and   (* bool -> bool -> bool *)
    | b_or    (* bool -> bool -> bool *)
    | b_iff   (* bool -> bool -> bool *)
    | b_xor   (* bool -> bool -> bool *)

    | b_nat_isLe  (* nat -> nat -> bool *)
    | b_nat_isLt  (* nat -> nat -> bool *)
    | b_nat_plus  (* nat -> nat -> nat *)
    | b_nat_minus (* nat -> nat -> nat *)
    | b_nat_times (* nat -> nat -> nat *)
    | b_nat_div (* nat -> nat -> nat *)

    | b_Z_isLe  (* Z -> Z -> bool *)
    | b_Z_isLt  (* Z -> Z -> bool *)
    | b_Z_plus  (* Z -> Z -> Z *)
    | b_Z_minus (* Z -> Z -> Z *)
    | b_Z_times (* Z -> Z -> Z *)
    | b_Z_div   (* Z -> Z -> Z *)
    .

    #[export]
    Instance BinaryF_eqdec : EqDecision BinaryF.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Section sec.

        Context
            {symbol : Set}
            {symbols : Symbols symbol}
        .

        Inductive BuiltinValue :=
        | bv_error
        | bv_bool (b : bool)
        | bv_nat (n : nat)
        | bv_Z (z : Z)
        | bv_list (m : list (AppliedOperatorOr' symbol BuiltinValue))
        | bv_pmap (m : Pmap (AppliedOperatorOr' symbol BuiltinValue))
        .

        Derive NoConfusion for BuiltinValue.

        Equations BVsize (r : BuiltinValue) : nat :=
            BVsize (bv_list m) := S (my_list_size m);
            BVsize (bv_pmap (PNodes m)) := S (my_pmapne_size m);
            BVsize (bv_pmap (PEmpty)) := 1;
            BVsize (bv_error) := 1 ;
            BVsize (bv_bool _) := 1 ;
            BVsize (bv_nat _) := 1 ;
            BVsize (bv_Z _) := 1 ;
        where my_list_size (l : list (AppliedOperatorOr' symbol BuiltinValue)) : nat :=
            my_list_size nil := 1 ;
            my_list_size (cons (aoo_operand o) xs) := S ((BVsize o) + (my_list_size xs)) ;
            my_list_size (cons (aoo_app ao) xs) := S ((myaosize ao) + (my_list_size xs)) ;
        where my_pmapne_size (m : Pmap_ne (AppliedOperatorOr' symbol BuiltinValue)) : nat :=
            my_pmapne_size (PNode001 n) := S (my_pmapne_size n) ;
            my_pmapne_size (PNode010 (aoo_operand o)) := S (BVsize o);
            my_pmapne_size (PNode010 (aoo_app a)) := S (myaosize a);
            my_pmapne_size (PNode011 (aoo_operand o) n) := S ((BVsize o) + (my_pmapne_size n));
            my_pmapne_size (PNode011 (aoo_app a) n) := S ((myaosize a) + (my_pmapne_size n));
            my_pmapne_size (PNode100 n) := S (my_pmapne_size n) ;
            my_pmapne_size (PNode101 n1 n2) := S ((my_pmapne_size n1) + (my_pmapne_size n2)) ;
            my_pmapne_size (PNode110 n (aoo_operand o)) := S ((BVsize o) + (my_pmapne_size n));
            my_pmapne_size (PNode110 n (aoo_app a)) := S ((myaosize a) + (my_pmapne_size n));
            my_pmapne_size (PNode111 n1 (aoo_app a) n2) := S ((myaosize a) + (my_pmapne_size n1) + (my_pmapne_size n2));
            my_pmapne_size (PNode111 n1 (aoo_operand o) n2) := S ((BVsize o) + (my_pmapne_size n1) + (my_pmapne_size n2));
        where myaosize (ao : AppliedOperator' symbol BuiltinValue) : nat :=
            myaosize (ao_operator _) := 1 ;
            myaosize (ao_app_operand ao' t) := S ((BVsize t) + (myaosize ao')) ;
            myaosize (ao_app_ao ao1 ao2) := S ((myaosize ao1)+(myaosize ao2)) ;
        .

        Lemma BuiltinValue_eqdec_helper_1 (sz : nat):
            ∀ x y : BuiltinValue, BVsize x <= sz ->
                {x = y} + {x ≠ y}
        with BuiltinValue_eqdec_helper_2 (sz : nat):
            ∀ x y : list (AppliedOperatorOr' symbol BuiltinValue), my_list_size x <= sz ->
                {x = y} + {x ≠ y}
        with BuiltinValue_eqdec_helper_3 (sz : nat):
            ∀ x y : (AppliedOperator' symbol BuiltinValue),
                myaosize x <= sz ->
                    {x = y} + {x ≠ y}
        with BuiltinValue_eqdec_helper_4 (sz : nat):
            ∀ x y : Pmap_ne (AppliedOperatorOr' symbol BuiltinValue),
                my_pmapne_size x <= sz ->
                    {x = y} + {x ≠ y}
        .
        Proof.
            {
                intros x y Hsz.
                revert x Hsz y.
                induction sz; intros x Hsz y.
                {
                    destruct x; (ltac1:(simpl in Hsz));
                    try (ltac1:(lia)).
                    destruct m; (ltac1:(simpl in Hsz));
                    try (ltac1:(lia)).
                }
                destruct x.
                {
                    destruct y;
                    try (solve [left; reflexivity]);
                    right; ltac1:(discriminate).
                }
                {
                    destruct y;
                    try (solve [left; reflexivity]);
                    try ltac1:(right; discriminate).
                    destruct (decide (b = b0)).
                    {
                        left. subst. reflexivity.
                    }
                    {
                        right. ltac1:(congruence).
                    }
                }
                {
                    destruct y;
                    try (solve [left; reflexivity]);
                    try ltac1:(right; discriminate).
                    destruct (decide (n = n0)).
                    {
                        left. subst. reflexivity.
                    }
                    {
                        right. ltac1:(congruence).
                    }
                }
                {
                    destruct y;
                    try (solve [left; reflexivity]);
                    try ltac1:(right; discriminate).
                    destruct (decide (z = z0)).
                    {
                        left. subst. reflexivity.
                    }
                    {
                        right. ltac1:(congruence).
                    }
                }
                {
                    ltac1:(simp BVsize in Hsz).
                    assert(Hsz' : my_list_size m <= sz) by (ltac1:(lia)).
                    destruct y;
                    try (solve[ltac1:(right; discriminate)]).

                    assert (IH := BuiltinValue_eqdec_helper_2 sz m m0 Hsz').
                    destruct IH as [IH|IH].
                    {
                        left. subst. reflexivity.
                    }
                    {
                        right. ltac1:(congruence).
                    }
                }
                {
                    {
                        destruct y;
                        try ltac1:(right; discriminate).
                        destruct m,m0;
                        try (solve[ltac1:(right; discriminate)]).
                        {
                            left. reflexivity.
                        }
                        simpl in Hsz.
                        fold my_pmapne_size in *.
                        assert(IH := BuiltinValue_eqdec_helper_4 sz p p0 ltac:(lia)).
                        destruct IH as [IH|IH].
                        {
                            left. subst. reflexivity.
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                }
            }
            {
                clear BuiltinValue_eqdec_helper_2.
                intros x y Hsz.
                revert x Hsz y.
                induction sz; intros x Hsz y.
                {
                    destruct x; (ltac1:(simpl in Hsz)).
                    {
                        ltac1:(lia).
                    }
                    {
                        destruct a; simpl in Hsz; ltac1:(lia).
                    }
                }
                destruct x.
                {
                    destruct y.
                    { left. reflexivity. }
                    { right. ltac1:(discriminate). }
                }
                {
                    destruct y.
                    { right. ltac1:(discriminate). }
                    destruct a,a0.
                    {
                        assert(IH := BuiltinValue_eqdec_helper_3 sz ao ao0).
                        ltac1:(ospecialize (IH _)).
                        {
                            assert(Hsz' := Hsz).
                            ltac1:(unfold my_list_size in Hsz'; fold myaosize in Hsz').
                            ltac1:(lia).
                        }
                        destruct IH as [IH|IH].
                        {
                            specialize (IHsz x).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                ltac1:(rewrite my_list_size_equation_2 in Hsz).
                                ltac1:(lia).
                            }
                            specialize (IHsz y).
                            destruct IHsz as [IHsz|IHsz].
                            {
                                subst. left. reflexivity.
                            }
                            {
                                right. ltac1:(congruence).
                            }
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                    {
                        right. ltac1:(congruence).
                    }
                    {
                        right. ltac1:(congruence).
                    }
                    {
                        assert(IH := BuiltinValue_eqdec_helper_1 sz operand operand0).
                        ltac1:(ospecialize (IH _)).
                        {
                            assert(Hsz' := Hsz).
                            ltac1:(unfold my_list_size in Hsz'; fold myaosize in Hsz').
                            ltac1:(lia).
                        }
                        destruct IH as [IH|IH].
                        {
                            specialize (IHsz x).
                            ltac1:(ospecialize (IHsz _)).
                            {
                                ltac1:(rewrite my_list_size_equation_3 in Hsz).
                                ltac1:(lia).
                            }
                            specialize (IHsz y).
                            destruct IHsz as [IHsz|IHsz].
                            {
                                subst. left. reflexivity.
                            }
                            {
                                right. ltac1:(congruence).
                            }
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                }
            }
            {
                clear BuiltinValue_eqdec_helper_3.
                intros x y Hsz.
                revert x Hsz y.
                induction sz; intros x Hsz y.
                {
                    destruct x; (ltac1:(simp BVsize in Hsz; lia)).
                }
                destruct x.
                {
                    destruct y.
                    {
                        destruct (decide (s = s0)).
                        {
                            subst. left. reflexivity.
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                    {
                        right. ltac1:(discriminate).
                    }
                    {
                        right. ltac1:(discriminate).
                    }
                }
                {
                    destruct y.
                    {
                        right. ltac1:(discriminate).
                    }
                    {
                        ltac1:(unshelve(simpl in Hsz)).
                        specialize (IHsz x ltac:(lia) y).
                        assert(IH2 := BuiltinValue_eqdec_helper_1 sz b b0 ltac:(lia)).
                        destruct IHsz as [IHsz|IHsz], IH2 as [IH2|IH2].
                        {
                            subst. left. reflexivity.
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                    {
                        right. ltac1:(discriminate).
                    }
                }
                {
                    destruct y.
                    {
                        right. ltac1:(discriminate).
                    }
                    {
                        right. ltac1:(discriminate).
                    }
                    {
                        ltac1:(unshelve(simpl in Hsz)).
                        assert (IH1 := IHsz x1 ltac:(lia) y1).
                        assert (IH2 := IHsz x2 ltac:(lia) y2).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                        {
                            subst. left. reflexivity.
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                }
            }
            {
                induction sz; intros x y Hsz.
                {
                    destruct x; simpl in Hsz; try (ltac1:(lia));
                    destruct a; simpl in Hsz; try (ltac1:(lia)).
                }
                destruct x.
                {
                    destruct y; try (solve [right; ltac1:(congruence)]).
                    simpl in Hsz.
                    assert (IH1 := IHsz x y ltac:(lia)).
                    destruct IH1 as [IH1|IH1].
                    {
                        subst; left. reflexivity.
                    }
                    {
                        right. ltac1:(congruence).
                    }
                }
                {
                    destruct y; try (solve [right; ltac1:(congruence)]);
                    destruct a; try (solve [right; ltac1:(congruence)]);
                    destruct a0; try (solve [right; ltac1:(congruence)]);
                    simpl in Hsz; fold myaosize in *.
                    {
                        assert (IH1 := BuiltinValue_eqdec_helper_3 sz ao ao0 ltac:(lia)).
                        destruct IH1 as [IH1|IH1].
                        {
                            subst; left. reflexivity.
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                    {
                        assert (IH1 := BuiltinValue_eqdec_helper_1 sz operand operand0 ltac:(lia)).
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
                    destruct y; try (solve [right; ltac1:(congruence)]);
                    destruct a; try (solve [right; ltac1:(congruence)]);
                    destruct a0; try (solve [right; ltac1:(congruence)]);
                    simpl in Hsz; fold myaosize in *.
                    {
                        assert (IH1 := IHsz x y ltac:(lia)).
                        assert (IH2 := BuiltinValue_eqdec_helper_3 sz ao ao0 ltac:(lia)).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                        {
                            subst; left. reflexivity.
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                    {
                        assert (IH1 := BuiltinValue_eqdec_helper_1 sz operand operand0 ltac:(lia)).
                        assert (IH2 := IHsz x y ltac:(lia)).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                        {
                            subst; left; reflexivity.
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
                {
                    destruct y; try (solve [right; ltac1:(congruence)]).
                    simpl in Hsz.
                    assert (IH1 := IHsz x y ltac:(lia)).
                    destruct IH1 as [IH1|IH1].
                    {
                        subst; left. reflexivity.
                    }
                    {
                        right. ltac1:(congruence).
                    }
                }
                {
                    destruct y; try (solve [right; ltac1:(congruence)]).
                    simpl in Hsz.
                    assert (IH1 := IHsz x1 y1 ltac:(lia)).
                    assert (IH2 := IHsz x2 y2 ltac:(lia)).
                    destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                    {
                        subst; left. reflexivity.
                    }
                    {
                        right. ltac1:(congruence).
                    }
                    {
                        right. ltac1:(congruence).
                    }
                    {
                        right. ltac1:(congruence).
                    }
                }
                {
                    destruct y; try (solve [right; ltac1:(congruence)]);
                    destruct a; try (solve [right; ltac1:(congruence)]);
                    destruct a0; try (solve [right; ltac1:(congruence)]);
                    simpl in Hsz. fold myaosize in *.
                    {
                        assert (IH1 := IHsz x y ltac:(lia)).
                        assert (IH2 := BuiltinValue_eqdec_helper_3 sz ao ao0 ltac:(lia)).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                        {
                            subst; left. reflexivity.
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                    {
                        assert (IH1 := IHsz x y ltac:(lia)).
                        assert (IH2 := BuiltinValue_eqdec_helper_1 sz operand operand0 ltac:(lia)).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                        {
                            subst; left. reflexivity.
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                        {
                            right. ltac1:(congruence).
                        }
                    }
                }
                {
                    destruct y; try (solve [right; ltac1:(congruence)]);
                    destruct a; try (solve [right; ltac1:(congruence)]);
                    destruct a0; try (solve [right; ltac1:(congruence)]);
                    simpl in Hsz; fold myaosize in *.
                    {
                        assert (IH1 := IHsz x1 y1 ltac:(lia)).
                        assert (IH2 := IHsz x2 y2 ltac:(lia)).
                        assert (IH3 := BuiltinValue_eqdec_helper_3 sz ao ao0 ltac:(lia)).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2], IH3 as [IH3|IH3];
                        try (solve [subst; left; reflexivity]);
                        try (solve [right; ltac1:(congruence)]).
                    }
                    {
                        assert (IH1 := IHsz x1 y1 ltac:(lia)).
                        assert (IH2 := IHsz x2 y2 ltac:(lia)).
                        assert (IH3 := BuiltinValue_eqdec_helper_1 sz operand operand0 ltac:(lia)).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2], IH3 as [IH3|IH3];
                        try (solve [subst; left; reflexivity]);
                        try (solve [right; ltac1:(congruence)]).
                    }
                }
            }
        Defined.

        #[local]
        Instance BuiltinValue_eqdec : EqDecision BuiltinValue.
        Proof.
            intros x y.
            unfold Decision.
            eapply BuiltinValue_eqdec_helper_1.
            apply reflexivity.
        Defined.        

        Inductive BVLeaf :=
        | bvl_error
        | bvl_bool (b : bool)
        | bvl_nat (n : nat)
        | bvl_Z (z : Z)
        | bvl_sym (sym : symbol)
        .

        #[local]
        Instance BVLeaf_eqdec : EqDecision BVLeaf.
        Proof.
            ltac1:(solve_decision).
        Defined.

        Derive NoConfusion for BVLeaf.

        Print BuiltinValue. Print gen_tree.

        (*
        Fixpoint bv_to_tree (r : BuiltinValue) : gen_tree BVLeaf :=
        match r with
        | bv_error => GenLeaf bvl_error
        | bv_bool b => GenLeaf (bvl_bool b)
        | bv_nat n => GenLeaf (bvl_nat n)
        | bv_Z z => GenLeaf (bvl_Z z)
        | bv_list l => GenNode 0 (mylist_to_tree l)
        | bv_pmap PEmpty => GenNode 1 nil
        | bv_pmap (PNodes m) => GenNode 2 [(mypm_to_tree m)]
        end
        with mylist_to_tree (l : list (AppliedOperatorOr' symbol BuiltinValue)) : list (gen_tree BVLeaf) :=
        match l with
        | nil                       => nil
        | (cons (aoo_operand o) xs) => cons (GenNode 1 [(bv_to_tree o)]) (mylist_to_tree xs)
        | (cons (aoo_app ao) xs)    => cons (GenNode 0 [(myao_to_tree ao)]) (mylist_to_tree xs)
        end
        with mypm_to_tree (p : Pmap_ne (AppliedOperatorOr' symbol BuiltinValue)) : gen_tree BVLeaf :=
        match p with
        | (PNode001 n)                   => GenNode 1 [(mypm_to_tree n)]
        | (PNode010 (aoo_operand o))     => GenNode 2 [(GenNode 1 [(bv_to_tree o)])]
        | (PNode010 (aoo_app ao))        => GenNode 2 [(GenNode 0 [(myao_to_tree ao)])]
        | (PNode011 (aoo_operand o) y)   => GenNode 3 [(GenNode 1 [(bv_to_tree o)]);(mypm_to_tree y)]
        | (PNode011 (aoo_app ao) y)      => GenNode 3 [(GenNode 0 [(myao_to_tree ao)]);(mypm_to_tree y)]
        | (PNode100 x)                   => GenNode 4 [(mypm_to_tree x)]
        | (PNode101 x y)                 => GenNode 5 [(mypm_to_tree x); (mypm_to_tree y)]
        | (PNode110 x (aoo_operand o))   => GenNode 6 [(mypm_to_tree x); (GenNode 1 [(bv_to_tree o)])]
        | (PNode110 x (aoo_app ao))      => GenNode 6 [(mypm_to_tree x); (GenNode 0 [(myao_to_tree ao)])]
        | (PNode111 x (aoo_operand o) z) => GenNode 7  [(mypm_to_tree x); (GenNode 1 [(bv_to_tree o)]); (mypm_to_tree z)]
        | (PNode111 x (aoo_app ao) z)    => GenNode 7  [(mypm_to_tree x); (GenNode 0 [(myao_to_tree ao)]); (mypm_to_tree z)]
        end
        with myaoo_to_tree (aoo : AppliedOperatorOr' symbol BuiltinValue) : gen_tree BVLeaf :=
        match aoo with
        | aoo_app ao => GenNode 0 [(myao_to_tree ao)]
        | aoo_operand o => GenNode 1 [(bv_to_tree o)]
        end
        with myao_to_tree (ao : AppliedOperator' symbol BuiltinValue) : gen_tree BVLeaf :=
        match ao with
        | ao_operator o => GenLeaf (bvl_sym o)
        | ao_app_operand x y => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
        | ao_app_ao x y => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
        end
        .
        *)
        (*
        Equations tree_to_bv
            (t : gen_tree BVLeaf) : (option BuiltinValue)  :=
            tree_to_bv ((GenNode 1 nil)) := Some (bv_pmap (PEmpty));
            
            tree_to_bv (GenLeaf bvl_error)      := Some (bv_error)  ;
            tree_to_bv (GenLeaf (bvl_bool b))   := Some (bv_bool b) ;
            tree_to_bv (GenLeaf (bvl_nat n))    := Some (bv_nat n) ;
            tree_to_bv (GenLeaf (bvl_Z z))      := Some (bv_Z z) ;
            tree_to_bv (GenNode 0 l)            := (
                l' ← tree_to_mylist l;
                Some (bv_list (l'))
            )
            
            where tree_to_mylist (l' : list (gen_tree BVLeaf)) :
                    (option (list (AppliedOperatorOr' symbol BuiltinValue))) := {
                    tree_to_mylist nil                             := Some nil ;
                    tree_to_mylist (cons (GenNode 1 [(o)]) (xs))   := (
                        o' ← (tree_to_bv o);
                        xs' ← (tree_to_mylist xs);
                        Some (cons (aoo_operand o') xs')
                    );
                    tree_to_mylist (cons (GenNode 0 [(ao)]) (xs))  := (
                        ao' ← (tree_to_myao ao);
                        xs' ← (tree_to_mylist xs);
                        Some (cons (aoo_app ao') xs') 
                    )
                    where tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := {
                        
                        tree_to_myao (GenLeaf (bvl_sym o)) := Some (ao_operator o) ;
                        tree_to_myao (GenNode 0 [(x);(y)]) :=
                            (
                                x' ← (tree_to_myao x);
                                y' ← (tree_to_bv y);
                                Some (ao_app_operand x' y')
                            );
                        tree_to_myao (GenNode 1 [(x);(y)]) := (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_myao y);
                            Some (ao_app_ao x' y')
                         ) ;
                         
                        tree_to_myao _ := None
                    } ;
                    tree_to_mylist _ := None
            } ;
                
            tree_to_bv (GenNode 2 [(m)]) := (
                m' ← (tree_to_mypm m);
                Some (bv_pmap (PNodes m'))
            )
            where tree_to_mypm (p : (gen_tree BVLeaf)) : option (Pmap_ne (AppliedOperatorOr' symbol BuiltinValue)) := {
                tree_to_mypm (GenNode 1 [(n)]) := (
                    n' ← (tree_to_mypm n);
                    Some (PNode001 n')
                );
                tree_to_mypm (GenNode 2 [(GenNode 1 [(o)])])   := (
                    o' ← (tree_to_bv o);
                    Some (PNode010 (aoo_operand o')) 
                );
                tree_to_mypm (GenNode 2 [(GenNode 0 [(ao')])]) := (
                    ao'' ← (tree_to_myao ao');
                    Some (PNode010 (aoo_app ao''))
                )
                where tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := {
                        tree_to_myao (GenLeaf (bvl_sym o)) := Some (ao_operator o) ;
                        tree_to_myao (GenNode 0 [(x);(y)]) :=
                            (
                                x' ← (tree_to_myao x);
                                y' ← (tree_to_bv y);
                                Some (ao_app_operand x' y')
                            );
                        tree_to_myao (GenNode 1 [(x);(y)]) := (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_myao y);
                            Some (ao_app_ao x' y')
                         ) ;
                         
                        tree_to_myao _ := None
                    } ;
                
                tree_to_mypm (GenNode 3 [(GenNode 1 [(o)]);(y')])   := (
                    o' ← (tree_to_bv o);
                    y'' ← (tree_to_mypm y');
                    Some (PNode011 (aoo_operand o') y'')
                );
                tree_to_mypm (GenNode 3 [(GenNode 0 [(ao')]);(y')]) := (
                    ao'' ← (tree_to_myao ao');
                    y'' ← (tree_to_mypm y');
                    Some (PNode011 (aoo_app ao'') y'')
                )
                
                where tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := {
                        tree_to_myao (GenLeaf (bvl_sym o)) := Some (ao_operator o) ;
                        tree_to_myao (GenNode 0 [(x);(y)]) :=
                            (
                                x' ← (tree_to_myao x);
                                y' ← (tree_to_bv y);
                                Some (ao_app_operand x' y')
                            );
                        tree_to_myao (GenNode 1 [(x);(y)]) := (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_myao y);
                            Some (ao_app_ao x' y')
                         ) ;
                         
                        tree_to_myao _ := None
                    } ;
                tree_to_mypm (GenNode 4 [(x')])                     := (
                    x'' ← (tree_to_mypm x');
                    Some (PNode100 x'') 
                );
                tree_to_mypm (GenNode 5 [(x'); (y')])               := (
                    x'' ← (tree_to_mypm x');
                    y'' ← (tree_to_mypm y');
                    Some (PNode101 x'' y'') 
                );
                tree_to_mypm (GenNode 6 [(x'); (GenNode 1 [(o')])]) := (
                    x'' ← (tree_to_mypm x');
                    o'' ← (tree_to_bv o');
                    Some (PNode110 x'' (aoo_operand o''))
                 );
                tree_to_mypm (GenNode 6 [(x'); (GenNode 0 [(ao')])]) := (
                    x'' ← (tree_to_mypm x');
                    ao'' ← (tree_to_myao ao');
                    Some (PNode110 x'' (aoo_app ao''))
                )
                where tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := {
                        tree_to_myao (GenLeaf (bvl_sym o)) := Some (ao_operator o) ;
                        tree_to_myao (GenNode 0 [(x);(y)]) :=
                            (
                                x' ← (tree_to_myao x);
                                y' ← (tree_to_bv y);
                                Some (ao_app_operand x' y')
                            );
                        tree_to_myao (GenNode 1 [(x);(y)]) := (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_myao y);
                            Some (ao_app_ao x' y')
                         ) ;
                        tree_to_myao _ := None
                    } ;
                tree_to_mypm (GenNode 7%nat  [(x'); (GenNode 1 [(o)]); (z')]) := (
                    x'' ← (tree_to_mypm x');
                    o' ← (tree_to_bv o);
                    z'' ← (tree_to_mypm z');
                    Some (PNode111 x'' (aoo_operand o') z'')
                );
                tree_to_mypm (GenNode 7%nat  [(x'); (GenNode 0 [(ao')]); (z')]) := (
                    ao'' ← (tree_to_myao ao');
                    z'' ← (tree_to_mypm z');
                    x'' ← (tree_to_mypm x');
                    Some (PNode111 x'' (aoo_app ao'') z'')
                )
                where tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := {
                        tree_to_myao (GenLeaf (bvl_sym o)) := Some (ao_operator o) ;
                        tree_to_myao (GenNode 0 [(x);(y)]) :=
                            (
                                x' ← (tree_to_myao x);
                                y' ← (tree_to_bv y);
                                Some (ao_app_operand x' y')
                            );
                        tree_to_myao (GenNode 1 [(x);(y)]) := (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_myao y);
                            Some (ao_app_ao x' y')
                         ) ;
                        tree_to_myao _ := None
                    } ;
                tree_to_mypm _ := None
            } ;
            tree_to_bv _ := None
        .
        *)
    
        Fixpoint tree_to_bv
            (t : gen_tree BVLeaf) : (option BuiltinValue)  :=
        match t with
        | ((GenNode 1 nil)) => Some (bv_pmap (PEmpty))
        | (GenLeaf bvl_error)      => Some (bv_error)  
        | (GenLeaf (bvl_bool b))   => Some (bv_bool b) 
        | (GenLeaf (bvl_nat n))    => Some (bv_nat n) 
        | (GenLeaf (bvl_Z z))      => Some (bv_Z z) 
        | (GenNode 0 l)            => (
                let tree_to_mylist := fix tree_to_mylist (l' : list (gen_tree BVLeaf)) :
                    (option (list (AppliedOperatorOr' symbol BuiltinValue))) := (
                    match l' with
                    | nil                             => Some nil
                    | (cons (GenNode 1 [(o)]) (xs))   => (
                        o' ← (tree_to_bv o);
                        xs' ← (tree_to_mylist xs);
                        Some (cons (aoo_operand o') xs')
                    )
                    | (cons (GenNode 0 [(ao)]) (xs)) => (
                        let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := (
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
                let tree_to_mypm := fix tree_to_mypm (p : (gen_tree BVLeaf)) : option (Pmap_ne (AppliedOperatorOr' symbol BuiltinValue)) := (
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
                    let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := (
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
                    let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := (
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
                    let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := (
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
                    let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (AppliedOperator' symbol BuiltinValue) := (
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
            (r : BuiltinValue) : (gen_tree BVLeaf) :=
        match r with
        | (bv_pmap (PEmpty)) => (GenNode 1 nil)
        | (bv_error)         => (GenLeaf bvl_error)
        | (bv_bool b)        => (GenLeaf (bvl_bool b))
        | (bv_nat n)         => (GenLeaf (bvl_nat n))
        | (bv_Z z)           => (GenLeaf (bvl_Z z))
        | (bv_list l)        =>
            let mylist_to_tree := (
                fix mylist_to_tree
                    (l' : list (AppliedOperatorOr' symbol BuiltinValue)) : list (gen_tree BVLeaf) := (
                match l' with
                | nil => nil
                | (cons (aoo_operand o) xs) => cons (GenNode 1 [(bv_to_tree o)]) (mylist_to_tree xs)
                | (cons (aoo_app ao) xs) => (
                    let myao_to_tree := (
                        fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue) : gen_tree BVLeaf := (
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
                fix mypm_to_tree (p : Pmap_ne (AppliedOperatorOr' symbol BuiltinValue)) : gen_tree BVLeaf := (
                match p with
                | (PNode001 n)                     => GenNode 1 [(mypm_to_tree n)]
                | (PNode010 (aoo_operand o))       => GenNode 2 [(GenNode 1 [(bv_to_tree o)])]
                | (PNode010 (aoo_app ao'))         => (
                    let myao_to_tree := (
                        fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue) : gen_tree BVLeaf := (
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
                        fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue) : gen_tree BVLeaf := (
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
                        fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue) : gen_tree BVLeaf := (
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
                        fix myao_to_tree (ao : AppliedOperator' symbol BuiltinValue) : gen_tree BVLeaf := (
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
        


        Definition err
        :=
            @aoo_operand symbol BuiltinValue bv_error
        .

        Definition isBuiltin (bv : BuiltinValue) : BuiltinValue
        :=
            (bv_bool true)
        .

        Definition isError (bv : BuiltinValue) : bool
        :=
            match bv with bv_error => true | _ => false end
        .

        Definition isBool (bv : BuiltinValue) : bool
        :=
            match bv with bv_bool _ => true | _ => false end
        .

        Definition isNat (bv : BuiltinValue) : bool
        :=
            match bv with bv_nat _ => true | _ => false end
        .

        Definition bfmap1
            (f : BuiltinValue -> BuiltinValue)
            (x : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        match x with
        | aoo_operand x' => aoo_operand (f x')
        | _ => err
        end.

        Definition bfmap2
            (f : BuiltinValue -> BuiltinValue -> BuiltinValue)
            (x y : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        match x, y with
        | aoo_operand x', aoo_operand y' => aoo_operand (f x' y')
        | _,_ => err
        end.

        Definition bfmap_bool__bool
            (f : bool -> bool)
            (x : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        bfmap1
            (fun x' =>
            match x' with
            | bv_bool x'' => bv_bool (f x'')
            | _ => bv_error
            end
            )
            x
        .

        Definition bfmap_bool_bool__bool
            (f : bool -> bool -> bool)
            (x y : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        bfmap2
            (fun x' y' =>
            match x', y' with
            | bv_bool x'', bv_bool y'' => bv_bool (f x'' y'')
            | _, _ => bv_error
            end
            )
            x y
        .

        Definition bfmap_nat__nat
            (f : nat -> nat)
            (x : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        bfmap1
            (fun x' =>
            match x' with
            | bv_nat x'' => bv_nat (f x'')
            | _ => bv_error
            end
            )
            x
        .

        Definition bfmap_nat_nat__nat
            (f : nat -> nat -> nat)
            (x y : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        bfmap2
            (fun x' y' =>
            match x', y' with
            | bv_nat x'', bv_nat y'' => bv_nat (f x'' y'')
            | _, _ => bv_error
            end
            )
            x y
        .

        Definition bfmap_nat_nat__bool
            (f : nat -> nat -> bool)
            (x y : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        bfmap2
            (fun x' y' =>
            match x', y' with
            | bv_nat x'', bv_nat y'' => bv_bool (f x'' y'')
            | _, _ => bv_error
            end
            )
            x y
        .

        Definition bfmap_Z_Z__Z
            (f : Z -> Z -> Z)
            (x y : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        bfmap2
            (fun x' y' =>
            match x', y' with
            | bv_Z x'', bv_Z y'' => bv_Z (f x'' y'')
            | _, _ => bv_error
            end
            )
            x y
        .

        Definition bfmap_Z_Z__bool
            (f : Z -> Z -> bool)
            (x y : GroundTerm' symbol BuiltinValue)
            : GroundTerm' symbol BuiltinValue
        :=
        bfmap2
            (fun x' y' =>
            match x', y' with
            | bv_Z x'', bv_Z y'' => bv_bool (f x'' y'')
            | _, _ => bv_error
            end
            )
            x y
        .

        #[export]
        Instance β
            : Builtin
        := {|
            builtin_value
                := BuiltinValue ;

            builtin_nullary_function
                := NullaryF;

            builtin_unary_function
                := UnaryF ;

            builtin_binary_function
                := BinaryF ;

            builtin_nullary_function_interp
                := fun p =>
                match p with
                | b_false => aoo_operand (bv_bool false)
                | b_true => aoo_operand (bv_bool true)
                | b_zero => aoo_operand (bv_nat 0)
                end ;
 
            builtin_unary_function_interp
                := fun p v =>
                match p with
                | b_isBuiltin => bfmap1 isBuiltin v
                | b_isError =>
                    match v with
                    | aoo_operand x => aoo_operand (bv_bool (isError x))
                    | _ => aoo_operand (bv_bool false)
                    end
                | b_isBool =>
                    match v with
                    | aoo_operand x => aoo_operand (bv_bool (isBool x))
                    | _ => aoo_operand (bv_bool false)
                    end
                | b_neg =>
                    bfmap_bool__bool negb v
                | b_isNat =>
                    match v with
                    | aoo_operand x => aoo_operand (bv_bool (isNat x))
                    | _ => aoo_operand (bv_bool false)
                    end
                | b_nat_isZero =>
                    match v with
                    | aoo_operand (bv_nat 0) => aoo_operand (bv_bool true)
                    | _ => aoo_operand (bv_bool false)
                    end
                | b_nat_isSucc =>
                    match v with
                    | aoo_operand (bv_nat (S _)) => aoo_operand (bv_bool true)
                    | _ => aoo_operand (bv_bool false)
                    end
                | b_nat_succOf =>
                    bfmap_nat__nat S v
                | b_nat_predOf =>
                    match v with
                    | aoo_operand (bv_nat (S n)) => (aoo_operand (bv_nat n))
                    | _ => err
                    end
                end;

            builtin_binary_function_interp
                := fun p v1 v2 =>
                match p with
                | b_eq =>
                    aoo_operand (bv_bool (bool_decide (v1 = v2)))
                | b_and =>
                    bfmap_bool_bool__bool andb v1 v2
                | b_or =>
                    bfmap_bool_bool__bool orb v1 v2
                | b_iff =>
                    bfmap_bool_bool__bool eqb v1 v2
                | b_xor =>
                    bfmap_bool_bool__bool xorb v1 v2                    
                | b_nat_isLe =>
                    bfmap_nat_nat__bool Nat.leb v1 v2
                | b_nat_isLt =>
                    bfmap_nat_nat__bool Nat.ltb v1 v2
                | b_nat_plus =>
                    bfmap_nat_nat__nat plus v1 v2
                | b_nat_minus =>
                    bfmap_nat_nat__nat minus v1 v2
                | b_nat_times =>
                    bfmap_nat_nat__nat mult v1 v2
                | b_nat_div =>
                    match v2 with
                    | aoo_operand (bv_nat (0)) => err
                    | _ => bfmap_nat_nat__nat Nat.div v1 v2
                    end
                | b_Z_isLe =>
                    bfmap_Z_Z__bool Z.leb v1 v2
                | b_Z_isLt =>
                    bfmap_Z_Z__bool Z.ltb v1 v2
                | b_Z_plus =>
                    bfmap_Z_Z__Z Z.add v1 v2
                | b_Z_minus =>
                    bfmap_Z_Z__Z Z.sub v1 v2
                | b_Z_times =>
                    bfmap_Z_Z__Z Z.mul v1 v2
                | b_Z_div =>
                match v2 with
                | aoo_operand (bv_Z (0)) => err
                | _ => bfmap_Z_Z__Z Z.div v1 v2
                end
                end ;
        |}.

    End sec.


    Module Notations.
        
        
        Notation "'true'" := (ft_nullary b_true)
            : RuleScope
        .

        Notation "'false'" := (ft_nullary b_false)
            : RuleScope
        .
    
        Notation "b1 '&&' b2" :=
            (ft_binary default_builtin.b_and
                (b1)
                (b2)
            )
            : RuleScope
        .

        Notation "~~ b" :=
            (ft_unary default_builtin.b_neg (b))
        .
        

        Notation "'isNat' t" :=
            (ft_unary
                b_isNat
                t
            )
            (at level 90)
        .

        Notation "'(' x '+Nat' y ')'" :=
            (ft_binary b_nat_plus (x) (y))
        .

        Notation "'(' x '-Nat' y ')'" :=
            (ft_binary b_nat_minus (x) (y))
        .

        Notation "'(' x '*Nat' y ')'" :=
            (ft_binary b_nat_times (x) (y))
        .

        Notation "'(' x '/Nat' y ')'" :=
            (ft_binary b_nat_div (x) (y))
        .

        Notation "'(' x '==Nat' y ')'" :=
            (ft_binary b_eq (x) (y))
        .


        Notation "'(' x '+Z' y ')'" :=
            (ft_binary b_Z_plus (x) (y))
        .

        Notation "'(' x '-Z' y ')'" :=
            (ft_binary b_Z_minus (x) (y))
        .

        Notation "'(' x '*Z' y ')'" :=
            (ft_binary b_Z_times (x) (y))
        .

        Notation "'(' x '/Z' y ')'" :=
            (ft_binary b_Z_div (x) (y))
        .

        Notation "'(' x '==Z' y ')'" :=
            (ft_binary b_eq (x) (y))
        .

    End Notations.

End default_builtin.