From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    lowlang
    notations
    default_static_model
    BuiltinValue
.

From Coq Require Import ZArith Ring.

(* TODO eventually, move this into prelude *)
#[local]
Obligation Tactic := idtac.

Section sec.

    Context
        {symbol : Type}
        {_se : EqDecision symbol}
        {_sc : Countable symbol}
    .

    (* This is an attempt at an alternative definition that avoids lowlang.
        I could not figure out how to implement decision procedure for equality,
        so it is left for future work.
    
    (* TODO make parametric in a user type *)
    Inductive BuiltinValue0 :=
    | bv_error
    | bv_bool (b : bool)
    (* | bv_nat (n : nat) *)
    | bv_Z (z : Z)
    | bv_sym (s : symbol)
    | bv_str (s : string)
    | bv_list (m : list (@TermOver' symbol BuiltinValue0))
    | bv_pmap (m : Pmap (@TermOver' symbol BuiltinValue0))
    .

    Fixpoint BVsize (r : BuiltinValue0) : nat :=
    match r with
    | bv_error => 1
    | bv_bool _ => 1
    | bv_Z _ => 1
    | bv_sym _ => 1
    | bv_str _ => 1
    | bv_list l =>
        let TermBVsize := (fix TermBVsize (t : @TermOver' symbol BuiltinValue0) : nat :=
        match t with
        | t_over m => S (BVsize m)
        | t_term _ l => S (
            (fix helper (l' : list (@TermOver' symbol BuiltinValue0)) : nat :=
            match l' with
            | [] => 1
            | x::xs => S (TermBVsize x + helper xs)
            end
            )l)
        end) in
        S (sum_list_with TermBVsize l)
    | bv_pmap PEmpty => 1
    | bv_pmap (PNodes m) =>
        let TermBVsize := (fix TermBVsize (t : @TermOver' symbol BuiltinValue0) : nat :=
        match t with
        | t_over m => S (BVsize m)
        | t_term _ l => S (
            (fix helper (l' : list (@TermOver' symbol BuiltinValue0)) : nat :=
            match l' with
            | [] => 1
            | x::xs => S (TermBVsize x + helper xs)
            end
            )l)
        end) in
        S ((fix mypmsz (m' : Pmap_ne (@TermOver' symbol BuiltinValue0)) :=
        match m' with
        | PNode001 m'' => S (mypmsz m'')
        | PNode010 m'' => S (TermBVsize m'')
        | PNode011 m1 m2 => S (TermBVsize m1 + mypmsz m2)
        | PNode100 m'' => mypmsz m''
        | PNode101 m1 m2 => S (mypmsz m1 + mypmsz m2)
        | PNode110 m1 m2 => S (mypmsz m1 + TermBVsize m2)
        | PNode111 m1 m2 m3 => S (mypmsz m1 + TermBVsize m2 + mypmsz m3)
        end
        ) m)
    end
    .
    
    *)

    (* TODO make parametric in a user type *)
    Inductive BuiltinValue0 :=
    (* | bv_error *)
    | bv_bool (b : bool)
    (* | bv_nat (n : nat) *)
    | bv_Z (z : Z)
    | bv_sym (s : symbol)
    | bv_str (s : string)
    | bv_list (m : list (Term' symbol BuiltinValue0))
    | bv_pmap (m : Pmap (Term' symbol BuiltinValue0))
    .

    Fixpoint BVsize (r : BuiltinValue0) : nat :=
    match r with
    | bv_list m =>
        let my_list_size := (fix my_list_size (l : list (Term' symbol BuiltinValue0)) : nat :=
        match l with
        | nil => 1
        | (cons (term_operand o) xs) => S ((BVsize o) + (my_list_size xs))
        | (cons (term_preterm ao) xs) =>
            let myaosize := (fix myaosize (ao : PreTerm' symbol BuiltinValue0) : nat :=
            match ao with
            | (pt_operator _) => 1
            | (pt_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
            | (pt_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
            end) in
            S ((myaosize ao) + (my_list_size xs))
        end) in
        S (my_list_size m)
    | bv_pmap (PNodes m) =>
        let my_pmapne_size := (fix my_pmapne_size (m : Pmap_ne (Term' symbol BuiltinValue0)) : nat :=
    match m with
    | (PNode001 n) => S (my_pmapne_size n)
    | (PNode010 (term_operand o)) => S (BVsize o)
    | (PNode010 (term_preterm a)) =>
        let myaosize := (fix myaosize (ao : PreTerm' symbol BuiltinValue0) : nat :=
        match ao with
        | (pt_operator _) => 1
        | (pt_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
        | (pt_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
        end) in
        S (myaosize a)
    | (PNode011 (term_operand o) n) => S ((BVsize o) + (my_pmapne_size n))
    | (PNode011 (term_preterm a) n) =>
        let myaosize := (fix myaosize (ao : PreTerm' symbol BuiltinValue0) : nat :=
        match ao with
        | (pt_operator _) => 1
        | (pt_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
        | (pt_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
        end) in
        S ((myaosize a) + (my_pmapne_size n))
    | (PNode100 n) => S (my_pmapne_size n)
    | (PNode101 n1 n2) => S ((my_pmapne_size n1) + (my_pmapne_size n2))
    | (PNode110 n (term_operand o)) => S ((BVsize o) + (my_pmapne_size n))
    | (PNode110 n (term_preterm a)) =>
        let myaosize := (fix myaosize (ao : PreTerm' symbol BuiltinValue0) : nat :=
        match ao with
        | (pt_operator _) => 1
        | (pt_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
        | (pt_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
        end) in
        S ((myaosize a) + (my_pmapne_size n))
    | (PNode111 n1 (term_preterm a) n2) =>
        let myaosize := (fix myaosize (ao : PreTerm' symbol BuiltinValue0) : nat :=
        match ao with
        | (pt_operator _) => 1
        | (pt_app_operand ao' t) => S ((BVsize t) + (myaosize ao'))
        | (pt_app_ao ao1 ao2) => S ((myaosize ao1)+(myaosize ao2))
        end) in
        S ((myaosize a) + (my_pmapne_size n1) + (my_pmapne_size n2))
    | (PNode111 n1 (term_operand o) n2) => S ((BVsize o) + (my_pmapne_size n1) + (my_pmapne_size n2))
    end) in
        S (my_pmapne_size m)
    | bv_pmap (PEmpty) => 1
    (* | bv_error => 1 *)
    | bv_bool _ => 1
    (* | bv_nat _ => 1 *)
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
            (*abstract( *)destruct x; simpl in Hsz; try ltac1:(lia);
            destruct m; simpl in Hsz; try ltac1:(lia) (* ) *) .
        }
        {
            destruct x.
            (* {
                destruct y;
                try (solve [left; reflexivity]);
                right; ltac1:(discriminate).
            } *)
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (b = b0)).
                {
                    left. abstract(subst; reflexivity).
                }
                {
                    right; ltac1:(abstract congruence).
                }
            }
            (*
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (n = n0)).
                {
                    left. abstract(subst; reflexivity).
                }
                {
                    right; ltac1:(abstract congruence).
                }
            }
            *)
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (z = z0)).
                {
                    left. abstract(subst; reflexivity).
                }
                {
                    right; ltac1:(abstract congruence).
                }
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (s = s0)).
                {
                    left. abstract(subst; reflexivity).
                }
                {
                    right; ltac1:(abstract congruence).
                }
            }
            {
                destruct y;
                try (solve [left; reflexivity]);
                try (solve [right;ltac1:(discriminate)]).
                destruct (decide (s = s0)).
                {
                    left. abstract(subst; reflexivity).
                }
                {
                    right; ltac1:(abstract congruence).
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
                        right. ltac1:(abstract congruence).
                    }
                }
                {
                    destruct m0 as [|a0].
                    {
                        right; ltac1:(abstract congruence).
                    }
                    {
                        destruct a, a0.
                        {
                            assert (IH1 := IHm ltac:(abstract(simpl in *; lia)) m0).
                            destruct IH1 as [IH1|IH1].
                            {
                                injection IH1 as IH1'. clear IH1.
                                revert ao0.
                                induction ao; intros ao0.
                                {
                                    destruct ao0.
                                    {
                                        destruct (decide (s = s0)).
                                        {
                                            left. abstract(subst; reflexivity).
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        assert (IH1 := IHao ltac:(abstract(simpl in *; lia)) ao0).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            injection IH1 as IH1''. clear IH1.
                                            assert(IH2 := IHsz b ltac:(abstract(simpl in *; lia)) b0).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                subst.
                                                left; reflexivity.
                                            }
                                            {
                                                right; ltac1:(abstract congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        assert (IH1 := IHao1 ltac:(abstract(simpl in *; lia)) ao0_1).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            injection IH1 as IH1''. clear IH1.
                                            assert(IH2 := IHao2 ltac:(abstract(simpl in *; lia)) ao0_2).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                left; abstract(inversion IH2; subst; clear IH2; reflexivity).
                                            }
                                            {
                                                right; ltac1:(abstract congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                }
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                        }
                        {
                            right; ltac1:(abstract congruence).
                        }
                        {
                            right; ltac1:(abstract congruence).
                        }
                        {
                            specialize (IHsz operand ltac:(abstract(simpl in *; lia)) operand0).
                            specialize (IHm ltac:(abstract(simpl in *; lia)) m0).

                            destruct IHsz as [IHsz|IHsz], IHm as [IHm|IHm].
                            {
                                left. abstract(inversion IHm; subst; reflexivity).
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                            {
                                right; ltac1:(abstract congruence).
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
                    right; ltac1:(abstract congruence).
                }
                {
                    right; ltac1:(abstract congruence).
                }
                {
                    revert p0.
                    induction p; intros p0.
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).
                        assert (IH1 := IHp ltac:(abstract(simpl in *; lia)) p0).
                        destruct IH1 as [IH1|IH1].
                        {
                            left; abstract(inversion IH1; subst; reflexivity).
                        }
                        {
                            right; ltac1:(abstract congruence).
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        destruct a,t.
                        {
                            revert ao0.
                            induction ao; intros ao0.
                            {
                                destruct ao0.
                                {
                                    destruct (decide (s = s0)).
                                    {
                                        left. abstract(subst; reflexivity).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    right; ltac1:(abstract congruence).
                                }
                                {
                                    right; ltac1:(abstract congruence).
                                }
                            }
                            {
                                destruct ao0.
                                {
                                    right; ltac1:(abstract congruence).
                                }
                                {
                                    assert (IH1 := IHao ltac:(abstract(simpl in *; lia)) ao0).
                                    destruct IH1 as [IH1|IH1].
                                    {
                                        injection IH1 as IH1''. clear IH1.
                                        assert(IH2 := IHsz b ltac:(abstract(simpl in *; lia)) b0).
                                        destruct IH2 as [IH2|IH2].
                                        {
                                            subst.
                                            left; reflexivity.
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    right; ltac1:(abstract congruence).
                                }
                            }
                            {
                                destruct ao0.
                                {
                                    right; ltac1:(abstract congruence).
                                }
                                {
                                    right; ltac1:(abstract congruence).
                                }
                                {
                                    assert (IH1 := IHao1 ltac:(abstract(simpl in *; lia)) ao0_1).
                                    destruct IH1 as [IH1|IH1].
                                    {
                                        injection IH1 as IH1''. clear IH1.
                                        assert(IH2 := IHao2 ltac:(abstract(simpl in *; lia)) ao0_2).
                                        destruct IH2 as [IH2|IH2].
                                        {
                                            left; abstract(inversion IH2; subst; clear IH2; reflexivity).
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                            }
                        }
                        {
                            right; ltac1:(abstract congruence).
                        }
                        {
                            right; ltac1:(abstract congruence).
                        }
                        {
                            assert (IH1 := IHsz operand ltac:(abstract(simpl in *; lia)) operand0).
                            destruct IH1 as [IH1|IH1].
                            {
                                left; abstract(subst; reflexivity).
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(abstract congruence)]).

                        destruct a,t.
                        {

                            assert (IH1 := IHp ltac:(abstract(simpl in *; lia)) p0).
                            destruct IH1 as [IH1|IH1].
                            {
                                injection IH1 as IH1''. clear IH1.
                                revert ao0.
                                induction ao; intros ao0.
                                {
                                    destruct ao0.
                                    {
                                        destruct (decide (s = s0)).
                                        {
                                            left. abstract(subst; reflexivity).
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        assert (IH1 := IHao ltac:(abstract(simpl in *; lia)) ao0).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            injection IH1 as IH1'''. clear IH1.
                                            assert(IH2 := IHsz b ltac:(abstract(simpl in *; lia)) b0).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                left; abstract(subst; reflexivity).
                                            }
                                            {
                                                right; ltac1:(abstract congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        assert (IH1 := IHao1 ltac:(abstract(simpl in *; lia)) ao0_1).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            injection IH1 as IH1'''. clear IH1.
                                            assert(IH2 := IHao2 ltac:(abstract(simpl in *; lia)) ao0_2).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                left; abstract(inversion IH2; subst; clear IH2; reflexivity).
                                            }
                                            {
                                                right; ltac1:(abstract congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                }
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                            
                        }
                        {
                            right; ltac1:(abstract congruence).
                        }
                        {
                            right; ltac1:(abstract congruence).
                        }
                        {
                            assert (IH1 := IHsz operand ltac:(abstract(simpl in *; lia)) operand0).
                            destruct IH1 as [IH1|IH1].
                            {
                                subst.

                                assert (IH2 := IHp ltac:(abstract(simpl in *; lia)) p0).
                                destruct IH2 as [IH2|IH2].
                                {
                                    left; abstract(inversion IH2; subst; clear IH2; reflexivity).
                                }
                                {
                                    right; ltac1:(abstract congruence).
                                }
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        assert (IH1 := IHp ltac:(abstract(simpl in *; lia)) p0).
                        destruct IH1 as [IH1|IH1].
                        {
                            
                            left. abstract(inversion IH1; subst; clear IH1; reflexivity).
                        }
                        {
                            right; ltac1:(abstract congruence).
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        assert (IH1 := IHp1 ltac:(abstract(simpl in *; lia)) p0_1).
                        assert (IH2 := IHp2 ltac:(abstract(simpl in *; lia)) p0_2).
                        destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                        {
                            left. abstract (inversion IH1; subst; clear IH1; inversion IH2; subst; clear IH2; reflexivity).
                        }
                        {
                            right; ltac1:(abstract(congruence)).
                        }
                        {
                            right; ltac1:(abstract(congruence)).
                        }
                        {
                            right; ltac1:(abstract(congruence)).
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        destruct a,t;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(abstract congruence)]).

                        {
                            assert (IH1 := IHp ltac:(abstract(simpl in *; lia)) p0).
                            destruct IH1 as [IH1|IH1].
                            {
                                injection IH1 as IH1'''. clear IH1.

                                revert ao0.
                                induction ao; intros ao0.
                                {
                                    destruct ao0.
                                    {
                                        destruct (decide (s = s0)).
                                        {
                                            left. abstract(subst; reflexivity).
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        assert (IH1 := IHao ltac:(abstract(simpl in *; lia)) ao0).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            injection IH1 as IH1''. clear IH1.
                                            assert(IH2 := IHsz b ltac:(abstract(simpl in *; lia)) b0).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                left; abstract(subst; reflexivity).
                                            }
                                            {
                                                right; ltac1:(abstract congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        assert (IH1 := IHao1 ltac:(abstract(simpl in *; lia)) ao0_1).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            injection IH1 as IH1''''. clear IH1.
                                            assert(IH2 := IHao2 ltac:(abstract(simpl in *; lia)) ao0_2).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                left; abstract(inversion IH2; subst; clear IH2; reflexivity).
                                            }
                                            {
                                                right; ltac1:(abstract congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                }
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                        }
                        {
                            assert (IH1 := IHsz operand ltac:(abstract(simpl in *; lia)) operand0).
                            destruct IH1 as [IH1|IH1].
                            {
                                subst.
                                assert (IH1 := IHp ltac:(abstract(simpl in *; lia)) p0).
                                destruct IH1 as [IH1|IH1].
                                {
                                    left. abstract(inversion IH1; subst; clear IH1; reflexivity).
                                }
                                {
                                    right; ltac1:(abstract congruence).
                                }
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                        }
                    }
                    {
                        destruct p0;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(discriminate)]).

                        destruct a,t;
                        try (solve [left; reflexivity]);
                        try (solve [right;ltac1:(abstract congruence)]).

                        {
                            assert (IH1 := IHp1 ltac:(abstract(simpl in *; lia)) p0_1).
                            assert (IH2 := IHp2 ltac:(abstract(simpl in *; lia)) p0_2).
                            destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                            {
                                injection IH1 as IH1'''. clear IH1.
                                injection IH2 as IH2'''. clear IH2.
                                
                                revert ao0.
                                induction ao; intros ao0.
                                {
                                    destruct ao0.
                                    {
                                        destruct (decide (s = s0)).
                                        {
                                            left. abstract(subst; reflexivity).
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        assert (IH1 := IHao ltac:(abstract(simpl in *; lia)) ao0).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            injection IH1 as IH1''''. clear IH1.
                                            assert(IH2 := IHsz b ltac:(abstract(simpl in *; lia)) b0).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                left; abstract(subst; reflexivity).
                                            }
                                            {
                                                right; ltac1:(abstract congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                }
                                {
                                    destruct ao0.
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        right; ltac1:(abstract congruence).
                                    }
                                    {
                                        assert (IH1 := IHao1 ltac:(abstract(simpl in *; lia)) ao0_1).
                                        destruct IH1 as [IH1|IH1].
                                        {
                                            injection IH1 as IH1''''. clear IH1.
                                            assert(IH2 := IHao2 ltac:(abstract(simpl in *; lia)) ao0_2).
                                            destruct IH2 as [IH2|IH2].
                                            {
                                                left; abstract(inversion IH2; subst; clear IH2; reflexivity).
                                            }
                                            {
                                                right; ltac1:(abstract congruence).
                                            }
                                        }
                                        {
                                            right; ltac1:(abstract congruence).
                                        }
                                    }
                                }

                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                        }
                        {
                            assert (IH1 := IHp1 ltac:(abstract(simpl in *; lia)) p0_1).
                            assert (IH2 := IHp2 ltac:(abstract(simpl in *; lia)) p0_2).
                            assert (IH3 := IHsz operand ltac:(abstract(simpl in *; lia)) operand0).

                            destruct IH1 as [IH1|IH1], IH2 as [IH2|IH2].
                            {
                                injection IH1 as IH1'''. clear IH1.
                                injection IH2 as IH2'''. clear IH2.
                                destruct IH3 as [IH3|IH3].
                                {
                                    left. abstract(subst; reflexivity).
                                }
                                {
                                    right; ltac1:(abstract congruence).
                                }
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                            {
                                right; ltac1:(abstract congruence).
                            }
                        }
                    }
                }
            }

        }
    Defined.

    (* Print BuiltinValue0_eqdec_helper_0. *)

    #[export]
    Instance BuiltinValue0_eqdec : EqDecision BuiltinValue0.
    Proof.
        intros x y.
        unfold Decision.
        eapply BuiltinValue0_eqdec_helper_0.
        abstract(apply reflexivity).
    Defined.

    Inductive BVLeaf :=
    (* | bvl_error *)
    | bvl_bool (b : bool)
    (* | bvl_nat (n : nat) *)
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
    (* | (GenLeaf bvl_error)      => Some (bv_error)   *)
    | (GenLeaf (bvl_bool b))   => Some (bv_bool b)
    (* | (GenLeaf (bvl_nat n))    => Some (bv_nat n)  *)
    | (GenLeaf (bvl_Z z))      => Some (bv_Z z) 
    | (GenLeaf (bvl_str s))      => Some (bv_str s) 
    | (GenLeaf (bvl_sym s))      => Some (bv_sym s) 
    | (GenNode 0 l)            => (
            let tree_to_mylist := fix tree_to_mylist (l' : list (gen_tree BVLeaf)) :
                (option (list (Term' symbol BuiltinValue0))) := (
                match l' with
                | nil                             => Some nil
                | (cons (GenNode 1 [(o)]) (xs))   => (
                    o' ← (tree_to_bv o);
                    xs' ← (tree_to_mylist xs);
                    Some (cons (term_operand o') xs')
                )
                | (cons (GenNode 0 [(ao)]) (xs)) => (
                    let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (PreTerm' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (pt_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (pt_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (pt_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                    ao' ← (tree_to_myao ao);
                    xs' ← (tree_to_mylist xs);
                    Some (cons (term_preterm ao') xs') 
                )
                | _ => None
                end
            ) in
            l' ← tree_to_mylist l;
            Some (bv_list (l'))
        )
    | (GenNode 2 [(m)]) => (
            let tree_to_mypm := fix tree_to_mypm (p : (gen_tree BVLeaf)) : option (Pmap_ne (Term' symbol BuiltinValue0)) := (
            match p with
            | (GenNode 1 [(n)]) => (
                n' ← (tree_to_mypm n);
                Some (PNode001 n')
            )
            | (GenNode 2 [(GenNode 1 [(o)])]) => (
                o' ← (tree_to_bv o);
                Some (PNode010 (term_operand o')) 
            )
            | (GenNode 2 [(GenNode 0 [(ao')])]) => (
                let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (PreTerm' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (pt_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (pt_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (pt_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                ao'' ← (tree_to_myao ao');
                Some (PNode010 (term_preterm ao''))
            )
            
            | (GenNode 3 [(GenNode 1 [(o)]);(y')])  => (
                o' ← (tree_to_bv o);
                y'' ← (tree_to_mypm y');
                Some (PNode011 (term_operand o') y'')
            )
            | (GenNode 3 [(GenNode 0 [(ao')]);(y')]) => (
                let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (PreTerm' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (pt_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (pt_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (pt_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                ao'' ← (tree_to_myao ao');
                y'' ← (tree_to_mypm y');
                Some (PNode011 (term_preterm ao'') y'')
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
                Some (PNode110 x'' (term_operand o''))
                )
            | (GenNode 6 [(x'); (GenNode 0 [(ao')])]) => (
                let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (PreTerm' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (pt_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (pt_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (pt_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                x'' ← (tree_to_mypm x');
                ao'' ← (tree_to_myao ao');
                Some (PNode110 x'' (term_preterm ao''))
            )
            | (GenNode 7%nat  [(x'); (GenNode 1 [(o)]); (z')]) => (
                x'' ← (tree_to_mypm x');
                o' ← (tree_to_bv o);
                z'' ← (tree_to_mypm z');
                Some (PNode111 x'' (term_operand o') z'')
            )
            | (GenNode 7%nat  [(x'); (GenNode 0 [(ao')]); (z')]) => (
                let tree_to_myao := fix tree_to_myao (t : gen_tree BVLeaf) : option (PreTerm' symbol BuiltinValue0) := (
                    match t with
                    | (GenLeaf (bvl_sym o)) => Some (pt_operator o)
                    |  (GenNode 0 [(x);(y)]) =>
                        (
                            x' ← (tree_to_myao x);
                            y' ← (tree_to_bv y);
                            Some (pt_app_operand x' y')
                        )
                    |  (GenNode 1 [(x);(y)]) => (
                        x' ← (tree_to_myao x);
                        y' ← (tree_to_myao y);
                        Some (pt_app_ao x' y')
                        )
                        
                    |  _ => None
                    end
                    ) in
                ao'' ← (tree_to_myao ao');
                z'' ← (tree_to_mypm z');
                x'' ← (tree_to_mypm x');
                Some (PNode111 x'' (term_preterm ao'') z'')
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
    (* | (bv_error)         => (GenLeaf bvl_error) *)
    | (bv_bool b)        => (GenLeaf (bvl_bool b))
    (* | (bv_nat n)         => (GenLeaf (bvl_nat n)) *)
    | (bv_Z z)           => (GenLeaf (bvl_Z z))
    | (bv_sym s)           => (GenLeaf (bvl_sym s))
    | (bv_str s)           => (GenLeaf (bvl_str s))
    | (bv_list l)        =>
        let mylist_to_tree := (
            fix mylist_to_tree
                (l' : list (Term' symbol BuiltinValue0)) : list (gen_tree BVLeaf) := (
            match l' with
            | nil => nil
            | (cons (term_operand o) xs) => cons (GenNode 1 [(bv_to_tree o)]) (mylist_to_tree xs)
            | (cons (term_preterm ao) xs) => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : PreTerm' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (pt_operator o) => GenLeaf (bvl_sym o)
                    | (pt_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (pt_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
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
            fix mypm_to_tree (p : Pmap_ne (Term' symbol BuiltinValue0)) : gen_tree BVLeaf := (
            match p with
            | (PNode001 n)                     => GenNode 1 [(mypm_to_tree n)]
            | (PNode010 (term_operand o))       => GenNode 2 [(GenNode 1 [(bv_to_tree o)])]
            | (PNode010 (term_preterm ao'))         => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : PreTerm' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (pt_operator o) => GenLeaf (bvl_sym o)
                    | (pt_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (pt_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
                    end
                    )
                ) in
                GenNode 2 [(GenNode 0 [(myao_to_tree ao')])]
            )
            | (PNode011 (term_operand o) y')    => GenNode 3 [(GenNode 1 [(bv_to_tree o)]);(mypm_to_tree y')]
            | (PNode011 (term_preterm ao') y')      => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : PreTerm' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (pt_operator o) => GenLeaf (bvl_sym o)
                    | (pt_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (pt_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
                    end
                    )
                ) in
                GenNode 3 [(GenNode 0 [(myao_to_tree ao')]);(mypm_to_tree y')]
            )
            | (PNode100 x')                    => GenNode 4 [(mypm_to_tree x')]
            | (PNode101 x' y')                 => GenNode 5 [(mypm_to_tree x'); (mypm_to_tree y')]
            | (PNode110 x' (term_operand o'))   => GenNode 6 [(mypm_to_tree x'); (GenNode 1 [(bv_to_tree o')])]
            | (PNode110 x' (term_preterm ao'))      => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : PreTerm' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (pt_operator o) => GenLeaf (bvl_sym o)
                    | (pt_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (pt_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
                    end
                    )
                ) in
                GenNode 6 [(mypm_to_tree x'); (GenNode 0 [(myao_to_tree ao')])]
            )
            | (PNode111 x' (term_operand o) z') => GenNode 7%nat  [(mypm_to_tree x'); (GenNode 1 [(bv_to_tree o)]); (mypm_to_tree z')]
            | (PNode111 x' (term_preterm ao') z')   => (
                let myao_to_tree := (
                    fix myao_to_tree (ao : PreTerm' symbol BuiltinValue0) : gen_tree BVLeaf := (
                    match ao with
                    | (pt_operator o) => GenLeaf (bvl_sym o)
                    | (pt_app_operand x y) => GenNode 0 [(myao_to_tree x);(bv_to_tree y)]
                    | (pt_app_ao x y) => GenNode 1 [(myao_to_tree x);(myao_to_tree y)]
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
                    ltac1:(specialize (IHm ltac:(abstract(simpl in *; lia)))).
                    simpl in IHm.
                    rewrite bind_Some in IHm.
                    destruct IHm as [x [IHm1 IHm2]].
                    injection IHm2 as IHm2'. clear IHm2.  
                    induction ao.
                    {
                        simpl.
                        rewrite bind_Some.
                        exists (term_preterm (pt_operator s) :: m).
                        split>[|reflexivity].
                        rewrite bind_Some.
                        exists m.
                        split>[|reflexivity].
                        subst.
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
                        subst.
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
                        exists (term_preterm (pt_app_operand ao b) :: m).
                        split>[|reflexivity].
                        

                        rewrite bind_Some.
                        exists (pt_app_operand ao b).
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
                        exists (term_preterm (pt_app_ao ao1 ao2) :: m).
                        split>[|reflexivity].
                        rewrite bind_Some.
                        exists ((pt_app_ao ao1 ao2)).

                        simpl in IHao1.
                        ltac1:(ospecialize (IHao1 _)).
                        {
                            simpl in Hr. ltac1:(lia).
                        }
                        rewrite bind_Some in IHao1.
                        subst.
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
                    exists ((term_operand operand :: m)).
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
        remember ((*unit+*)bool+(*nat+*)Z+string+symbol)%type as MyT.
        ltac1:(unshelve(eapply @inj_countable with (A := MyT))).
        {
            subst MyT. apply _.
        }
        {
            subst.
            intros bvl. destruct bvl.
            {
                left. left. left. exact b.
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
                        (* destruct t1 as [t1|t2].
                        {
                            apply Some.
                            apply bvl_error.
                        } *)
                        {
                            apply Some.
                            apply bvl_bool.
                            apply t1.
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

Inductive FunctionSymbol : Set :=
| b_zero              (* Z *)
| b_list_empty        (* list *)
| b_map_empty         (* map *)
| b_map_size          (* map -> Z *)
| b_Z_plus            (* Z -> Z -> Z *)
| b_Z_minus           (* Z -> Z -> Z *)
| b_Z_times           (* Z -> Z -> Z *)
| b_Z_div             (* Z -> Z -> Z *)
| b_Z_isLe                 (* Z -> Z -> bool *)
| b_Z_isLt                 (* Z -> Z -> bool *)
| b_Z_isGe                 (* Z -> Z -> bool *)
| b_Z_isGt                 (* Z -> Z -> bool *)
| b_Z_eq                   (* Z -> Z -> bool *)
| b_Z_neq                  (* Z -> Z -> bool *)
| b_bool_neg          (* bool -> bool *)
| b_map_lookup        (* map -> 'a -> 'b *)
| b_map_update        (* map -> 'a -> 'b -> map  *)
.

#[export]
Instance FunctionSymbol_eqDec : EqDecision FunctionSymbol.
Proof. ltac1:(solve_decision). Defined.

#[export]
Program Instance FunctionSymbol_fin : Finite FunctionSymbol := {|
    enum := [
        b_zero
        ; b_list_empty
        ; b_map_empty 
        ; b_map_size
        ; b_Z_plus
        ; b_Z_minus
        ; b_Z_times
        ; b_Z_div
        ; b_Z_isLe
        ; b_Z_isLt
        ; b_Z_isGe
        ; b_Z_isGt
        ; b_Z_eq
        ; b_Z_neq
        ; b_bool_neg  
        ; b_map_lookup
        ; b_map_update
    ]
|}.
Next Obligation.
    (* This is probably not the fastest way but it works. *)
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    intros x; destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.

Inductive PredicateSymbol : Set :=
| b_isBuiltin              (* 'a -> Prop *)
| b_isNotBuiltin           (* 'a -> Prop *)
(*| b_isError                (* 'a -> Prop *)*)
(*| b_isNotError             (* 'a -> Prop *)*)
| b_isSymbol               (* 'a -> Prop *)
| b_isNotSymbol            (* 'a -> Prop *)
| b_isZ                    (* 'a -> Prop *)
| b_isNotZ                 (* 'a -> Prop *)
| b_isBool                    (* 'a -> Prop *)
| b_isNotBool                    (* 'a -> Prop *)
| b_isString               (* 'a -> Prop *)
| b_isNotString            (* 'a -> Prop *)
| b_isList                 (* 'a -> Prop *)
| b_isNotList              (* 'a -> Prop *)
| b_isMap                  (* 'a -> Prop *)
| b_isNotMap               (* 'a -> Prop *)
| b_bool_is_true      (* bool -> Prop *)
| b_bool_is_false      (* bool -> Prop *)
| b_term_eq                (* term -> term -> Prop *)
| b_map_hasKey             (* map -> 'a -> Prop *)
| b_is_applied_symbol      (* string -> 'a -> Prop *)
| b_is_not_applied_symbol  (* string -> 'a -> Prop *)
| b_have_same_symbol       (* term -> term -> Prop *)
| b_have_different_symbols   (* term -> term -> Prop *)
.

#[export]
Instance PredicateSymbol_eqDec : EqDecision PredicateSymbol.
Proof. ltac1:(solve_decision). Defined.


#[export]
Program Instance PredicateSymbol_fin : Finite PredicateSymbol := {|
    enum := [
        b_isBuiltin              ;
        b_isNotBuiltin           ;
        (* b_isError                ;
        b_isNotError             ; *)
        b_isSymbol               ;
        b_isNotSymbol            ;
        b_isZ                    ;
        b_isNotZ                 ;
        b_isBool                 ;
        b_isNotBool              ;
        b_isString               ;
        b_isNotString            ;
        b_isList                 ;
        b_isNotList              ;
        b_isMap                  ;
        b_isNotMap               ;
        b_bool_is_true           ;
        b_bool_is_false          ;
        b_term_eq                ;
        b_map_hasKey             ;
        b_is_applied_symbol      ;
        b_is_not_applied_symbol  ;
        b_have_same_symbol       ;
        b_have_different_symbols
    ]
|}.
Next Obligation.
    (* This is probably not the fastest way but it works. *)
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    intros x; destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.

Section sec2.

    Context
        {symbol : Type}
        {symbols : Symbols symbol}
    .

    Definition BuiltinValue := @BuiltinValue0 symbol.

    Definition impl_isZ (bv : BuiltinValue) : bool
    :=
        match bv with bv_Z _ => true | _ => false end
    .

    Definition impl_isString (bv : BuiltinValue) : bool
    :=
        match bv with bv_str _ => true | _ => false end
    .

    Definition impl_isBool (bv : BuiltinValue) : bool
    :=
        match bv with bv_bool _ => true | _ => false end
    .

    Definition impl_isList (bv : BuiltinValue) : bool
    :=
        match bv with bv_list _ => true | _ => false end
    .

    Definition impl_isMap (bv : BuiltinValue) : bool
    :=
        match bv with bv_pmap _ => true | _ => false end
    .

    Definition bfmap1
        (f : BuiltinValue -> option BuiltinValue)
        (x : @TermOver' symbol BuiltinValue)
        : option (@TermOver' symbol BuiltinValue)
    :=
    match x with
    | t_over x' => t_over <$> (f x')
    | _ => None
    end.

    Definition bfmap2
        (f : BuiltinValue -> BuiltinValue -> option BuiltinValue)
        (x y : @TermOver' symbol BuiltinValue)
        : option (@TermOver' symbol BuiltinValue)
    :=
    match x, y with
    | t_over x', t_over y' => (t_over <$> (f x' y'))
    | _,_ => None
    end.

    Definition bfmap2P
        (f : BuiltinValue -> BuiltinValue -> bool)
        (x y : @TermOver' symbol BuiltinValue)
        : bool
    :=
    match x, y with
    | t_over x', t_over y' => f x' y'
    | _,_ => false
    end.

    Definition bfmap_Z_Z__Z
        (f : Z -> Z -> Z)
        (x y : @TermOver' symbol BuiltinValue)
        : option (@TermOver' symbol BuiltinValue)
    :=
    bfmap2
        (fun x' y' =>
        match x', y' with
        | bv_Z x'', bv_Z y'' => Some (bv_Z (f x'' y''))
        | _, _ => None
        end
        )
        x y
    .

    Definition bfmap_Z_Z__Prop
        (f : Z -> Z -> bool)
        (x y : @TermOver' symbol BuiltinValue)
        : bool
    :=
    bfmap2P
        (fun x' y' =>
        match x', y' with
        | bv_Z x'', bv_Z y'' => f x'' y''
        | _, _ => false
        end
        )
        x y
    .

    Definition bfmap_Z_Z__bool
        (f : Z -> Z -> bool)
        (x y : @TermOver' symbol BuiltinValue)
        : option (@TermOver' symbol BuiltinValue)
    :=
    bfmap2
        (fun x' y' =>
        match x', y' with
        | bv_Z x'', bv_Z y'' => Some (bv_bool (f x'' y''))
        | _, _ => Some (bv_bool false)
        end
        )
        x y
    .

    Definition my_encode := ((@encode (@TermOver' (symbol) BuiltinValue0)) _ (@TermOver_countable (symbol) BuiltinValue0 (@symbol_eqdec symbol symbols) _ (@symbol_countable symbol symbols) (@BuiltinValue0_countable (symbol) (@symbol_eqdec symbol symbols) (@symbol_countable symbol symbols)))).
    Definition my_decode := ((@decode (@TermOver' (symbol) BuiltinValue0)) _ (@TermOver_countable (symbol) BuiltinValue0 (@symbol_eqdec symbol symbols) _ (@symbol_countable symbol symbols) (@BuiltinValue0_countable (symbol) (@symbol_eqdec symbol symbols) (@symbol_countable symbol symbols)))).


    Definition liftNulary
        (f : MyUnit -> option (@TermOver' (symbol) BuiltinValue))
        : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> option (@TermOver' (symbol) BuiltinValue))
    :=
        fun nv l =>
        match l with
        | [] => f nv
        | _::_ => None
        end
    .

    Definition liftNularyP
        (f : MyUnit -> option bool)
        : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> option bool)
    :=
        fun nv l =>
        match l with
        | [] => f nv
        | _::_ => None
        end
    .

    Definition liftUnary
        (f : MyUnit -> (@TermOver' (symbol) BuiltinValue) -> option (@TermOver' (symbol) BuiltinValue))
        : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> option (@TermOver' (symbol) BuiltinValue))
    :=
        fun nv l =>
        match l with
        | [] => None
        | x1::[] => f nv x1
        | _::_::_ => None
        end
    .

    Definition liftUnaryP
        (f : MyUnit -> (@TermOver' (symbol) BuiltinValue) -> option bool)
        : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> option bool)
    :=
        fun nv l =>
        match l with
        | [] => None
        | x1::[] => f nv x1
        | _::_::_ => None
        end
    .

    Definition liftBinary
        (f : MyUnit -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue) -> option (@TermOver' (symbol) BuiltinValue))
        : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> option (@TermOver' (symbol) BuiltinValue))
    :=
        fun nv l =>
        match l with
        | [] => None
        | _::[] => None
        | x1::x2::[] => f nv x1 x2
        | _::_::_::_ => None
        end
    .

    Definition liftBinaryP
        (f : MyUnit -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue) -> option bool)
        : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> option bool)
    :=
        fun nv l =>
        match l with
        | [] => None
        | _::[] => None
        | x1::x2::[] => f nv x1 x2
        | _::_::_::_ => None
        end
    .

    Definition liftTernary
        (f : MyUnit -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue) -> option (@TermOver' (symbol) BuiltinValue))
        : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> option (@TermOver' (symbol) BuiltinValue))
    :=
        fun nv l =>
        match l with
        | [] => None
        | _::[] => None
        | _::_::[] => None
        | x1::x2::x3::[] => f nv x1 x2 x3
        | _::_::_::_::_ => None
        end
    .

    #[local]
    Program Instance mysignature : Signature := {|
        builtin_function_symbol
            := FunctionSymbol ;

        builtin_predicate_symbol
            := PredicateSymbol ;
    
        bps_ar := fun p =>
            match p with
            | b_isBuiltin => 1
            | b_isNotBuiltin => 1
            | b_isSymbol => 1
            | b_isNotSymbol => 1
            | b_isZ => 1
            | b_isNotZ => 1
            | b_isBool => 1
            | b_isNotBool => 1
            | b_isString => 1
            | b_isNotString => 1
            | b_isList => 1
            | b_isNotList => 1
            | b_isMap => 1
            | b_isNotMap => 1
            | b_bool_is_true => 1
            | b_bool_is_false => 1
            | b_term_eq => 2
            | b_map_hasKey => 2
            | b_is_applied_symbol => 2
            | b_is_not_applied_symbol => 2
            | b_have_same_symbol => 2
            | b_have_different_symbols => 2
            end ;
        bps_neg := fun p =>
            match p with
            | b_isBuiltin => Some b_isNotBuiltin
            | b_isNotBuiltin => Some b_isBuiltin
            | b_isSymbol => Some b_isNotSymbol
            | b_isNotSymbol => Some b_isSymbol
            | b_isZ => Some b_isNotZ
            | b_isNotZ => Some b_isZ
            | b_isBool => Some b_isNotBool
            | b_isNotBool => Some b_isBool
            | b_isString => Some b_isNotString
            | b_isNotString => Some b_isString
            | b_isList => Some b_isNotList
            | b_isNotList => Some b_isList
            | b_isMap => Some b_isNotMap
            | b_isNotMap => Some b_isMap
            | b_bool_is_true => Some b_bool_is_false
            | b_bool_is_false => Some b_bool_is_true
            | b_term_eq => None
            | b_map_hasKey => None
            | b_is_applied_symbol => Some b_is_not_applied_symbol
            | b_is_not_applied_symbol => Some b_is_applied_symbol
            | b_have_same_symbol => Some b_have_different_symbols
            | b_have_different_symbols => Some b_have_same_symbol
            end ;

    |}.
    Next Obligation.
        intros p p' H; destruct p, p'; ltac1:(simplify_eq/=); reflexivity.
    Qed.
    Next Obligation.
        intros p p' H; destruct p; simpl; ltac1:(simplify_eq/=); try reflexivity.
    Qed.
    Fail Next Obligation.

    #[local]
    Obligation Tactic := Program.Tactics.program_simpl.
    Program
    Definition βover
        : ModelOver mysignature MyUnit BuiltinValue0
    := {|

        builtin_function_interp
            := fun p =>
            match p with
            (* nulary *)
            | b_zero => liftNulary (
                    fun _ => Some (t_over (bv_Z 0))
                )
            | b_list_empty =>  liftNulary (
                    fun _ => Some ((t_over (bv_list nil)))
                )
            | b_map_empty =>  liftNulary (
                    fun _ => Some (t_over (bv_pmap ∅))
                )
            (* unary *)            
            | b_bool_neg => liftUnary (
                fun _ v =>
                match v with
                | t_over (bv_bool b) => Some (t_over (bv_bool (negb b)))
                | _ => None
                end
            )
            | b_map_size => liftUnary (
                fun _ v =>
                match v with
                | t_over (bv_pmap m) => Some (t_over (bv_Z (Z.of_nat (size m))))
                | _ => None
                end
            )
            | b_Z_plus => liftBinary (
                fun _ v1 v2 =>
                bfmap_Z_Z__Z Z.add v1 v2
            )
            | b_Z_minus => liftBinary (
                fun _ v1 v2 =>
                bfmap_Z_Z__Z Z.sub v1 v2
            )
            | b_Z_times => liftBinary (
                fun _ v1 v2 =>
                bfmap_Z_Z__Z Z.mul v1 v2
            )
            | b_Z_div => liftBinary (
                fun _ v1 v2 =>
                match v2 with
                | t_over (bv_Z (0)) => None
                | _ => bfmap_Z_Z__Z Z.div v1 v2
                end
            )

            | b_Z_eq => liftBinary (
                fun _ v1 v2 =>
                Some (t_over (bv_bool (bool_decide (v1 = v2))))
            )

            | b_Z_neq => liftBinary (
                fun _ v1 v2 =>
                Some (t_over (bv_bool (negb (bool_decide (v1 = v2)))))
            )

            | b_Z_isLe => liftBinary (
                fun _ v1 v2 =>
                ((bfmap_Z_Z__bool Z.leb v1 v2))
            )

            | b_Z_isLt => liftBinary (
                fun _ v1 v2 =>
                ((bfmap_Z_Z__bool Z.ltb v1 v2))
            )

            | b_Z_isGe => liftBinary (
                fun _ v1 v2 =>
                ((bfmap_Z_Z__bool Z.geb v1 v2))
            )

            | b_Z_isGt => liftBinary (
                fun _ v1 v2 =>
                ((bfmap_Z_Z__bool Z.gtb v1 v2))
            )

            | b_map_lookup => liftBinary (
                fun _ v1 v2 =>
                match v1 with
                | t_over (bv_pmap m) =>
                    let p := my_encode (v2) in
                    match m !! p with
                    | Some v => Some (prettify v)
                    | None => None
                    end
                | _ => None
                end
            )

            (* ternary *)
            | b_map_update => liftTernary (
                fun _ v1 v2 v3 =>
                match v1 with
                | t_over (bv_pmap m) =>
                    let p := my_encode (v2) in
                    let m' := <[ p := (uglify' v3) ]>m in
                    Some (t_over (bv_pmap m'))
                | _ => None
                end
            )
            end ;

            builtin_predicate_interp
            := fun p =>
            match p with
            | b_term_eq => liftBinaryP (
                fun _ v1 v2 =>
                Some (bool_decide (v1 = v2))
            )

            | b_bool_is_true => liftUnaryP (
                fun _ v =>
                match v with
                | t_over (bv_bool b) => Some (eqb b true)
                | _ => None
                end
            )

            | b_bool_is_false => liftUnaryP (
                fun _ v =>
                match v with
                | t_over (bv_bool b) => Some (eqb b false)
                | _ => None
                end
            )

            | b_isBuiltin => liftUnaryP (
                fun _ v =>
                match v with
                | t_over b => Some true
                | t_term _ _ => Some false
                end
            )
            | b_isNotBuiltin => liftUnaryP (
                fun _ v =>
                match v with
                | t_over b => Some false
                | t_term _ _ => Some true
                end
            )
            | b_isSymbol => liftUnaryP (
                fun _ v =>
                match v with
                | t_term _ _ => Some true
                | _ => Some false
                end
            )

            | b_isNotSymbol => liftUnaryP (
                fun _ v =>
                match v with
                | t_term _ _ => Some false
                | _ => Some true
                end
            )
   
            | b_isString => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (impl_isString x)
                | _ => Some false
                end
            )

            | b_isNotString => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (negb (impl_isString x))
                | _ => Some true
                end
            )
                
            | b_isList => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (impl_isList x)
                | _ => Some false
                end
            )

            | b_isNotList => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (negb (impl_isList x))
                | _ => Some true
                end
            )

            | b_isBool => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (impl_isBool x)
                | _ => Some false
                end
            )

            | b_isNotBool => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (negb (impl_isBool x))
                | _ => Some true
                end
            )
                
            | b_isMap => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (impl_isMap x)
                | _ => Some false
                end
            )

            | b_isNotMap => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (negb (impl_isMap x))
                | _ => Some true
                end
            )

            | b_isZ => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (impl_isZ x)
                | _ => Some false
                end
            )

            | b_isNotZ => liftUnaryP (
                fun _ v =>
                match v with
                | t_over x => Some (negb (impl_isZ x))
                | _ => Some true
                end
            )    

            | b_map_hasKey => liftBinaryP (
                fun _ v1 v2 =>
                match v1 with
                | t_over (bv_pmap m) =>
                    let p := my_encode (v2) in
                    match m !! p with
                    | Some _ => Some true
                    | None => Some false
                    end
                | _ => None
                end
            )

            | b_have_same_symbol => liftBinaryP (
                fun _ v1 v2 =>
                match v1 with
                | t_term s1 _ =>
                    match v2 with
                    | t_term s2 _ => Some (bool_decide (s1 = s2))
                    | _ => None
                    end
                | _ => None
                end
            )

            | b_have_different_symbols => liftBinaryP (
                fun _ v1 v2 =>
                match v1 with
                | t_term s1 _ =>
                    match v2 with
                    | t_term s2 _ => Some (negb (bool_decide (s1 = s2)))
                    | _ => None
                    end
                | _ => None
                end
            )

            | b_is_applied_symbol => liftBinaryP (
                fun _ v1 v2 =>
                match v1 with
                | t_over (bv_sym s) =>
                    match v2 with
                    | t_term s' _ => Some (bool_decide (s' = s))
                    | _ => None
                    end
                | _ => None
                end
            )

            | b_is_not_applied_symbol => liftBinaryP (
                fun _ v1 v2 =>
                match v1 with
                | t_over (bv_sym s) =>
                    match v2 with
                    | t_term s' _ => Some ( negb (bool_decide (s' = s)))
                    | _ => None
                    end
                | _ => None
                end
            )
            end ;
            bps_neg_correct := _;
    |}.
    (* Solve All Obligations with (simpl; intros; try discriminate). *)
    (* Fail Next Obligation. *)
    Next Obligation.
        intros.
        destruct p,p'; simpl in *; case_on_length (); ltac1:(repeat case_match; simplify_eq/=); try reflexivity.
        {
          rewrite negb_involutive. reflexivity.
        }
        {
          rewrite negb_involutive. reflexivity.
        }
        {
          rewrite negb_involutive. reflexivity.
        }
        {
          rewrite negb_involutive. reflexivity.
        }
        {
          rewrite negb_involutive. reflexivity.
        }
        {
          destruct b0; reflexivity.
        }
        {
          destruct b0; reflexivity.
        }
        {
          rewrite negb_involutive. reflexivity.
        }
        {
          rewrite negb_involutive. reflexivity.
        }
    Qed.
    Fail Next Obligation.

    #[local]
    Instance β
        : Model mysignature MyUnit
    := {|
        builtin_value
            := BuiltinValue ;

        builtin_model_over := βover ;
    |}.

End sec2.


Module Notations.
    
    Notation "'isZ' t" :=
        ((e_fun
            b_isZ
            [(t)]
        ))
        (at level 90)
    .

    Notation "'isString' t" :=
        ((e_fun
            b_isString
            [(t)]
        ))
        (at level 90)
    .

    Notation "'isList' t" :=
        ((e_fun
            b_isList
            [(t)]
        ))
        (at level 90)
    .

    Notation "'isMap' t" :=
        ((e_fun
            b_isMap
            [(t)]
        ))
        (at level 90)
    .

    Notation "'(' x '+Z' y ')'" :=
        ((e_fun b_Z_plus [(x); (y)]))
    .

    Notation "'(' x '-Z' y ')'" :=
        ((e_fun b_Z_minus [(x); (y)]))
    .

    Notation "'(' x '*Z' y ')'" :=
        ((e_fun b_Z_times [(x); (y)]))
    .

    Notation "'(' x '/Z' y ')'" :=
        ((e_fun b_Z_div [(x); (y)]))
    .

    Notation "'(' x '<Z' y ')'" :=
        ((e_fun b_Z_isLt [(x); (y)]))
    .

    Notation "'(' x '>Z' y ')'" :=
        ((e_fun b_Z_isLt [(x); (y)]))
    .

    Notation "'(' x '==Term' y ')'" :=
        ((e_fun b_term_eq [(x); (y)]))
    .

    Notation "'(' x '==Z' y ')'" :=
        ((e_fun b_Z_eq [(x); (y)]))
    .

    Notation "<opaque map>" := (bv_pmap (PNodes _)) (only printing).

End Notations.

Definition builtins_binding : BuiltinsBinding := {|
    bb_function_names := [
        (* Sort predicates *)
        ("sym.is", "b_isSymbol");
        ("sym.isNot", "b_isNotSymbol");
        ("bool.is", "b_isBool");
        ("bool.isNot", "b_isNotBool");
        ("string.is", "b_isString");
        ("string.isNot", "b_isNotString");
        ("z.is", "b_isZ");
        ("z.isNot", "b_isZNot");

        ("bool.neg", "b_bool_neg");
        ("bool.is_true", "b_bool_is_true");
        ("bool.is_false", "b_bool_is_false");
        
        ("term.eq", "b_term_eq");
        ("term.same_symbol", "b_have_same_symbol");
        ("term.different_symbol", "b_have_different_symbols");        ("z.minus", "b_Z_minus");
        ("z.plus", "b_Z_plus");
        ("z.eq", "b_Z_eq");
        ("z.le", "b_Z_isLe");
        ("z.lt", "b_Z_isLt");
        ("map.hasKey", "b_map_hasKey");
        ("map.lookup", "b_map_lookup");
        ("map.size", "b_map_size");
        ("map.empty", "b_map_empty");
        ("map.update", "b_map_update")
    ];
|}.

Definition eject
    {symbol : Type}
    (v : @BuiltinValue0 symbol)
    :
    option (bool+(Z+(string)))%type
    :=
    match v with
    | bv_bool b => Some (inl b)
    | bv_Z z => Some (inr(inl z))
    | bv_str s => Some (inr(inr (s)))
    | _ => None
    end 
.


(* Print bv_list. *)

Section sb.
    Context
        {symbol : Type}
        (show_symbol : symbol -> string)
    .

    (* Doing recursion of BuiltinValue0 is really hard. I gave up, as we need to deprecate klike anyway. *)
    Definition show_builtin
        (v : @BuiltinValue symbol)
        : string
    :=
        match v with
        | bv_bool true => "true"
        | bv_bool false => "false"
        | bv_Z z => pretty_Z z
        | bv_sym s => (show_symbol s) +:+ "@sym"
        | bv_str s => (s) +:+ "@str"
        | bv_list l =>
            "<unsupported (list of stuff)>"
        | bv_pmap p =>
            "<unsupported (map of stuff)>"
        end
.

End sb.
