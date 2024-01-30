From Minuska Require Import
    prelude
    spec_syntax
.

Require Export Minuska.varsof.

Section eqdec.

    #[export]
    Instance AppliedOperator'_eqdec
        {symbol : Type}
        {symbols : Symbols symbol}
        (builtin : Type)
        {builtin_dec : EqDecision builtin}
        : EqDecision (AppliedOperator' symbol builtin)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance GroundTerm'_eqdec
        {A : Type}
        {symbols : Symbols A}
        (T : Type)
        {T_dec : EqDecision T}
        : EqDecision (GroundTerm' A T)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance Expression_eqdec {Σ : StaticModel}
        : EqDecision (Expression)
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance LeftRight_eqdec
        : EqDecision LeftRight
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Program Instance LeftRight_fin
        : Finite LeftRight
    := {|
        enum := [LR_Left;LR_Right];
    |}.
    Next Obligation.
        ltac1:(compute_done).
    Qed.
    Next Obligation.
        destruct x;
        ltac1:(compute_done).
    Qed.
    Fail Next Obligation.

    #[export]
    Instance atomicProposition_eqdec {Σ : StaticModel}
        : EqDecision AtomicProposition
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance BuiltinOrVar_eqdec {Σ : StaticModel}
        : EqDecision BuiltinOrVar
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance GroundTerm_eqdec {Σ : StaticModel}
        : EqDecision GroundTerm
    .
    Proof.
        intros e1 e2.
        apply GroundTerm'_eqdec.
        apply builtin_value_eqdec.
    Defined.

    #[export]
    Instance  OpenTerm_eqdec {Σ : StaticModel}
        : EqDecision OpenTerm
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance  SideCondition_eqdec {Σ : StaticModel}
        : EqDecision SideCondition
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

    #[export]
    Instance RhsPattern_eqdec {Σ : StaticModel}
        : EqDecision RhsPattern
    .
    Proof.
        ltac1:(solve_decision).
    Defined.

End eqdec.


Section countable.

    Fixpoint AppliedOperator'_to_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : AppliedOperator' symbol builtin)
        : gen_tree symbol
    :=
    match a with
    | (ao_operator s) => GenLeaf s
    | (ao_app_operand aps b) =>
        (
            let x := (encode (0, encode b)) in
            GenNode (Pos.to_nat x) ([AppliedOperator'_to_gen_tree symbol builtin aps;AppliedOperator'_to_gen_tree symbol builtin aps(* we duplicate it to make the reverse simpler*)])
        )
    | (ao_app_ao aps1 aps2)
        => (
            let xd := (1, encode 0) in
            let x := (encode xd) in
            GenNode (Pos.to_nat x) ([AppliedOperator'_to_gen_tree _ _ aps1; AppliedOperator'_to_gen_tree _ _ aps2])
        )
    end.

    Fixpoint AppliedOperator'_of_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (t : gen_tree symbol)
        : option (AppliedOperator' symbol builtin)
    :=
    match t with
    | (GenLeaf s)
        => Some (ao_operator s)
    | (GenNode n [gt1;gt2]) =>
        let d := (@decode (nat*positive) _ _ (Pos.of_nat n)) in
        match d with
            | Some (0, pb) =>
                let d' := (@decode builtin _ _ pb) in
                match d' with
                | Some b =>
                    let d'' := (AppliedOperator'_of_gen_tree symbol builtin gt1) in
                    match d'' with 
                    | Some as1 => Some (ao_app_operand as1 b)
                    | _ => None
                    end
                | _ => None
                end
            | Some (1, _) =>
                let d'1 := AppliedOperator'_of_gen_tree symbol builtin gt1 in
                let d'2 := AppliedOperator'_of_gen_tree symbol builtin gt2 in
                match d'1, d'2 with
                | Some aps1, Some aps2 => Some (ao_app_ao aps1 aps2)
                | _, _ => None
                end
            | _ => None
            end
    | _ => None
    end
    .

    Lemma AppliedOperator'_of_to_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (a : AppliedOperator' symbol builtin)
        : AppliedOperator'_of_gen_tree symbol builtin (AppliedOperator'_to_gen_tree symbol builtin a) = Some a
    .
    Proof.
        induction a; simpl.
        { reflexivity. }
        {
            ltac1:(rewrite ! Pos2Nat.id decode_encode).
            rewrite decode_encode.
            rewrite IHa.
            reflexivity.
        }
        {
            rewrite IHa1.
            rewrite IHa2.
            reflexivity.
        }
    Qed.

    #[export]
    Instance appliedOperator_countable
        (symbol_set : Type)
        {symbols : Symbols symbol_set}
        (builtin_set : Type)
        {builtin_eqdec : EqDecision builtin_set}
        {builtin_countable : Countable builtin_set}
        : Countable (AppliedOperator' symbol_set builtin_set)
    .
    Proof.
        apply inj_countable
        with
            (f := AppliedOperator'_to_gen_tree symbol_set builtin_set)
            (g := AppliedOperator'_of_gen_tree symbol_set builtin_set)
        .
        intros x.
        apply AppliedOperator'_of_to_gen_tree.
    Qed.

    Definition GroundTerm'_to_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {T_eqdec : EqDecision builtin}
        {T_countable : Countable builtin}
        (e : GroundTerm' symbol builtin)
        : gen_tree (builtin + (AppliedOperator' symbol builtin))%type
    :=
    match e with
    | (aoo_operand b) => GenLeaf (inl _ b)
    | (aoo_app s) => GenLeaf (inr _ s)
    end
    .

    Definition GroundTerm'_from_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (t : gen_tree (builtin+(AppliedOperator' symbol builtin))%type)
        :  option (GroundTerm' symbol builtin)
    :=
    match t with
    | (GenLeaf (inl _ b)) => Some (aoo_operand b)
    | (GenLeaf (inr _ s)) => Some (aoo_app s)
    | _ => None
    end
    .

    Lemma GroundTerm'_to_from_gen_tree
        (symbol : Type)
        {symbols : Symbols symbol}
        (builtin : Type)
        {builtin_eqdec : EqDecision builtin}
        {builtin_countable : Countable builtin}
        (e : GroundTerm' symbol builtin)
        : GroundTerm'_from_gen_tree symbol builtin (GroundTerm'_to_gen_tree symbol builtin e) = Some e
    .
    Proof.
        destruct e; reflexivity.
    Qed.

    #[export]
    Instance GroundTerm'_countable
        (symbol_set : Type)
        {symbols : Symbols symbol_set}
        (builtin_set : Type)
        {builtin_eqdec : EqDecision builtin_set}
        {builtin_countable : Countable builtin_set}
        : Countable (GroundTerm' symbol_set builtin_set)
    .
    Proof.
        apply inj_countable
        with
            (f := GroundTerm'_to_gen_tree symbol_set builtin_set)
            (g := GroundTerm'_from_gen_tree symbol_set builtin_set)
        .
        intros x.
        apply GroundTerm'_to_from_gen_tree.
    Defined.

End countable.


Fixpoint AppliedOperator'_fmap
    {A B C : Type}
    (f : B -> C)
    (ao : AppliedOperator' A B)
    : AppliedOperator' A C
:=
match ao with
| ao_operator o => ao_operator o
| ao_app_operand ao' x => ao_app_operand (AppliedOperator'_fmap f ao') (f x)
| ao_app_ao ao1 ao2 => ao_app_ao (AppliedOperator'_fmap f ao1) (AppliedOperator'_fmap f ao2)
end.

#[export]
Instance AppliedOperator'_A_B_fmap (A : Type)
    : FMap (AppliedOperator' A)
    := @AppliedOperator'_fmap A
.


Definition Term'_fmap
    {A B C : Type}
    (f : B -> C)
    (aoo : Term' A B)
    : Term' A C
:=
match aoo with
| aoo_app ao => aoo_app (f <$> ao)
| aoo_operand o => aoo_operand (f o)
end.


#[global]
Instance Term'_A_B_fmap (A : Type)
    : FMap (Term' A)
    := @Term'_fmap A
.

#[global]
Instance Term_symbol_fmap
    {Σ : StaticModel}
    : FMap (Term' symbol)
.
Proof.
    apply Term'_A_B_fmap.
Defined.


Fixpoint AppliedOperator'_collapse_option
    {A B : Type}
    (ao : AppliedOperator' A (option B))
    : option (AppliedOperator' A B)
:=
match ao with
| ao_operator o =>
    Some (ao_operator o)

| ao_app_operand ao' x =>
    ao'' ← AppliedOperator'_collapse_option ao';
    x'' ← x;
    Some (ao_app_operand ao'' x'')

| ao_app_ao ao1 ao2 =>
    ao1'' ← AppliedOperator'_collapse_option ao1;
    ao2'' ← AppliedOperator'_collapse_option ao2;
    Some (ao_app_ao ao1'' ao2'')
end.


Definition Term'_collapse_option
    {A B : Type}
    (aoo : Term' A (option B))
    : option (Term' A B)
:=
match aoo with
| aoo_app ao =>
    tmp ← AppliedOperator'_collapse_option ao;
    Some (aoo_app tmp)
| aoo_operand op =>
    tmp ← op;
    Some (aoo_operand tmp)
end.


Fixpoint AppliedOperator'_zipWith
    {A B C D : Type}
    (fa : A -> A -> A)
    (fbc : B -> C -> D)
    (f1 : AppliedOperator' A B -> C -> D)
    (f2 : B -> AppliedOperator' A C -> D)
    (ao1 : AppliedOperator' A B)
    (ao2 : AppliedOperator' A C)
    : AppliedOperator' A D
:=
match ao1,ao2 with
| ao_operator o1, ao_operator o2 => ao_operator (fa o1 o2)
| ao_operator o1, ao_app_operand app2 op2 =>
    ao_operator o1
| ao_operator o1, ao_app_ao app21 app22 =>
    ao_operator o1
| ao_app_operand app1 op1, ao_app_operand app2 op2 =>
    ao_app_operand
        (AppliedOperator'_zipWith fa fbc f1 f2 app1 app2)
        (fbc op1 op2)
| ao_app_operand app1 op1, ao_operator o2 =>
    ao_operator o2
| ao_app_operand app1 op1, ao_app_ao app21 app22 =>
    ao_app_operand
        ((AppliedOperator'_zipWith fa fbc f1 f2 app1 app21))
        (f2 op1 app22)
| ao_app_ao app11 app12, ao_app_ao app21 app22 =>
    ao_app_ao
        (AppliedOperator'_zipWith fa fbc f1 f2 app11 app21)
        (AppliedOperator'_zipWith fa fbc f1 f2 app12 app22)
| ao_app_ao app11 app12, ao_operator op2 =>
    ao_operator op2
| ao_app_ao app11 app12, ao_app_operand app21 op22 =>
    ao_app_operand 
        (AppliedOperator'_zipWith fa fbc f1 f2 app11 app21)
        (f1 app12 op22)
end.

Fixpoint AO'_getOperator {A B : Type}
    (ao : AppliedOperator' A B)
    : A :=
match ao with
| ao_operator o => o
| ao_app_operand ao' _ => AO'_getOperator ao'
| ao_app_ao ao' _ => AO'_getOperator ao'
end.


