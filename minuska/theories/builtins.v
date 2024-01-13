From Minuska Require Import
    prelude
    spec_syntax
.

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
            builtin_unary_predicate
                := Emptyset ;
            builtin_binary_predicate
                := Emptyset ;
            builtin_unary_function
                := Emptyset ;
            builtin_binary_function
                := Emptyset ;
            builtin_unary_predicate_interp
                := fun p v => match p with end ;
            builtin_binary_predicate_interp
                := fun p v1 v2 => match p with end ;
            builtin_unary_function_interp
                := fun p v => match p with end ;
            builtin_binary_function_interp
                := fun p v1 v2 => match p with end ;
        |}.

    End sec.

End empty_builtin.

Module nat_builtin.

    Inductive NatUnaryP : Set :=
    | Nat_isNat
    | Nat_isZero
    | Nat_isSucc
    .

    #[export]
    Instance NatUnaryP_eqdec : EqDecision NatUnaryP.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Inductive NatBinaryP : Set :=
    | Nat_isLe
    | Nat_isLt
    .

    #[export]
    Instance NatBinaryP_eqdec : EqDecision NatBinaryP.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Inductive NatUnaryF : Set :=
    | Nat_succOf
    | Nat_predOf
    .

    #[export]
    Instance NatUnaryF_eqdec : EqDecision NatUnaryF.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Inductive NatBinaryF : Set :=
    | Nat_plus
    | Nat_minus
    .

    #[export]
    Instance NatBinaryF_eqdec : EqDecision NatBinaryF.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Section sec.

        Context
            {symbol : Set}
            {symbols : Symbols symbol}
        .


        Definition err
            {T : Type}
        := @aoo_operand symbol (option T) None
        .

        Definition b1fmap
            {B : Type}
            (f : B -> B)
            (t : GroundTerm' symbol (option B))
            : GroundTerm' symbol (option B)
        :=
            match t with
            | aoo_operand x => aoo_operand (f <$> x)
            | _ => aoo_operand None
            end
        .

        Notation "f '<b1$>' t" := (b1fmap f t) (at level 90).

        Definition b2fmap
            {B : Type}
            (f : B -> B -> B)
            (t1 t2 : GroundTerm' symbol (option B))
            : GroundTerm' symbol (option B)
        :=
            match t1,t2 with
            | aoo_operand (Some z1), aoo_operand (Some z2) =>
                aoo_operand (Some (f z1 z2))
            | _,_ => aoo_operand None
            end
        .


        #[export]
        Instance β
            : Builtin
        := {|
            builtin_value
                := option nat ;
            builtin_unary_predicate
                := NatUnaryP ;
            builtin_binary_predicate
                := NatBinaryP ;
            builtin_unary_function
                := NatUnaryF ;
            builtin_binary_function
                := NatBinaryF ;
            builtin_unary_predicate_interp
                := fun p v =>
                match p with
                | Nat_isZero =>
                    match v with
                    | aoo_operand (Some 0) => true
                    | _ => false
                    end
                | Nat_isSucc =>
                    match v with
                    | aoo_operand (Some (S _)) => true
                    | _ => false
                    end
                | Nat_isNat =>
                    match v with
                    | aoo_operand _ => true
                    | _ => false
                    end
                end;

            builtin_binary_predicate_interp
                := fun p v1 v2 =>
                match p with
                | Nat_isLe =>
                    match v1,v2 with
                    | (aoo_operand (Some x)), (aoo_operand (Some y)) =>
                        x <=? y
                    | _, _ => false
                    end
                | Nat_isLt =>
                    match v1,v2 with
                    | (aoo_operand (Some x)), (aoo_operand (Some y)) =>
                        x <? y
                    | _, _ => false
                    end
                end;
 
            builtin_unary_function_interp
                := fun p v =>
                match p with
                | Nat_succOf =>
                    S <b1$> v
                | Nat_predOf =>
                    match v with
                    | aoo_operand (Some 0) => aoo_operand None
                    | aoo_operand (Some (S n)) => (aoo_operand (Some n))
                    | _ => err
                    end
                end;

            builtin_binary_function_interp
                := fun p v1 v2 =>
                match p with
                | Nat_plus =>
                    match v1, v2 with
                    | (aoo_operand (Some x)), (aoo_operand (Some y))
                        => aoo_operand (Some (x + y))
                    | _,_ => err
                    end
                | Nat_minus =>
                    match v1, v2 with
                    | (aoo_operand (Some x)), (aoo_operand (Some y))
                        => aoo_operand (Some (x - y))
                    | _,_ => err
                    end
                end ;
        |}.

    End sec.
End nat_builtin.