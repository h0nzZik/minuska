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

        #[export]
        Program Instance Cβ
            :
            @ComputableBuiltins _ _ β
        := {|
            builtin_unary_predicate_interp_bool := fun _ _ => false ;
            builtin_binary_predicate_interp_bool := fun _ _ _ => false ;
        |}.
        Next Obligation.
            destruct p.
        Qed.
        Next Obligation.
            destruct p.
        Qed.
        Fail Next Obligation.

    End sec.

End empty_builtin.

Module nat_builtin.

    Inductive NatUnaryP : Set := 
    | Nat_isZero
    | Nat_isSuccc
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
                match p, v with
                | Nat_isZero, aoo_operand (Some 0) => True
                | _, _ => False
                end ;

            builtin_binary_predicate_interp
                := fun p v1 v2 =>
                match p, v1, v2 with
                | Nat_isLe, (aoo_operand (Some x)), (aoo_operand (Some y))
                => x < y
                | _,_,_ => False
                end ;

            builtin_unary_function_interp
                := fun p v =>
                match p with
                | Nat_succOf => S <b1$> v
                | _ => err
                end ;

            builtin_binary_function_interp
                := fun p v1 v2 =>
                match p, v1, v2 with
                | Nat_plus, (aoo_operand (Some x)), (aoo_operand (Some y))
                => aoo_operand (Some (x + y))
                | _, _, _ => err
                end ;
    
        |}.

    End sec.
End nat_builtin.