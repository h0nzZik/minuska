From Minuska Require Import
    prelude
    spec_syntax
    notations
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

    | b_isZero  (* 'a -> bool *)
    | b_isSucc  (* 'a -> bool *)
    | b_succOf  (* nat -> nat *)
    | b_predOf  (* nat -> nat *)
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

    | b_isLe  (* nat -> nat -> bool *)
    | b_isLt  (* nat -> nat -> bool *)
    | b_plus  (* nat -> nat -> nat *)
    | b_minus (* nat -> nat -> nat *)
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
        .

        #[export]
        Instance BuiltinValue_eqDec : EqDecision BuiltinValue.
        Proof. ltac1:(solve_decision). Defined.

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
                | b_isZero =>
                    match v with
                    | aoo_operand (bv_nat 0) => aoo_operand (bv_bool true)
                    | _ => aoo_operand (bv_bool false)
                    end
                | b_isSucc =>
                    match v with
                    | aoo_operand (bv_nat (S _)) => aoo_operand (bv_bool true)
                    | _ => aoo_operand (bv_bool false)
                    end
                | b_succOf =>
                    bfmap_nat__nat S v
                | b_predOf =>
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
                | b_isLe =>
                    bfmap_nat_nat__bool Nat.leb v1 v2
                | b_isLt =>
                    bfmap_nat_nat__bool Nat.ltb v1 v2
                | b_plus =>
                    bfmap_nat_nat__nat plus v1 v2
                | b_minus =>
                    bfmap_nat_nat__nat minus v1 v2
                end ;
        |}.

    End sec.


    Module Notations.
        
        (*
        Notation "'true'" := (ft_nullary b_true)
            : RuleScsScope
        .

        Notation "'false'" := (ft_nullary b_false)
            : RuleScsScope
        .
        *)
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
            (ft_binary b_plus (x) (y))
        .

    End Notations.

End default_builtin.