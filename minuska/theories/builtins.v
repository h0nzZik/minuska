From Minuska Require Import
    prelude
    spec_syntax
    syntax_properties
    notations
    default_static_model
    BuiltinValue
.

From Coq Require Import ZArith.

Inductive Emptyset : Set := .

#[export]
Instance emptyset_eqdec : EqDecision Emptyset.
Proof.
    intros x y.
    destruct x, y.
Defined.


Module empty_builtin.

    Section sec.

        Context
            {symbol : Set}
            {symbols : Symbols symbol}
        .

        #[local]
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
            builtin_ternary_function
                := Emptyset ;
            builtin_nullary_function_interp
                := fun p => match p with end ;
            builtin_unary_function_interp
                := fun p v => match p with end ;
            builtin_binary_function_interp
                := fun p v1 v2 => match p with end ;
            builtin_ternary_function_interp
                := fun p v1 v2 v3 => match p with end ;
        |}.

    End sec.

End empty_builtin.

Module default_builtin.
    Export BuiltinValue.

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

    | b_list_empty

    | b_map_empty
    .

    #[export]
    Instance NullaryF_eqDec : EqDecision NullaryF.
    Proof. ltac1:(solve_decision). Defined.

    Inductive UnaryF : Set :=
    | b_isBuiltin (* 'a -> bool *)
    | b_isError   (* 'a -> bool *)
    | b_isBool    (* 'a -> bool *)
    | b_isNat     (* 'a -> bool *)
    | b_isZ     (* 'a -> bool *)
    | b_isString  (* 'a -> bool *)
    | b_isList    (* 'a -> bool *)
    | b_isMap     (* 'a -> bool *)

    | b_bool_neg (* bool -> bool *)

    | b_nat_isZero  (* 'a -> bool *)
    | b_nat_isSucc  (* 'a -> bool *)
    | b_nat_succOf  (* nat -> nat *)
    | b_nat_predOf  (* nat -> nat *)

    | b_Z_of_nat    (* nat -> Z *)

    | b_map_size    (* map -> nat *)
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

    | b_map_hasKey  (* map -> 'a -> bool *)
    | b_map_lookup  (* map -> 'a -> 'b *)

    | b_is_applied_symbol (* string -> 'a -> bool*)
    .

    #[export]
    Instance BinaryF_eqdec : EqDecision BinaryF.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Inductive TernaryF : Set :=
    | b_map_update (* map -> 'a -> 'b -> map  *)
    .

    #[export]
    Instance TernaryF_eqdec : EqDecision TernaryF.
    Proof.
        ltac1:(solve_decision).
    Defined.

    Section sec.

        Context
            {symbol : Set}
            {symbols : Symbols symbol}
        .

        Definition BuiltinValue := @BuiltinValue0 symbol.

        Definition err
        :=
            @term_operand symbol BuiltinValue bv_error
        .

        Definition impl_isBuiltin (bv : BuiltinValue) : BuiltinValue
        :=
            (bv_bool true)
        .

        Definition impl_isError (bv : BuiltinValue) : bool
        :=
            match bv with bv_error => true | _ => false end
        .

        Definition impl_isBool (bv : BuiltinValue) : bool
        :=
            match bv with bv_bool _ => true | _ => false end
        .

        Definition impl_isNat (bv : BuiltinValue) : bool
        :=
            match bv with bv_nat _ => true | _ => false end
        .

        Definition impl_isZ (bv : BuiltinValue) : bool
        :=
            match bv with bv_Z _ => true | _ => false end
        .

        Definition impl_isString (bv : BuiltinValue) : bool
        :=
            match bv with bv_str _ => true | _ => false end
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
            (f : BuiltinValue -> BuiltinValue)
            (x : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
        :=
        match x with
        | term_operand x' => term_operand (f x')
        | _ => err
        end.

        Definition bfmap2
            (f : BuiltinValue -> BuiltinValue -> BuiltinValue)
            (x y : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
        :=
        match x, y with
        | term_operand x', term_operand y' => term_operand (f x' y')
        | _,_ => err
        end.

        Definition bfmap_bool__bool
            (f : bool -> bool)
            (x : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
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
            (x y : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
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
            (x : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
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
            (x y : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
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
            (x y : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
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
            (x y : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
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
            (x y : Term' symbol BuiltinValue)
            : Term' symbol BuiltinValue
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

        #[local]
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

            builtin_ternary_function
                := TernaryF ;

            builtin_nullary_function_interp
                := fun p =>
                match p with
                | b_false => term_operand (bv_bool false)
                | b_true => term_operand (bv_bool true)
                | b_zero => term_operand (bv_nat 0)
                | b_list_empty => (term_operand (bv_list nil))
                | b_map_empty => (term_operand (bv_pmap ∅))
                end ;
 
            builtin_unary_function_interp
                := fun p v =>
                match p with
                | b_isBuiltin => bfmap1 impl_isBuiltin v
                | b_isError =>
                    match v with
                    | term_operand x => term_operand (bv_bool (impl_isError x))
                    | _ => term_operand (bv_bool false)
                    end
                | b_isBool =>
                    match v with
                    | term_operand x => term_operand (bv_bool (impl_isBool x))
                    | _ => term_operand (bv_bool false)
                    end
                | b_isString =>
                    match v with
                    | term_operand x => term_operand (bv_bool (impl_isString x))
                    | _ => term_operand (bv_bool false)
                    end
                | b_isList =>
                    match v with
                    | term_operand x => term_operand (bv_bool (impl_isList x))
                    | _ => term_operand (bv_bool false)
                    end
                | b_isMap =>
                    match v with
                    | term_operand x => term_operand (bv_bool (impl_isMap x))
                    | _ => term_operand (bv_bool false)
                    end

                | b_bool_neg =>
                    bfmap_bool__bool negb v
                
                | b_isNat =>
                    match v with
                    | term_operand x => term_operand (bv_bool (impl_isNat x))
                    | _ => term_operand (bv_bool false)
                    end
                | b_isZ =>
                    match v with
                    | term_operand x => term_operand (bv_bool (impl_isZ x))
                    | _ => term_operand (bv_bool false)
                    end
                
                | b_nat_isZero =>
                    match v with
                    | term_operand (bv_nat 0) => term_operand (bv_bool true)
                    | _ => term_operand (bv_bool false)
                    end
                | b_nat_isSucc =>
                    match v with
                    | term_operand (bv_nat (S _)) => term_operand (bv_bool true)
                    | _ => term_operand (bv_bool false)
                    end
                | b_nat_succOf =>
                    bfmap_nat__nat S v
                | b_nat_predOf =>
                    match v with
                    | term_operand (bv_nat (S n)) => (term_operand (bv_nat n))
                    | _ => err
                    end
                | b_map_size =>
                    match v with
                    | term_operand (bv_pmap m) => (term_operand (bv_nat (size m)))
                    | _ => err
                    end
                | b_Z_of_nat =>
                  match v with
                  | term_operand (bv_nat n) => (term_operand (bv_Z (Z.of_nat n)))
                  | _ => err
                  end
                end;

            builtin_binary_function_interp
                := fun p v1 v2 =>
                match p with
                | b_eq =>
                    term_operand (bv_bool (bool_decide (v1 = v2)))
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
                    | term_operand (bv_nat (0)) => err
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
                | term_operand (bv_Z (0)) => err
                | _ => bfmap_Z_Z__Z Z.div v1 v2
                end
                | b_map_hasKey =>
                    match v1 with
                    | term_operand (bv_pmap m) =>
                        let p := encode v2 in
                        match m !! p with
                        | Some _ => (term_operand (bv_bool true))
                        | None => (term_operand (bv_bool false))
                        end
                    | _ => err
                    end
                | b_map_lookup =>
                    match v1 with
                    | term_operand (bv_pmap m) =>
                        let p := encode v2 in
                        match m !! p with
                        | Some v => v
                        | None => err
                        end
                    | _ => err
                    end
                | b_is_applied_symbol =>
                    match v1 with
                    | term_operand (bv_sym s) =>
                        match v2 with
                        | term_preterm ao => (term_operand (bv_bool (bool_decide (AO'_getOperator ao = s))))
                        | _ => (term_operand (bv_bool false))
                        end
                    | _ => (term_operand (bv_bool false))
                    end
                end ;
            builtin_ternary_function_interp := fun p v1 v2 v3 =>
                match p with
                | b_map_update =>
                    match v1 with
                    | term_operand (bv_pmap m) =>
                        let p := encode v2 in
                        let m' := <[ p := v3 ]>m in
                        term_operand (bv_pmap m')
                    | _ => err
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

        Notation "b1 '||' b2" :=
            (ft_binary default_builtin.b_or
                (b1)
                (b2)
            )
            : RuleScope
        .

        Notation "~~ b" :=
            (ft_unary default_builtin.b_bool_neg (b))
        .

        Notation "'isBool' t" :=
            (ft_unary
                b_isBool
                t
            )
            (at level 90)
        .        

        Notation "'isNat' t" :=
            (ft_unary
                b_isNat
                t
            )
            (at level 90)
        .

        Notation "'isZ' t" :=
            (ft_unary
                b_isZ
                t
            )
            (at level 90)
        .

        Notation "'isString' t" :=
            (ft_unary
                b_isString
                t
            )
            (at level 90)
        .

        Notation "'isList' t" :=
            (ft_unary
                b_isList
                t
            )
            (at level 90)
        .

        Notation "'isMap' t" :=
            (ft_unary
                b_isMap
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

        Notation "'(' x '<Z' y ')'" :=
            (ft_binary b_Z_isLt (x) (y))
        .

        Notation "'(' x '>Z' y ')'" :=
            (ft_binary b_Z_isLt (y) (x))
        .

        Notation "'(' x '==Z' y ')'" :=
            (ft_binary b_eq (x) (y))
        .

        Notation "'(' x '==Bool' y ')'" :=
            (ft_binary b_eq (x) (y))
        .

        Notation "'(' x '==Gen' y ')'" :=
            (ft_binary b_eq (x) (y))
        .


        Notation "<opaque map>" := (bv_pmap (PNodes _)) (only printing).

    End Notations.

End default_builtin.


    Section ws.

        Definition isAppliedSymbol (s:string) (e : @Expression (default_model (default_builtin.β))) :=
            (@ft_binary ( default_model (default_builtin.β))
                default_builtin.b_is_applied_symbol
                (@ft_element
                    ( default_model (default_builtin.β))
                    (@term_operand
                        (@spec_syntax.symbol
                            ( default_model (default_builtin.β))
                        )
                        (@builtin_value _ _ default_builtin.β )
                        (bv_sym s)
                    )
                )
                e
            )
        .

    End ws.