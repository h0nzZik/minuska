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
            {Σ : StaticModel}
        .

        Print StaticModel.
        Definition BuiltinValue := @BuiltinValue0 symbol.

        Definition err {Σ : StaticModel}
        :=
            @t_over Σ BuiltinValue bv_error
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
            (x : TermOver BuiltinValue)
            : TermOver BuiltinValue
        :=
        match x with
        | t_over x' => t_over (f x')
        | _ => err
        end.

        Definition bfmap2
            (f : BuiltinValue -> BuiltinValue -> BuiltinValue)
            (x y : TermOver BuiltinValue)
            : TermOver BuiltinValue
        :=
        match x, y with
        | t_over x', t_over y' => t_over (f x' y')
        | _,_ => err
        end.

        Definition bfmap_bool__bool
            (f : bool -> bool)
            (x : TermOver BuiltinValue)
            : TermOver BuiltinValue
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
            (x y : TermOver BuiltinValue)
            : TermOver BuiltinValue
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
            (x : TermOver BuiltinValue)
            : TermOver BuiltinValue
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
            (x y : TermOver BuiltinValue)
            : TermOver BuiltinValue
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
            (x y : TermOver BuiltinValue)
            : TermOver BuiltinValue
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
            (x y : TermOver BuiltinValue)
            : TermOver BuiltinValue
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
            (x y : TermOver BuiltinValue)
            : TermOver BuiltinValue
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

        Check @Builtin.
        #[local]
        Instance β
            : @Builtin string MySymbols
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
                uglify'
                match p with
                | b_false => t_over (bv_bool false)
                | b_true => t_over (bv_bool true)
                | b_zero => t_over (bv_nat 0)
                | b_list_empty => (t_over (bv_list nil))
                | b_map_empty => (t_over (bv_pmap ∅))
                end ;
 
            builtin_unary_function_interp
                := fun p v =>
                uglify'
                match p with
                | b_isBuiltin => bfmap1 impl_isBuiltin (prettify v)
                | b_isError =>
                    match (prettify v) with
                    | t_over x => t_over (bv_bool (impl_isError x))
                    | _ => t_over (bv_bool false)
                    end
                | b_isBool =>
                    match (prettify v) with
                    | t_over x => t_over (bv_bool (impl_isBool x))
                    | _ => t_over (bv_bool false)
                    end
                | b_isString =>
                    match (prettify v) with
                    | t_over x => t_over (bv_bool (impl_isString x))
                    | _ => t_over (bv_bool false)
                    end
                | b_isList =>
                    match (prettify v) with
                    | t_over x => t_over (bv_bool (impl_isList x))
                    | _ => t_over (bv_bool false)
                    end
                | b_isMap =>
                    match (prettify v) with
                    | t_over x => t_over (bv_bool (impl_isMap x))
                    | _ => t_over (bv_bool false)
                    end

                | b_bool_neg =>
                    bfmap_bool__bool negb (prettify v)
                
                | b_isNat =>
                    match (prettify v) with
                    | t_over x => t_over (bv_bool (impl_isNat x))
                    | _ => t_over (bv_bool false)
                    end
                | b_isZ =>
                    match (prettify v) with
                    | t_over x => t_over (bv_bool (impl_isZ x))
                    | _ => t_over (bv_bool false)
                    end
                
                | b_nat_isZero =>
                    match (prettify v) with
                    | t_over (bv_nat 0) => t_over (bv_bool true)
                    | _ => t_over (bv_bool false)
                    end
                | b_nat_isSucc =>
                    match (prettify v) with
                    | t_over (bv_nat (S _)) => t_over (bv_bool true)
                    | _ => t_over (bv_bool false)
                    end
                | b_nat_succOf =>
                    bfmap_nat__nat S (prettify v)
                | b_nat_predOf =>
                    match (prettify v) with
                    | t_over (bv_nat (S n)) => (t_over (bv_nat n))
                    | _ => err
                    end
                | b_map_size =>
                    match (prettify v) with
                    | t_over (bv_pmap m) => (t_over (bv_nat (size m)))
                    | _ => err
                    end
                | b_Z_of_nat =>
                  match (prettify v) with
                  | t_over (bv_nat n) => (t_over (bv_Z (Z.of_nat n)))
                  | _ => err
                  end
                end;

            builtin_binary_function_interp
                := fun p v1 v2 =>
                uglify'
                match p with
                | b_eq =>
                    t_over (bv_bool (bool_decide (v1 = v2)))
                | b_and =>
                    bfmap_bool_bool__bool andb (prettify v1) (prettify v2)
                | b_or =>
                    bfmap_bool_bool__bool orb (prettify v1) (prettify v2)
                | b_iff =>
                    bfmap_bool_bool__bool eqb (prettify v1) (prettify v2)
                | b_xor =>
                    bfmap_bool_bool__bool xorb (prettify v1) (prettify v2)
                | b_nat_isLe =>
                    bfmap_nat_nat__bool Nat.leb (prettify v1) (prettify v2)
                | b_nat_isLt =>
                    bfmap_nat_nat__bool Nat.ltb (prettify v1) (prettify v2)
                | b_nat_plus =>
                    bfmap_nat_nat__nat plus (prettify v1) (prettify v2)
                | b_nat_minus =>
                    bfmap_nat_nat__nat minus (prettify v1) (prettify v2)
                | b_nat_times =>
                    bfmap_nat_nat__nat mult (prettify v1) (prettify v2)
                | b_nat_div =>
                    match prettify v2 with
                    | t_over (bv_nat (0)) => err
                    | _ => bfmap_nat_nat__nat Nat.div (prettify v1) (prettify v2)
                    end
                | b_Z_isLe =>
                    bfmap_Z_Z__bool Z.leb (prettify v1) (prettify v2)
                | b_Z_isLt =>
                    bfmap_Z_Z__bool Z.ltb (prettify v1) (prettify v2)
                | b_Z_plus =>
                    bfmap_Z_Z__Z Z.add (prettify v1) (prettify v2)
                | b_Z_minus =>
                    bfmap_Z_Z__Z Z.sub (prettify v1) (prettify v2)
                | b_Z_times =>
                    bfmap_Z_Z__Z Z.mul (prettify v1) (prettify v2)
                | b_Z_div =>
                match prettify v2 with
                | t_over (bv_Z (0)) => err
                | _ => bfmap_Z_Z__Z Z.div (prettify v1) (prettify v2)
                end
                | b_map_hasKey =>
                    match prettify v1 with
                    | t_over (bv_pmap m) =>
                        let p := encode v2 in
                        match m !! p with
                        | Some _ => (t_over (bv_bool true))
                        | None => (t_over (bv_bool false))
                        end
                    | _ => err
                    end
                | b_map_lookup =>
                    match prettify v1 with
                    | t_over (bv_pmap m) =>
                        let p := encode v2 in
                        match m !! p with
                        | Some v => v
                        | None => err
                        end
                    | _ => err
                    end
                | b_is_applied_symbol =>
                    match prettify v1 with
                    | t_over (bv_sym s) =>
                        match v2 with
                        | term_preterm ao => (t_over (bv_bool (bool_decide (AO'_getOperator ao = s))))
                        | _ => (t_over (bv_bool false))
                        end
                    | _ => (t_over (bv_bool false))
                    end
                end ;
            builtin_ternary_function_interp := fun p v1 v2 v3 =>
                uglify'
                match p with
                | b_map_update =>
                    match prettify v1 with
                    | t_over (bv_pmap m) =>
                        let p := encode v2 in
                        let m' := <[ p := v3 ]>m in
                        t_over (bv_pmap m')
                    | _ => err
                    end
                end ;
        |}.

    End sec.


    Module Notations.
        
        
        Notation "'true'" := (e_nullary b_true)
            : RuleScope
        .

        Notation "'false'" := (e_nullary b_false)
            : RuleScope
        .
    
        Notation "b1 '&&' b2" :=
            (e_binary default_builtin.b_and
                (b1)
                (b2)
            )
            : RuleScope
        .

        Notation "b1 '||' b2" :=
            (e_binary default_builtin.b_or
                (b1)
                (b2)
            )
            : RuleScope
        .

        Notation "~~ b" :=
            (e_unary default_builtin.b_bool_neg (b))
        .

        Notation "'isBool' t" :=
            (e_unary
                b_isBool
                t
            )
            (at level 90)
        .        

        Notation "'isNat' t" :=
            (e_unary
                b_isNat
                t
            )
            (at level 90)
        .

        Notation "'isZ' t" :=
            (e_unary
                b_isZ
                t
            )
            (at level 90)
        .

        Notation "'isString' t" :=
            (e_unary
                b_isString
                t
            )
            (at level 90)
        .

        Notation "'isList' t" :=
            (e_unary
                b_isList
                t
            )
            (at level 90)
        .

        Notation "'isMap' t" :=
            (e_unary
                b_isMap
                t
            )
            (at level 90)
        .

        Notation "'(' x '+Nat' y ')'" :=
            (e_binary b_nat_plus (x) (y))
        .

        Notation "'(' x '-Nat' y ')'" :=
            (e_binary b_nat_minus (x) (y))
        .

        Notation "'(' x '*Nat' y ')'" :=
            (e_binary b_nat_times (x) (y))
        .

        Notation "'(' x '/Nat' y ')'" :=
            (e_binary b_nat_div (x) (y))
        .

        Notation "'(' x '==Nat' y ')'" :=
            (e_binary b_eq (x) (y))
        .


        Notation "'(' x '+Z' y ')'" :=
            (e_binary b_Z_plus (x) (y))
        .

        Notation "'(' x '-Z' y ')'" :=
            (e_binary b_Z_minus (x) (y))
        .

        Notation "'(' x '*Z' y ')'" :=
            (e_binary b_Z_times (x) (y))
        .

        Notation "'(' x '/Z' y ')'" :=
            (e_binary b_Z_div (x) (y))
        .

        Notation "'(' x '<Z' y ')'" :=
            (e_binary b_Z_isLt (x) (y))
        .

        Notation "'(' x '>Z' y ')'" :=
            (e_binary b_Z_isLt (y) (x))
        .

        Notation "'(' x '==Z' y ')'" :=
            (e_binary b_eq (x) (y))
        .

        Notation "'(' x '==Bool' y ')'" :=
            (e_binary b_eq (x) (y))
        .

        Notation "'(' x '==Gen' y ')'" :=
            (e_binary b_eq (x) (y))
        .


        Notation "<opaque map>" := (bv_pmap (PNodes _)) (only printing).

    End Notations.

End default_builtin.


    Section ws.
        Check @t_over.
        Definition isAppliedSymbol (s:string) (e : @Expression2 (default_model (default_builtin.β))) :=
            (@e_binary ( default_model (default_builtin.β))
                default_builtin.b_is_applied_symbol
                (@e_ground
                    ( default_model (default_builtin.β))
                    (@t_over _ (@builtin_value _ _ default_builtin.β) (bv_sym s))
                )
                e
            )
        .

    End ws.