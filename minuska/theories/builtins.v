From Minuska Require Import
    prelude
    spec
    basic_properties
    lowlang
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
            : Builtin MyUnit := {|
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
    | b_isZ     (* 'a -> bool *)
    | b_isString  (* 'a -> bool *)
    | b_isList    (* 'a -> bool *)
    | b_isMap     (* 'a -> bool *)

    | b_bool_neg (* bool -> bool *)

    | b_map_size    (* map -> Z *)
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

    | b_Z_isLe  (* Z -> Z -> bool *)
    | b_Z_isLt  (* Z -> Z -> bool *)
    | b_Z_plus  (* Z -> Z -> Z *)
    | b_Z_minus (* Z -> Z -> Z *)
    | b_Z_times (* Z -> Z -> Z *)
    | b_Z_div   (* Z -> Z -> Z *)

    | b_map_hasKey  (* map -> 'a -> bool *)
    | b_map_lookup  (* map -> 'a -> 'b *)

    | b_is_applied_symbol (* string -> 'a -> bool*)
    | b_have_same_symbol (* term -> term -> bool*)
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
            @t_over symbol BuiltinValue bv_error
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
            (x : @TermOver' symbol BuiltinValue)
            : @TermOver' symbol BuiltinValue
        :=
        match x with
        | t_over x' => t_over (f x')
        | _ => err
        end.

        Definition bfmap2
            (f : BuiltinValue -> BuiltinValue -> BuiltinValue)
            (x y : @TermOver' symbol BuiltinValue)
            : @TermOver' symbol BuiltinValue
        :=
        match x, y with
        | t_over x', t_over y' => t_over (f x' y')
        | _,_ => err
        end.

        Definition bfmap_bool__bool
            (f : bool -> bool)
            (x : @TermOver' symbol BuiltinValue)
            : @TermOver' symbol BuiltinValue
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
            (x y : @TermOver' symbol BuiltinValue)
            : @TermOver' symbol BuiltinValue
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

        Definition bfmap_Z_Z__Z
            (f : Z -> Z -> Z)
            (x y : @TermOver' symbol BuiltinValue)
            : @TermOver' symbol BuiltinValue
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
            (x y : @TermOver' symbol BuiltinValue)
            : @TermOver' symbol BuiltinValue
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

        Definition my_encode := ((@encode (@TermOver' (symbol) BuiltinValue.BuiltinValue0)) _ (@TermOver_countable (symbol) BuiltinValue.BuiltinValue0 (@symbol_eqdec symbol symbols) _ (@symbol_countable symbol symbols) (@BuiltinValue.BuiltinValue0_countable (symbol) (@symbol_eqdec symbol symbols) (@symbol_countable symbol symbols)))).

        #[local]
        Instance β
            : Builtin MyUnit
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
                | b_false => fun _ => t_over (bv_bool false)
                | b_true => fun _ => t_over (bv_bool true)
                | b_zero => fun _ => t_over (bv_Z 0)
                | b_list_empty => fun _ => (t_over (bv_list nil))
                | b_map_empty => fun _ => (t_over (bv_pmap ∅))
                end ;
 
            builtin_unary_function_interp
                := fun p v =>
                match p with
                | b_isBuiltin => fun _ => bfmap1 impl_isBuiltin v
                | b_isError =>
                    match v with
                    | t_over x => fun _ => t_over (bv_bool (impl_isError x))
                    | _ => fun _ => t_over (bv_bool false)
                    end
                | b_isBool =>
                    match v with
                    | t_over x => fun _ => t_over (bv_bool (impl_isBool x))
                    | _ => fun _ => t_over (bv_bool false)
                    end
                | b_isString =>
                    match v with
                    | t_over x => fun _ => t_over (bv_bool (impl_isString x))
                    | _ => fun _ => t_over (bv_bool false)
                    end
                | b_isList =>
                    match v with
                    | t_over x => fun _ => t_over (bv_bool (impl_isList x))
                    | _ => fun _ => t_over (bv_bool false)
                    end
                | b_isMap =>
                    match v with
                    | t_over x => fun _ => t_over (bv_bool (impl_isMap x))
                    | _ => fun _ => t_over (bv_bool false)
                    end

                | b_bool_neg =>
                    fun _ => bfmap_bool__bool negb v
                
                | b_isZ =>
                    match v with
                    | t_over x => fun _ => t_over (bv_bool (impl_isZ x))
                    | _ => fun _ => t_over (bv_bool false)
                    end
                
                | b_map_size =>
                    match v with
                    | t_over (bv_pmap m) => fun _ => (t_over (bv_Z (Z.of_nat (size m))))
                    | _ => fun _ => err
                    end
                end;

            builtin_binary_function_interp
                := fun p v1 v2 =>
                match p with
                | b_eq =>
                    fun _ => t_over (bv_bool (bool_decide (v1 = v2)))
                | b_and =>
                    fun _ => bfmap_bool_bool__bool andb v1 v2
                | b_or =>
                    fun _ => bfmap_bool_bool__bool orb v1 v2
                | b_iff =>
                    fun _ => bfmap_bool_bool__bool eqb v1 v2
                | b_xor =>
                    fun _ => bfmap_bool_bool__bool xorb v1 v2                    
                | b_Z_isLe =>
                    fun _ => bfmap_Z_Z__bool Z.leb v1 v2
                | b_Z_isLt =>
                    fun _ => bfmap_Z_Z__bool Z.ltb v1 v2
                | b_Z_plus =>
                    fun _ => bfmap_Z_Z__Z Z.add v1 v2
                | b_Z_minus =>
                    fun _ => bfmap_Z_Z__Z Z.sub v1 v2
                | b_Z_times =>
                    fun _ => bfmap_Z_Z__Z Z.mul v1 v2
                | b_Z_div =>
                match v2 with
                | t_over (bv_Z (0)) => fun _ => err
                | _ => fun _ => bfmap_Z_Z__Z Z.div v1 v2
                end
                | b_map_hasKey =>
                    match v1 with
                    | t_over (bv_pmap m) =>
                        let p := my_encode (v2) in
                        match m !! p with
                        | Some _ => fun _ => (t_over (bv_bool true))
                        | None => fun _ => (t_over (bv_bool false))
                        end
                    | _ => fun _ => err
                    end
                | b_map_lookup =>
                    match v1 with
                    | t_over (bv_pmap m) =>
                        let p := my_encode (v2) in
                        match m !! p with
                        | Some v => fun _ => (prettify v)
                        | None => fun _ => err
                        end
                    | _ => fun _ => err
                    end
                | b_have_same_symbol =>
                    match v1 with
                    | t_term s1 _ =>
                        match v2 with
                        | t_term s2 _ => fun _ => (t_over (bv_bool (bool_decide (s1 = s2))))
                        | _ => fun _ => t_over (bv_bool false)
                        end
                    | _ => fun _ => t_over (bv_bool false)
                    end
                | b_is_applied_symbol =>
                    match v1 with
                    | t_over (bv_sym s) =>
                        match v2 with
                        | t_term s' _ => fun _ => (t_over (bv_bool (bool_decide (s' = s))))
                        | _ => fun _ => (t_over (bv_bool false))
                        end
                    | _ => fun _ => (t_over (bv_bool false))
                    end
                end ;
            builtin_ternary_function_interp := fun p v1 v2 v3 =>
                match p with
                | b_map_update =>
                    match v1 with
                    | t_over (bv_pmap m) =>
                        let p := my_encode (v2) in
                        let m' := <[ p := (uglify' v3) ]>m in
                        fun _ => t_over (bv_pmap m')
                    | _ => fun _ => err
                    end
                end ;
        |}.

    End sec.


    Module Notations.
        
        
        Notation "'true'" := ( (e_nullary b_true))
            : RuleScope
        .

        Notation "'false'" := ( (e_nullary b_false))
            : RuleScope
        .
    
        Notation "b1 '&&' b2" :=
            ( (e_binary default_builtin.b_and
                ( b1)
                ( b2)
            ))
            : RuleScope
        .

        Notation "b1 '||' b2" :=
            ( (e_binary default_builtin.b_or
                ( b1)
                ( b2)
            ))
            : RuleScope
        .

        Notation "~~ b" :=
            ( (e_unary default_builtin.b_bool_neg ( b)))
        .

        Notation "'isBool' t" :=
            ( (e_unary
                b_isBool
                ( t)
            ))
            (at level 90)
        .        

        Notation "'isZ' t" :=
            ((e_unary
                b_isZ
                (t)
            ))
            (at level 90)
        .

        Notation "'isString' t" :=
            ((e_unary
                b_isString
                (t)
            ))
            (at level 90)
        .

        Notation "'isList' t" :=
            ((e_unary
                b_isList
                (t)
            ))
            (at level 90)
        .

        Notation "'isMap' t" :=
            ((e_unary
                b_isMap
                (t)
            ))
            (at level 90)
        .

        Notation "'(' x '+Z' y ')'" :=
            ((e_binary b_Z_plus (x) (y)))
        .

        Notation "'(' x '-Z' y ')'" :=
            ((e_binary b_Z_minus (x) (y)))
        .

        Notation "'(' x '*Z' y ')'" :=
            ((e_binary b_Z_times (x) (y)))
        .

        Notation "'(' x '/Z' y ')'" :=
            ((e_binary b_Z_div (x) (y)))
        .

        Notation "'(' x '<Z' y ')'" :=
            ((e_binary b_Z_isLt (x) (y)))
        .

        Notation "'(' x '>Z' y ')'" :=
            ((e_binary b_Z_isLt (x) (y)))
        .

        Notation "'(' x '==Z' y ')'" :=
            ((e_binary b_eq (x) (y)))
        .

        Notation "'(' x '==Bool' y ')'" :=
            ((e_binary b_eq (x) (y)))
        .

        Notation "'(' x '==Gen' y ')'" :=
            ((e_binary b_eq (x) (y)))
        .


        Notation "<opaque map>" := (bv_pmap (PNodes _)) (only printing).

    End Notations.

End default_builtin.


Definition isAppliedSymbol (s:string) (e : @Expression2 (default_model (default_builtin.β))) :=
    let M := ( default_model (default_builtin.β)) in
    ((@e_binary M
        default_builtin.b_is_applied_symbol
        (@e_ground (M) (t_over (bv_sym s)))
        )
        (e)
    )
.