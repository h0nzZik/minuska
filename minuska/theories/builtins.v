From Minuska Require Import
    prelude
    spec
    basic_properties
    lowlang
    syntax_properties
    notations
    default_static_model
    BuiltinValue
    pval_ocaml_binding
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
            builtin_function_symbol
                := Emptyset ;
            builtin_function_interp
                := fun p => match p with end ;
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

    Inductive FunctionSymbol : Set :=
    (* nulary *)
    | b_false             (* bool *)
    | b_true              (* bool *)
    | b_zero              (* Z *)
    | b_list_empty        (* list *)
    | b_map_empty         (* map *)
    (* unary *)
    | b_isBuiltin         (* 'a -> bool *)
    | b_isError           (* 'a -> bool *)
    | b_isBool            (* 'a -> bool *)
    | b_isZ               (* 'a -> bool *)
    | b_isString          (* 'a -> bool *)
    | b_isList            (* 'a -> bool *)
    | b_isMap             (* 'a -> bool *)
    | b_bool_neg          (* bool -> bool *)
    | b_map_size          (* map -> Z *)
    (* binary *)
    | b_eq                (* 'a -> 'b -> bool *)
    | b_and               (* bool -> bool -> bool *)
    | b_or                (* bool -> bool -> bool *)
    | b_iff               (* bool -> bool -> bool *)
    | b_xor               (* bool -> bool -> bool *)
    | b_Z_isLe            (* Z -> Z -> bool *)
    | b_Z_isLt            (* Z -> Z -> bool *)
    | b_Z_plus            (* Z -> Z -> Z *)
    | b_Z_minus           (* Z -> Z -> Z *)
    | b_Z_times           (* Z -> Z -> Z *)
    | b_Z_div             (* Z -> Z -> Z *)
    | b_map_hasKey        (* map -> 'a -> bool *)
    | b_map_lookup        (* map -> 'a -> 'b *)
    | b_is_applied_symbol (* string -> 'a -> bool*)
    | b_have_same_symbol  (* term -> term -> bool*)
    (* ternary*)
    | b_map_update        (* map -> 'a -> 'b -> map  *)
    .

    #[export]
    Instance FunctionSymbol_eqDec : EqDecision FunctionSymbol.
    Proof. ltac1:(solve_decision). Defined.

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


        Definition liftNulary
            (f : MyUnit -> (@TermOver' (symbol) BuiltinValue))
            : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue))
        :=
            fun nv l =>
            match l with
            | [] => f nv
            | _::_ => @t_over symbol BuiltinValue (bv_error)
            end
        .

        Definition liftUnary
            (f : MyUnit -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue))
            : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue))
        :=
            fun nv l =>
            match l with
            | [] => @t_over symbol BuiltinValue (bv_error)
            | x1::[] => f nv x1
            | _::_::_ => @t_over symbol BuiltinValue (bv_error)
            end
        .

        Definition liftBinary
            (f : MyUnit -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue))
            : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue))
        :=
            fun nv l =>
            match l with
            | [] => @t_over symbol BuiltinValue (bv_error)
            | _::[] => @t_over symbol BuiltinValue (bv_error)
            | x1::x2::[] => f nv x1 x2
            | _::_::_::_ => @t_over symbol BuiltinValue (bv_error)
            end
        .

        Definition liftTernary
            (f : MyUnit -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue))
            : (MyUnit -> list (@TermOver' (symbol) BuiltinValue) -> (@TermOver' (symbol) BuiltinValue))
        :=
            fun nv l =>
            match l with
            | [] => @t_over symbol BuiltinValue (bv_error)
            | _::[] => @t_over symbol BuiltinValue (bv_error)
            | _::_::[] => @t_over symbol BuiltinValue (bv_error)
            | x1::x2::x3::[] => f nv x1 x2 x3
            | _::_::_::_::_ => @t_over symbol BuiltinValue (bv_error)
            end
        .

        #[local]
        Instance β
            : Builtin MyUnit
        := {|
            builtin_value
                := BuiltinValue ;

            builtin_function_symbol
                := FunctionSymbol;

            builtin_function_interp
                := fun p =>
                match p with
                (* nulary *)
                | b_false => liftNulary (
                        fun _ => t_over (bv_bool false)
                    )
                | b_true => liftNulary (
                        fun _ => t_over (bv_bool true)
                    )
                | b_zero => liftNulary (
                        fun _ => t_over (bv_Z 0)
                    )
                | b_list_empty =>  liftNulary (
                        fun _ => (t_over (bv_list nil))
                    )
                | b_map_empty =>  liftNulary (
                        fun _ => (t_over (bv_pmap ∅))
                    )
                (* unary *)
                | b_isBuiltin => liftUnary (
                    fun _ v => bfmap1 impl_isBuiltin v
                ) 
                | b_isError => liftUnary (
                    fun _ v =>
                    match v with
                    | t_over x => t_over (bv_bool (impl_isError x))
                    | _ => t_over (bv_bool false)
                    end
                )
                | b_isBool => liftUnary (
                    fun _ v =>
                    match v with
                    | t_over x => t_over (bv_bool (impl_isBool x))
                    | _ => t_over (bv_bool false)
                    end
                )
                    
                | b_isString => liftUnary (
                    fun _ v =>
                    match v with
                    | t_over x => t_over (bv_bool (impl_isString x))
                    | _ => t_over (bv_bool false)
                    end
                )
                    
                | b_isList => liftUnary (
                    fun _ v =>
                    match v with
                    | t_over x => t_over (bv_bool (impl_isList x))
                    | _ => t_over (bv_bool false)
                    end
                )
                    
                | b_isMap => liftUnary (
                    fun _ v =>
                    match v with
                    | t_over x => t_over (bv_bool (impl_isMap x))
                    | _ => t_over (bv_bool false)
                    end
                )

                | b_bool_neg => liftUnary (
                    fun _ v =>
                    bfmap_bool__bool negb v
                )
                
                | b_isZ => liftUnary (
                    fun _ v =>
                    match v with
                    | t_over x => t_over (bv_bool (impl_isZ x))
                    | _ => t_over (bv_bool false)
                    end
                )
                    
                
                | b_map_size => liftUnary (
                    fun _ v =>
                    match v with
                    | t_over (bv_pmap m) => (t_over (bv_Z (Z.of_nat (size m))))
                    | _ => err
                    end
                )

                (* binary *)
                | b_eq => liftBinary (
                    fun _ v1 v2 =>
                    t_over (bv_bool (bool_decide (v1 = v2)))
                )
                | b_and => liftBinary (
                    fun _ v1 v2 =>
                    bfmap_bool_bool__bool andb v1 v2
                )
                    
                | b_or => liftBinary (
                    fun _ v1 v2 =>
                    bfmap_bool_bool__bool orb v1 v2
                )
                | b_iff => liftBinary (
                    fun _ v1 v2 =>
                    bfmap_bool_bool__bool eqb v1 v2
                )
                | b_xor => liftBinary (
                    fun _ v1 v2 =>
                    bfmap_bool_bool__bool xorb v1 v2
                )
                | b_Z_isLe => liftBinary (
                    fun _ v1 v2 =>
                    bfmap_Z_Z__bool Z.leb v1 v2
                )
                | b_Z_isLt => liftBinary (
                    fun _ v1 v2 =>
                    bfmap_Z_Z__bool Z.ltb v1 v2
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
                    | t_over (bv_Z (0)) => err
                    | _ => bfmap_Z_Z__Z Z.div v1 v2
                    end
                )
                | b_map_hasKey => liftBinary (
                    fun _ v1 v2 =>
                    match v1 with
                    | t_over (bv_pmap m) =>
                        let p := my_encode (v2) in
                        match m !! p with
                        | Some _ => (t_over (bv_bool true))
                        | None => (t_over (bv_bool false))
                        end
                    | _ => err
                    end
                )
                | b_map_lookup => liftBinary (
                    fun _ v1 v2 =>
                    match v1 with
                    | t_over (bv_pmap m) =>
                        let p := my_encode (v2) in
                        match m !! p with
                        | Some v => (prettify v)
                        | None => err
                        end
                    | _ => err
                    end
                )
                    
                | b_have_same_symbol => liftBinary (
                    fun _ v1 v2 =>
                    match v1 with
                    | t_term s1 _ =>
                        match v2 with
                        | t_term s2 _ => (t_over (bv_bool (bool_decide (s1 = s2))))
                        | _ => t_over (bv_bool false)
                        end
                    | _ => t_over (bv_bool false)
                    end
                )
                    
                | b_is_applied_symbol => liftBinary (
                    fun _ v1 v2 =>
                    match v1 with
                    | t_over (bv_sym s) =>
                        match v2 with
                        | t_term s' _ => (t_over (bv_bool (bool_decide (s' = s))))
                        | _ => (t_over (bv_bool false))
                        end
                    | _ => (t_over (bv_bool false))
                    end
                )

                (* ternary *)
                | b_map_update => liftTernary (
                    fun _ v1 v2 v3 =>
                    match v1 with
                    | t_over (bv_pmap m) =>
                        let p := my_encode (v2) in
                        let m' := <[ p := (uglify' v3) ]>m in
                        t_over (bv_pmap m')
                    | _ => err
                    end
                )
                end ;
        |}.

    End sec.


    Module Notations.
        
        
        Notation "'true'" := ( (e_fun b_true []))
            : RuleScope
        .

        Notation "'false'" := ( (e_fun b_false []))
            : RuleScope
        .
    
        Notation "b1 '&&' b2" :=
            ( (e_fun default_builtin.b_and
                [b1;
                b2]
            ))
            : RuleScope
        .

        Notation "b1 '||' b2" :=
            ( (e_fun default_builtin.b_or
                [b1; b2]
            ))
            : RuleScope
        .

        Notation "~~ b" :=
            ( (e_fun default_builtin.b_bool_neg [b]))
        .

        Notation "'isBool' t" :=
            ( (e_fun
                b_isBool
                [(t)]
            ))
            (at level 90)
        .        

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

        Notation "'(' x '==Z' y ')'" :=
            ((e_fun b_eq [(x); (y)]))
        .

        Notation "'(' x '==Bool' y ')'" :=
            ((e_fun b_eq [(x); (y)]))
        .

        Notation "'(' x '==Gen' y ')'" :=
            ((e_fun b_eq [(x); (y)]))
        .


        Notation "<opaque map>" := (bv_pmap (PNodes _)) (only printing).

    End Notations.

End default_builtin.


Definition isAppliedSymbol (s:string) (e : @Expression2 (default_model (default_builtin.β))) :=
    let M := ( default_model (default_builtin.β)) in
    (@e_fun M
        default_builtin.b_is_applied_symbol
        [
            (@e_ground (M) (t_over (bv_sym s)));
            (e)
        ]
    )
.

Definition builtins_binding : BuiltinsBinding := {|
    bb_function_names := [
        ("bool.neg", "b_bool_neg");
        ("bool.and", "b_and");
        ("bool.or", "b_or");
        ("bool.eq", "b_eq");
        ("bool.false", "b_false");
        ("bool.true", "b_true");
        ("bool.is", "b_isBool");
        ("term.same_symbol", "b_have_same_symbol");
        ("z.minus", "b_Z_minus");
        ("z.plus", "b_Z_plus");
        ("z.is", "b_isZ");
        ("z.eq", "b_eq");
        ("z.le", "b_Z_isLe");
        ("z.lt", "b_Z_isLt");
        ("string.is", "b_isString");
        ("map.hasKey", "b_map_hasKey");
        ("map.lookup", "b_map_lookup");
        ("map.size", "b_map_size");
        ("map.empty", "b_map_empty");
        ("map.update", "b_map_update")
    ];
|}.