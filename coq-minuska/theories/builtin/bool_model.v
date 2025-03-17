From Minuska Require Import
    prelude
    spec
    bool_signature
    model_traits
.

Definition bool_carrier := bool.

#[export]
Instance bool_carrier__with_bool_trait
    :
    WithBoolTrait bool_carrier
:= {|
    wbt_inject_bool := fun x => x ;
|}.

Definition bool_function_interp
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    {Cbool : WithBoolTrait Carrier}
    {Cerr : WithErrTrait Carrier}
    (asb : Carrier -> option bool)
:
    BoolFunSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    @TermOver' symbol Carrier
:=
    fun f nd args =>
    match f with
    | bool_fun_true => t_over (wbt_inject_bool true)
    | bool_fun_false => t_over (wbt_inject_bool false)
    | bool_fun_neg =>
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some true => t_over (wbt_inject_bool false)
            | Some false => t_over (wbt_inject_bool true)
            | None => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | bool_fun_and =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                t_over (wbt_inject_bool (andb b1 b2))
            | _,_ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | bool_fun_or =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                t_over (wbt_inject_bool (orb b1 b2))
            | _,_ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | bool_fun_iff =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                t_over (wbt_inject_bool (eqb b1 b2))
            | _, _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | bool_fun_xor =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                t_over (wbt_inject_bool (negb (eqb b1 b2)))
            | _, _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    end
.

Definition bool_predicate_interp
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    (asb : Carrier -> option bool)
:
    BoolPredSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    bool
:=
    fun p nv args =>
    match p with
    | bool_pred_is => 
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some _ => true
            | _ => false
            end
        | _ => false
        end
    | bool_pred_is_false =>
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some false => true
            | _ => false
            end
        | _ => false
        end
    | bool_pred_is_true =>
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some true => true
            | _ => false
            end
        | _ => false
        end
    end
.

Definition bool_model_over
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    (Carrier : Type)
    {Cbool : WithBoolTrait Carrier}
    {Cerr : WithErrTrait Carrier}
    (asb : Carrier -> option bool)
    :
    @ModelOver symbol symbols bool_signature NondetValue Carrier
:= {|
    builtin_function_interp := fun (f : @builtin_function_symbol bool_signature) => bool_function_interp NondetValue Carrier asb f;
    builtin_predicate_interp := fun (p : @builtin_predicate_symbol bool_signature) => bool_predicate_interp NondetValue Carrier asb p;
|}.


Definition simple_bool_carrier := option bool_carrier.

#[local]
Instance simple_bool_carrier__with_bool_trait
    : WithBoolTrait simple_bool_carrier
:= {|
    wbt_inject_bool := fun b => (Some b) ;
|}.

#[local]
Instance simple_bool_carrier__with_err_trait
    : WithErrTrait simple_bool_carrier
:= {|
    wet_error := None ;
|}.

(* from here down it does not compose *)
Definition simple_bool_model
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    :
    Model bool_signature NondetValue
:= {|
    builtin_value := simple_bool_carrier ;
    builtin_model_over := bool_model_over symbol symbols NondetValue simple_bool_carrier (fun x => x);
|}.

