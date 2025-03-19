From Minuska Require Import
    prelude
    spec
    bool_signature
    model_traits
    model_algebra
    (* model_functor *)
.

Definition bool_carrier := bool.
(* 
#[export]
Instance bool_carrier__with_bool_trait
    :
    WithBoolTrait bool_carrier
:= {|
    wbt_inject_bool := fun x => x ;
|}. *)

Definition bool_function_interp
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    {Cbool : Injection bool Carrier}
    {Cerr : Injection ErrT Carrier}
    (asb : Carrier -> option bool)
:
    BoolFunSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    @TermOver' symbol Carrier
:=
    fun f nd args =>
    match f with
    | bool_fun_true => t_over (inject bool Carrier true)
    | bool_fun_false => t_over (inject bool Carrier false)
    | bool_fun_neg =>
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some true => t_over (inject bool Carrier false)
            | Some false => t_over (inject bool Carrier true)
            | None => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | bool_fun_and =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                t_over (inject bool Carrier (andb b1 b2))
            | _,_ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | bool_fun_or =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                t_over (inject bool Carrier (orb b1 b2))
            | _,_ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | bool_fun_iff =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                t_over (inject bool Carrier (eqb b1 b2))
            | _, _ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | bool_fun_xor =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                t_over (inject bool Carrier (negb (eqb b1 b2)))
            | _, _ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
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
    (Cbool : Injection bool Carrier)
    (Cerr : Injection ErrT Carrier)
    (asb : Carrier -> option bool)
    :
    @ModelOver symbol symbols bool_signature NondetValue Carrier
:= {|
    builtin_function_interp := fun (f : @builtin_function_symbol bool_signature) => bool_function_interp NondetValue Carrier asb f;
    builtin_predicate_interp := fun (p : @builtin_predicate_symbol bool_signature) => bool_predicate_interp NondetValue Carrier asb p;
|}.

Definition bool_relaxed_model
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    :
    RelaxedModel bool_signature NondetValue ErrT
:= {|
    rm_carrier := bool_carrier ;
    rm_model_over :=
        fun (Carrier : Type)
            (inja : Injection ErrT Carrier)
            (injb : ReversibleInjection bool_carrier Carrier)
            => bool_model_over symbol symbols NondetValue Carrier
                (@ri_injection _ _ injb)
                inja
                (@ri_reverse _ _ injb)
|}.

Definition bool_model
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
:=
    model_of_relaxed (bool_relaxed_model symbol symbols NondetValue)
.