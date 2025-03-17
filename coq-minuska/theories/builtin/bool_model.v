From Minuska Require Import
    prelude
    spec
    bool_signature
.

Inductive bool_carrier :=
| c_bool_b (b : bool)
| c_bool_err
.

#[local]
Instance bool_carrier_eqdec : EqDecision bool_carrier.
Proof.
    ltac1:(solve_decision).
Defined.


Definition bool_function_interp
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
:
    BoolFunSymbol ->
    NondetValue ->
    list (@TermOver' symbol  bool_carrier) ->
    @TermOver' symbol  bool_carrier
:=
    fun f nd args =>
    match f with
    | bool_fun_true => t_over (c_bool_b true)
    | bool_fun_false => t_over (c_bool_b false)
    | bool_fun_neg =>
        match args with
        | (t_over (c_bool_b true))::_ => t_over (c_bool_b false)
        | (t_over (c_bool_b false))::_ => t_over (c_bool_b true)
        | _ => t_over c_bool_err
        end
    | bool_fun_and =>
        match args with
        | (t_over (c_bool_b b1))::(t_over (c_bool_b b2))::_ =>
            t_over (c_bool_b (andb b1 b2))
        | _ => t_over (c_bool_err)
        end
    | bool_fun_or =>
        match args with
        | (t_over (c_bool_b b1))::(t_over (c_bool_b b2))::_ =>
            t_over (c_bool_b (orb b1 b2))
        | _ => t_over (c_bool_err)
        end
    | bool_fun_iff =>
        match args with
        | (t_over (c_bool_b b1))::(t_over (c_bool_b b2))::_ =>
            t_over (c_bool_b (eqb b1 b2))
        | _ => t_over (c_bool_err)
        end
    | bool_fun_xor =>
        match args with
        | (t_over (c_bool_b b1))::(t_over (c_bool_b b2))::_ =>
            t_over (c_bool_b (negb (eqb b1 b2)))
        | _ => t_over (c_bool_err)
        end
    end
.

Definition bool_predicate_interp
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
:
    BoolPredSymbol ->
    NondetValue ->
    list (@TermOver' symbol  bool_carrier) ->
    bool
:=
    fun p nv args =>
    match p with
    | bool_pred_is => true
    | bool_pred_is_false =>
        match args with
        | (t_over (c_bool_b false))::_ => true
        | _ => false
        end
    | bool_pred_is_true =>
        match args with
        | (t_over (c_bool_b true))::_ => true
        | _ => false
        end
    end
.

Definition bool_model_over
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    :
    @ModelOver symbol symbols bool_signature NondetValue bool_carrier
:= {|
    builtin_function_interp := fun (f : @builtin_function_symbol bool_signature) => bool_function_interp NondetValue f;
    builtin_predicate_interp := fun (p : @builtin_predicate_symbol bool_signature) => bool_predicate_interp NondetValue p;
|}.

