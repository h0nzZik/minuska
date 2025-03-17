From Minuska Require Import
    prelude
    spec
    bool_model
    int_signature
    model_traits
.

Definition int_carrier := Z.

Definition int_function_interp
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    {_WE : WithErrTrait Carrier}
    {_WB : WithBoolTrait Carrier}
    {_WI : WithIntTrait Carrier}
    (asi : Carrier -> option int_carrier)
:
    IntFunSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    @TermOver' symbol  Carrier
:=
    fun f nd args =>
    match f with
    | int_plus =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1), (asi x2) with
            | Some z1, Some z2 => t_over (wit_inject_Z (z1 + z2)%Z)
            | _, _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | int_minus =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1), (asi x2) with
            | Some z1, Some z2 => t_over (wit_inject_Z (z1 - z2))
            | _, _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | int_uminus =>
        match args with
        | (t_over x1)::[] =>
            match (asi x1) with
            | Some z1 => t_over (wit_inject_Z z1)
            | _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | int_zero =>
        match args with
        | [] => t_over (wit_inject_Z 0)
        | _ => t_over wet_error
        end
    | int_one =>
        match args with
        | [] => t_over (wit_inject_Z 1)
        | _ => t_over wet_error
        end
    | int_eq =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => t_over (wbt_inject_bool (bool_decide (z1 = z2)))
            | _, _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | int_le =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => t_over (wbt_inject_bool (bool_decide (z1 <= z2)%Z))
            | _, _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | int_lt =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => t_over (wbt_inject_bool (bool_decide (z1 < z2)%Z))
            | _, _ => t_over wet_error
            end
        | _ => t_over wet_error
        end

    end
.

Definition int_predicate_interp
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    (asi : Carrier -> option int_carrier)
:
    IntPredSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    bool
:=
    fun p nv args =>
    match p with
    | bool_pred_is =>
        match args with
        | (t_over x1)::[] =>
            match (asi x1) with
            | Some _ => true
            | _ => false
            end
        | _ => false
        end
    end
.

Definition int_model_over
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    (Carrier : Type)
    {Cint : WithIntTrait Carrier}
    {Cbool : WithBoolTrait Carrier}
    {Cerr : WithErrTrait Carrier}
    (asi : Carrier -> option int_carrier)
    :
    @ModelOver symbol symbols int_signature NondetValue Carrier
:= {|
    builtin_function_interp := fun (f : @builtin_function_symbol int_signature) => int_function_interp NondetValue Carrier asi f;
    builtin_predicate_interp := fun (p : @builtin_predicate_symbol int_signature) => int_predicate_interp NondetValue Carrier asi p;
|}.


Inductive simple_int_carrier :=
| sic_bool (b : bool_carrier)
| sic_int (i : int_carrier)
| sic_err
.

#[local]
Instance simple_int_carrier__eqdec
    : EqDecision simple_int_carrier
.
Proof.
    ltac1:(solve_decision).
Defined.

#[local]
Program Instance simple_int_carrier__with_int_trait
    : WithIntTrait simple_int_carrier
:= {|
    wit_inject_Z := fun i => (sic_int i) ;
|}.
Next Obligation.
    inversion H; reflexivity.
Qed.
Fail Next Obligation.

#[local]
Program Instance simple_int_carrier__with_bool_trait
    : WithBoolTrait simple_int_carrier
:= {|
    wbt_inject_bool := fun b => (sic_bool b) ;
|}.
Next Obligation.
    inversion H; reflexivity.
Qed.
Fail Next Obligation.

#[local]
Instance simple_int_carrier__with_err_trait
    : WithErrTrait simple_int_carrier
:= {|
    wet_error := sic_err;
|}.

(* from here down it does not compose *)
Definition simple_int_model
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    :
    Model int_signature NondetValue
:= {|
    builtin_value := simple_int_carrier ;
    builtin_model_over := int_model_over symbol symbols NondetValue simple_int_carrier (fun x => match x with sic_int i => Some i | _ => None end);
|}.


