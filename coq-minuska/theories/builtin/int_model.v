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


