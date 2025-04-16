From Minuska Require Import
    prelude
    spec
    bool_model
    int_signature
    model_traits
    model_algebra
    (* model_functor *)
.

Definition int_carrier := Z.

Definition int_function_interp
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    {_WE : Injection ErrT Carrier}
    {_WB : Injection bool Carrier}
    {_WI : Injection Z Carrier}
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
            | Some z1, Some z2 => t_over (inject Z Carrier (z1 + z2)%Z)
            | _, _ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | int_minus =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1), (asi x2) with
            | Some z1, Some z2 => t_over (inject Z Carrier (z1 - z2)%Z)
            | _, _ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | int_uminus =>
        match args with
        | (t_over x1)::[] =>
            match (asi x1) with
            | Some z1 => t_over (inject Z Carrier (-z1)%Z)
            | _ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | int_zero =>
        match args with
        | [] => t_over (inject Z Carrier 0%Z)
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | int_one =>
        match args with
        | [] => t_over (inject Z Carrier 1%Z)
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | int_eq =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => t_over (inject bool Carrier (bool_decide (z1 = z2)%Z))
            | _, _ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | int_le =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => t_over (inject bool Carrier (bool_decide (z1 <= z2)%Z))
            | _, _ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
        end
    | int_lt =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => t_over (inject bool Carrier (bool_decide (z1 < z2)%Z))
            | _, _ => t_over (inject ErrT Carrier et_error)
            end
        | _ => t_over (inject ErrT Carrier et_error)
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
    (_WE : Injection ErrT Carrier)
    (_WB : Injection bool Carrier)
    (_WI : Injection Z Carrier)
    (asi : Carrier -> option int_carrier)
    :
    @ModelOver symbol symbols int_signature NondetValue Carrier
:= {|
    builtin_function_interp := fun (f : @builtin_function_symbol int_signature) => int_function_interp NondetValue Carrier asi f;
    builtin_predicate_interp := fun (p : @builtin_predicate_symbol int_signature) => int_predicate_interp NondetValue Carrier asi p;
|}.

Definition int_relaxed_model
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    :
    RelaxedModel int_signature NondetValue (ErrT+bool)
:= {|
    rm_carrier := int_carrier ;
    rm_model_over :=
        fun (Carrier : Type)
            (inja : Injection (ErrT+bool) Carrier)
            (injb : ReversibleInjection int_carrier Carrier)
            => int_model_over symbol symbols NondetValue Carrier
                {| inject := fun (e:ErrT) => @inject _ _ inja (inl e) |}
                {| inject := fun (b:bool) => @inject _ _ inja (inr b) |}
                (@ri_injection _ _ injb)
                (@ri_reverse _ _ injb)
|}.

(* Definition int_model
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    : Model int_signature NondetValue
:=
    model_of_relaxed (int_relaxed_model symbol symbols NondetValue)
. *)

