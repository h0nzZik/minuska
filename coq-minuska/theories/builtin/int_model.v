From Minuska Require Import
    prelude
    spec
    bool_model
    int_signature
    model_algebra
    (* model_functor *)
.

(* Definition int_carrier := Z. *)

Definition int_function_interp
    {TermSymbol : Type}
    (NondetValue : Type)
    (Carrier : Type)
    {_WB : Injection bool Carrier}
    {_WI : Injection Z Carrier}
    (asi : Carrier -> option Z)
:
    IntFunSymbol ->
    NondetValue ->
    list (@TermOver' TermSymbol Carrier) ->
    option (@TermOver' TermSymbol  Carrier)
:=
    fun f nd args =>
    match f with
    | int_plus =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1), (asi x2) with
            | Some z1, Some z2 => Some (t_over (inject Z Carrier (z1 + z2)%Z))
            | _, _ => None
            end
        | _ => None
        end
    | int_minus =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1), (asi x2) with
            | Some z1, Some z2 => Some (t_over (inject Z Carrier (z1 - z2)%Z))
            | _, _ => None
            end
        | _ => None
        end
    | int_uminus =>
        match args with
        | (t_over x1)::[] =>
            match (asi x1) with
            | Some z1 => Some (t_over (inject Z Carrier (-z1)%Z))
            | _ => None
            end
        | _ => None
        end
    | int_zero =>
        match args with
        | [] => Some (t_over (inject Z Carrier 0%Z))
        | _ => None
        end
    | int_one =>
        match args with
        | [] => Some (t_over (inject Z Carrier 1%Z))
        | _ => None
        end
    | int_eq =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => Some (t_over (inject bool Carrier (bool_decide (z1 = z2)%Z)))
            | _, _ => None
            end
        | _ => None
        end
    | int_le =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => Some (t_over (inject bool Carrier (bool_decide (z1 <= z2)%Z)))
            | _, _ => None
            end
        | _ => None
        end
    | int_lt =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1),(asi x2) with
            | Some z1, Some z2 => Some (t_over (inject bool Carrier (bool_decide (z1 < z2)%Z)))
            | _, _ => None
            end
        | _ => None
        end

    end
.

Definition int_predicate_interp
    {TermSymbol : Type}
    (NondetValue : Type)
    (Carrier : Type)
    (asi : Carrier -> option Z)
:
    IntPredSymbol ->
    NondetValue ->
    list (@TermOver' TermSymbol Carrier) ->
    option bool
:=
    fun p nv args =>
    match p with
    | bool_pred_is =>
        match args with
        | (t_over x1)::[] =>
            match (asi x1) with
            | Some _ => Some true
            | _ => Some false
            end
        | _ => None
        end
    end
.

Definition int_relaxed_va
    (TermSymbol : Type)
    (NondetValue : Type)
    :
    RelaxedValueAlgebra bool Z NondetValue TermSymbol int_signature.IntFunSymbol int_signature.IntPredSymbol
:= {|
    rva_over :=
        fun (Carrier : Type)
            (inja : Injection bool Carrier)
            (injb : ReversibleInjection Z Carrier)
            => {|
                builtin_function_interp := fun (f : IntFunSymbol) =>
                    int_function_interp NondetValue Carrier (injb.(ri_reverse)) f; 
                builtin_predicate_interp := fun (p : IntPredSymbol) =>
                    int_predicate_interp NondetValue Carrier (injb.(ri_reverse)) p; 
            |}
    ;
|}.


Definition int_va
    (TermSymbol : Type)
    (NondetValue : Type)
:=
    small_model_of_relaxed (int_relaxed_va TermSymbol NondetValue)
.

