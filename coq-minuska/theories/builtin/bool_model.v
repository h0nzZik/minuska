From Minuska Require Import
    prelude
    spec
    bool_signature
    model_algebra
.

(* Definition bool_carrier := bool. *)

Definition bool_function_interp
    {TermSymbol : Type}
    (NondetValue : Type)
    (Carrier : Type)
    {Cbool : Injection bool Carrier}
    (asb : Carrier -> option bool)
:
    BoolFunSymbol ->
    NondetValue ->
    list (@TermOver' TermSymbol Carrier) ->
    option (@TermOver' TermSymbol Carrier)
:=
    fun f nd args =>
    match f with
    | bool_fun_true => Some (t_over (inject bool Carrier true))
    | bool_fun_false => Some (t_over (inject bool Carrier false))
    | bool_fun_neg =>
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some true => Some (t_over (inject bool Carrier false))
            | Some false => Some (t_over (inject bool Carrier true))
            | None => None
            end
        | _ => None
        end
    | bool_fun_and =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                Some (t_over (inject bool Carrier (andb b1 b2)))
            | _,_ => None
            end
        | _ => None
        end
    | bool_fun_or =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                Some (t_over (inject bool Carrier (orb b1 b2)))
            | _,_ => None
            end
        | _ => None
        end
    | bool_fun_iff =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                Some (t_over (inject bool Carrier (eqb b1 b2)))
            | _, _ => None
            end
        | _ => None
        end
    | bool_fun_xor =>
        match args with
        | (t_over (x1))::(t_over (x2))::[] =>
            match (asb x1),(asb x2) with
            | (Some b1), (Some b2) =>
                Some (t_over (inject bool Carrier (negb (eqb b1 b2))))
            | _, _ => None
            end
        | _ => None
        end
    end
.

Definition bool_predicate_interp
    {TermSymbol : Type}
    (NondetValue : Type)
    (Carrier : Type)
    (asb : Carrier -> option bool)
:
    BoolPredSymbol ->
    NondetValue ->
    list (@TermOver' TermSymbol Carrier) ->
    option bool
:=
    fun p nv args =>
    match p with
    | bool_pred_is => 
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some _ => Some true
            | _ => Some false
            end
        | _ => None
        end
    | bool_pred_is_false =>
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some false => Some true
            | Some true => Some false
            | _ => None
            end
        | _ => None
        end
    | bool_pred_is_true =>
        match args with
        | (t_over x1)::[] =>
            match (asb x1) with
            | Some true => Some true
            | Some false => Some false
            | _ => None
            end
        | _ => None
        end
    end
.

Definition bool_relaxed_va
    (TermSymbol : Type)
    (NondetValue : Type)
    :
    RelaxedValueAlgebra void bool NondetValue TermSymbol bool_signature.BoolFunSymbol bool_signature.BoolPredSymbol
:= {|
    rva_over :=
        fun (Carrier : Type)
            (inja : Injection void Carrier)
            (injb : ReversibleInjection bool Carrier)
            => {|
                builtin_function_interp := fun (f : BoolFunSymbol) =>
                    bool_function_interp NondetValue Carrier (injb.(ri_reverse)) f; 
                builtin_predicate_interp := fun (p : BoolPredSymbol) =>
                    bool_predicate_interp NondetValue Carrier (injb.(ri_reverse)) p; 
            |}
    ;
|}.

Definition bool_va
    (TermSymbol : Type)
    (NondetValue : Type)
:=
    small_model_of_relaxed (bool_relaxed_va TermSymbol NondetValue)
.
