From Minuska Require Import
    prelude
    spec
    model_functor
    model_traits
    list_signature
    model_algebra
.


#[local]
Instance list_model_functor : CarrierFunctorT := {|
    cf_carrier := list ;
|}.

Definition list_function_interp
    (InnerT : Type)
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    {_WE : WithErrTrait Carrier}
    {_WB : WithBoolTrait Carrier}
    {_WL : WithListTrait InnerT Carrier}
    (asi : Carrier -> option (InnerT))
    (asl : Carrier -> option (list InnerT))
:
    ListFunSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    @TermOver' symbol  Carrier
:=
    fun f nd args =>
    match f with
    | list_nil =>
        match args with
        | [] => t_over (wlt_inject_list [])
        | _ => t_over wet_error
        end
    | list_cons =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1), (asl x2) with
            | Some v, Some l => t_over (wlt_inject_list (v::l))
            | _, _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | list_head =>
        match args with
        | (t_over x1)::[] =>
            match asl x1 with
            | Some [] => t_over wet_error
            | Some (h::_) => t_over (wlt_inject_inner h)
            | _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | list_tail =>
        match args with
        | (t_over x1)::[] =>
            match asl x1 with
            | Some [] => t_over wet_error
            | Some (_::t) => t_over (wlt_inject_list t)
            | _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    | list_is_nil =>
        match args with
        | (t_over x1)::[] =>
            match (asl x1) with
            | Some l => t_over (wbt_inject_bool (bool_decide (l = [])))
            | _ => t_over wet_error
            end
        | _ => t_over wet_error
        end
    end
.

Definition list_predicate_interp
    (InnerT : Type)
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    {_WE : WithErrTrait Carrier}
    {_WB : WithBoolTrait Carrier}
    {_WL : WithListTrait InnerT Carrier}
    (asi : Carrier -> option (InnerT))
    (asl : Carrier -> option (list InnerT))
:
    ListPredSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    bool
:=
    fun p nd args =>
    match p with
    | list_is =>
        match args with
        | (t_over x1)::[] =>
            match (asl x1) with
            | Some _ => true
            | _ => false
            end
        | _ => false
        end
    end
.

Definition list_model_over
    (InnerT : Type)
    {symbol : Type}
    {symbols : Symbols symbol}
    (NondetValue : Type)
    (Carrier : Type)
    {_WE : WithErrTrait Carrier}
    {_WB : WithBoolTrait Carrier}
    {_WL : WithListTrait InnerT Carrier}
    (asi : Carrier -> option (InnerT))
    (asl : Carrier -> option (list InnerT))
    :
    @ModelOver symbol symbols list_signature NondetValue Carrier
:= {|
    builtin_function_interp := fun (f : @builtin_function_symbol list_signature) => list_function_interp InnerT NondetValue Carrier asi asl f;
    builtin_predicate_interp := fun (p : @builtin_predicate_symbol list_signature) => list_predicate_interp InnerT NondetValue Carrier asi asl p;
|}.

Variant simple_list_carrier (Inner : Type) :=
| slc_inner (x : Inner)
| slc_list (l : list Inner)
.

#[local]
Instance simple_list_carrier__eqdec
    (Inner : Type)
    {_ : EqDecision Inner}
    : EqDecision (simple_list_carrier Inner)
.
Proof.
    ltac1:(solve_decision).
Defined.

#[local]
Instance slc_carfun : CarrierFunctorT := {|
    cf_carrier := simple_list_carrier ;
|}.

#[local]
Instance lift_wet
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    (my_signature : Signature)
    (M : Model my_signature NondetValue)
    {_WET : WithErrTrait (spec.builtin_value M)}
 :
    WithErrTrait (simple_list_carrier (builtin_value M))
:= {|
    wet_error := slc_inner (spec.builtin_value M) model_traits.wet_error
|}.


#[local]
Program Instance lift_wbt
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    (my_signature : Signature)
    (M : Model my_signature NondetValue)
    {_WBT : WithBoolTrait (spec.builtin_value M)}
 :
    WithBoolTrait (simple_list_carrier (builtin_value M))
:= {|
    wbt_inject_bool := (slc_inner (spec.builtin_value M)) ∘ model_traits.wbt_inject_bool
|}.
Next Obligation.
    unfold compose in H.
    inversion H; subst; clear H.
    apply (inj _) in H1.
    apply H1.
Qed.
Fail Next Obligation.

#[local]
Program Instance wlt (Inner : Type)
    :
    WithListTrait Inner (simple_list_carrier Inner)
:= {|
    wlt_inject_inner := slc_inner Inner ;
    wlt_inject_list := slc_list Inner ;
|}.
Next Obligation.
    inversion H; subst; clear H.
    reflexivity.
Qed.
Next Obligation.
    inversion H; subst; clear H.
    reflexivity.
Qed.
Fail Next Obligation.


Definition simple_list_functor
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    :
    forall (my_signature : Signature)
        (M : Model my_signature NondetValue),
        WithErrTrait ((spec.builtin_value M)) ->
        WithBoolTrait ((spec.builtin_value M)) ->
        Model list_signature NondetValue
:= fun my_signature M _WE _WB =>
{|
    builtin_value :=
        simple_list_carrier (spec.builtin_value M)
    ;
    builtin_model_over :=
        list_model_over
            (spec.builtin_value M)
            NondetValue
            (simple_list_carrier (spec.builtin_value M))
            (λ x, match x with slc_inner _ x' => Some x' | _ => None end)
            (λ x, match x with slc_list _ x' => Some x' | _ => None end)
    ;
|}
.
