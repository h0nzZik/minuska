From Minuska Require Import
    prelude
    spec
    model_functor
    model_traits
    list_signature
    model_algebra
    (* model_functor *)
.

Definition list_function_interp
    (InnerT : Type)
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    (Carrier : Type)
    (_WB : Injection bool Carrier)
    (_WI : Injection InnerT Carrier)
    (_WL : Injection (list InnerT) Carrier)
    (asi : Carrier -> option (InnerT))
    (asl : Carrier -> option (list InnerT))
:
    ListFunSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    option (@TermOver' symbol  Carrier)
:=
    fun f nd args =>
    match f with
    | list_nil =>
        match args with
        | [] => Some (t_over (inject (list InnerT) Carrier []))
        | _ => None
        end
    | list_cons =>
        match args with
        | (t_over x1)::(t_over x2)::[] =>
            match (asi x1), (asl x2) with
            | Some v, Some l => Some (t_over (inject (list InnerT) Carrier (v::l)))
            | _, _ => None
            end
        | _ => None
        end
    | list_head =>
        match args with
        | (t_over x1)::[] =>
            match asl x1 with
            | Some [] => None
            | Some (h::_) => Some (t_over (inject InnerT Carrier h))
            | _ => None
            end
        | _ => None
        end
    | list_tail =>
        match args with
        | (t_over x1)::[] =>
            match asl x1 with
            | Some [] => None
            | Some (_::t) => Some (t_over (inject (list InnerT) Carrier t))
            | _ => None
            end
        | _ => None
        end
    | list_is_nil =>
        match args with
        | (t_over x1)::[] =>
            match (asl x1) with
            | Some l => Some (t_over (inject bool Carrier (bool_decide (l = []))))
            | _ => None
            end
        | _ => None
        end
    end
.

Definition list_predicate_interp
    (InnerT : Type)
    (symbol : Type)
    (symbols : Symbols symbol)
    (NondetValue : Type)
    (Carrier : Type)
    (_WB : Injection bool Carrier)
    (_WI : Injection InnerT Carrier)
    (_WL : Injection (list InnerT) Carrier)
    (asi : Carrier -> option (InnerT))
    (asl : Carrier -> option (list InnerT))
:
    ListPredSymbol ->
    NondetValue ->
    list (@TermOver' symbol Carrier) ->
    option bool
:=
    fun p nd args =>
    match p with
    | list_is =>
        match args with
        | (t_over x1)::[] =>
            match (asl x1) with
            | Some _ => Some true
            | _ => Some false
            end
        | _ => None
        end
    end
.

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
Program Instance simple_list_carrier__countable
    (Inner : Type)
    {_ : EqDecision Inner}
    {_ : Countable Inner}
    : Countable (simple_list_carrier Inner) := {|
    encode := fun slc =>
        stdpp.countable.encode (
            match slc with
            | slc_inner _ x => inl x
            | slc_list _ l => inr l
            end
        )
    ;
    decode := fun (p : positive) =>
        match (@stdpp.countable.decode (Inner+(list Inner)) _ _ p) with
        | Some (inl x) => Some (slc_inner _ x)
        | Some (inr l) => Some (slc_list _ l)
        | None => None
        end
|}.
Next Obligation.
    rewrite decode_encode.
        ltac1:(repeat case_match; simplify_eq/=);
        reflexivity.
Qed.
Fail Next Obligation.

Program Definition list_relaxed_functor :
    RelaxedModelFunctorT (bool)
:= {|
    rmf_signature := fun _ => list_signature ;
    rmf_nondet := fun ND => ND ;

    rmf_model :=
        fun (signature : Signature)
            (NondetValue : Type)
            (symbol : Type)
            (symbols : Symbols symbol)
            M
        => 
        {|
            rm_carrier := (simple_list_carrier (rm_carrier _ _ _ M)) ;
            rm_model_over :=
                fun
                    (Carrier : Type)
                    (inja : Injection (bool) Carrier)
                    (injb : ReversibleInjection (simple_list_carrier (rm_carrier _ _ _ M)) Carrier)
                => 
                    let asi := (fun c =>
                        match (@ri_reverse _ _ injb) c with Some d => (
                            match d with
                            | slc_inner _ d' => Some d'
                            | _ => None
                            end
                        )
                        | None => None end) in
                    let asl := (fun c =>
                        match (@ri_reverse _ _ injb) c with Some d => (
                            match d with
                            | slc_list _ d' => Some d'
                            | _ => None
                            end
                        )
                        | None => None end) in
                let WL : Injection (list (rm_carrier signature NondetValue (bool) M)) Carrier := {|
                    inject := fun l => @inject _ _ (@ri_injection _ _ injb) (slc_list _ l)
                |} in
                let WI := {|
                    inject := fun i => @inject _ _ (@ri_injection _ _ injb) (slc_inner _ i)
                |} in
                let WB := {|
                    inject := fun b => @inject _ _ inja (b)                
                |} in
                {|
                    builtin_function_interp := fun (f : @builtin_function_symbol list_signature) => list_function_interp (rm_carrier _ _ _ M) symbol symbols NondetValue Carrier WB WI WL asi asl f;
                    builtin_predicate_interp := fun (p : @builtin_predicate_symbol list_signature) => list_predicate_interp (rm_carrier _ _ _ M) symbol symbols NondetValue Carrier WB WI WL asi asl p;
                |}
        |}  ;
|}.
Next Obligation.
    apply simple_list_carrier__eqdec.
    apply rm_carrier_eqdec.
Defined.
Next Obligation.
    (* Countable *)
    destruct M.
    apply _.
Defined.
Next Obligation.
    apply inject_inj in H.
    ltac1:(injection H as H).
    exact H.
Qed.
Next Obligation.
    apply inject_inj in H.
    ltac1:(injection H as H).
    exact H.
Qed.
Next Obligation.
    apply (inj (inject bool Carrier)) in H.
    exact H.
Qed.
Next Obligation.
    destruct p; simpl in *;
        ltac1:(simplify_eq/=).
Qed.
Fail Next Obligation.


