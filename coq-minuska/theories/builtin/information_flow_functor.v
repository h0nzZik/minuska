From Minuska Require Import
    prelude
    spec
    model_algebra
    model_traits
.

From stdpp Require Import decidable.

Class IFCRelaxedModelTrait
    (TagType : Type)
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    (Morig : RelaxedModel signature NondetValue FromT)
    (Miflow : RelaxedModel signature NondetValue FromT)
:= {
    ifc_tagged : @rm_carrier _ _ _ _ _ Morig -> gset TagType -> @rm_carrier _ _ _ _ _ Miflow ;
    ifc_get_tags : @rm_carrier _ _ _ _ _ Miflow -> gset TagType ;
    ifc_get_pure : @rm_carrier _ _ _ _ _ Miflow -> @rm_carrier _ _ _ _ _ Morig ;

    ifc_get_tags_of_tagged :
        forall c tags,
            ifc_get_tags (ifc_tagged c tags) = tags ;
    
    ifc_get_pure_of_tagged :
        forall c tags,
            ifc_get_pure (ifc_tagged c tags) = c ;
}.

Program Definition information_flow_functor
    (TagType : Type)
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    :
    RelaxedModelFunctorT void
:= {|
    rmf_signature := fun signature => signature ;
    rmf_nondet := fun ND => ND ;

    rmf_model :=
        fun (signature : Signature)
            (NondetValue : Type)
            (symbol : Type)
            (symbols : Symbols symbol)
            M
        => 
        {|
            rm_carrier := ((rm_carrier _ _ _ M)*(gset TagType)) ;
            rm_model_over :=
                fun
                    (Carrier : Type)
                    (inja : Injection void Carrier)
                    (injb : ReversibleInjection _ Carrier)
                =>
                let myinj := (rinj_compose injb ({| 
                    ri_injection := {| inject := fun a => (a,∅) |} ;
                    ri_reverse := fun b => Some b.1
                |})) in
                {|
                    builtin_function_interp :=
                        fun
                            (f : @builtin_function_symbol signature)
                            (nv : NondetValue)
                            l
                        =>  @spec.builtin_function_interp _ _ _ _ _
                            (@rm_model_over _ _ _ _ _ M Carrier inja 
                                myinj
                            )
                            f
                            nv
                            l
                    ;

                    builtin_predicate_interp :=
                        fun
                            (p : @builtin_predicate_symbol signature)
                            (nv : NondetValue)
                            l
                        =>  @spec.builtin_predicate_interp _ _ _ _ _
                            (@rm_model_over _ _ _ _ _ M Carrier inja 
                                myinj
                            )
                            p
                            nv
                            l
                    ;
                |}
        |}  ;
|}.
Next Obligation.
    intros.
    (* Search RelDecision prod. *)
    ltac1:(unshelve(eapply prod_eq_dec)).
    apply rm_carrier_eqdec.
Defined.
Next Obligation.
    intros. simpl in *. ltac1:(simplify_eq/=). reflexivity.
Qed.
Fail Next Obligation.

