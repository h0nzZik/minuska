From Minuska Require Import
    prelude
    spec
    model_algebra
    model_traits
.

From stdpp Require Import decidable.

Class IFLattice (TagType : Type) := {
    ifl_meet :
        TagType -> TagType -> TagType
    ;
    ifl_meet_assoc ::
        Assoc (=) ifl_meet
    ;
    ifl_meet_comm ::
        Comm (=) ifl_meet
    ;

    ifl_join :
        TagType -> TagType -> TagType
    ;
    ifl_join_assoc ::
        Assoc (=) ifl_join
    ;
    ifl_join_comm ::
        Comm (=) ifl_join
    ;

    ifl_absorb_1 :
        forall a b, ifl_join a (ifl_meet a b) = a
    ;

    ifl_absorb_2 :
        forall a b, ifl_meet a (ifl_join a b) = a
    ;

    ifl_bot : TagType ;

    ifl_join_bot :
        forall a,
        ifl_join ifl_bot a = a
    ;

    ifl_top : TagType ; 

    ifl_meet_top :
        forall a,
        ifl_meet ifl_top a = a
    ;
}.


Class IFCRelaxedModelTrait0
    (TagType : Type)
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EF : EqDecision FromT}
    (Morig : RelaxedModel signature NondetValue FromT)
    (Miflow : RelaxedModel signature NondetValue FromT)
:= {
    ifc_tagged :
        @rm_carrier _ _ _ _ _ Morig ->
        gset TagType ->
        @rm_carrier _ _ _ _ _ Miflow
    ;
    ifc_get_tags :
        @rm_carrier _ _ _ _ _ Miflow ->
        gset TagType
    ;
    ifc_get_pure :
        @rm_carrier _ _ _ _ _ Miflow ->
        @rm_carrier _ _ _ _ _ Morig
    ;

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
    ltac1:(unshelve(eapply prod_eq_dec)).
    apply rm_carrier_eqdec.
Defined.
Next Obligation.
    intros. simpl in *. ltac1:(simplify_eq/=). reflexivity.
Qed.
Fail Next Obligation.

Definition information_flow_functor_tagged
    (TagType : Type)
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    (M : @RelaxedModel symbol symbols signature NondetValue void)
    (c : @rm_carrier _ _ _ _ _ M)
    (tags : gset TagType)
    :
    @rm_carrier _ _ _ _ _ (rmf_apply (information_flow_functor TagType) M)
:=
     (c,tags)
.

Definition information_flow_functor_get_tags
    (TagType : Type)
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    (M : @RelaxedModel symbol symbols signature NondetValue void)
    (c' : @rm_carrier _ _ _ _ _ (rmf_apply (information_flow_functor TagType) M))
    :
    gset TagType
:=
    c'.2
.

Definition information_flow_functor_get_pure
    (TagType : Type)
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    (M : @RelaxedModel symbol symbols signature NondetValue void)
    (c' : @rm_carrier _ _ _ _ _ (rmf_apply (information_flow_functor TagType) M))
    :
    @rm_carrier _ _ _ _ _ M
:=
    c'.1
.

#[export]
Program Instance information_flow_functor_trait
    (TagType : Type)
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    (M : @RelaxedModel symbol symbols signature NondetValue void)
    :
    IFCRelaxedModelTrait0 TagType M (rmf_apply (information_flow_functor TagType) M)
:= {|
    ifc_tagged := information_flow_functor_tagged TagType M ;
    ifc_get_tags := information_flow_functor_get_tags TagType M;
    ifc_get_pure := information_flow_functor_get_pure TagType M;
|}.
Next Obligation.
    intros.
    simpl.
    reflexivity.
Qed.
Next Obligation.
    intros.
    simpl.
    reflexivity.
Qed.
Fail Next Obligation.

Definition eval_predicate_in_orig
    {TagType : Type}
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EF : EqDecision FromT}
    {Morig : RelaxedModel signature NondetValue FromT}
    {Miflow : RelaxedModel signature NondetValue FromT}
    (trait0 : IFCRelaxedModelTrait0 TagType Morig Miflow)
    (Carrier : Type)
    (inja : Injection FromT Carrier)
    (injb : ReversibleInjection (@rm_carrier _ _ _ _ _ Morig) Carrier)
    (p : builtin_predicate_symbol)
    (nv : NondetValue)
    (args : list (TermOver' (@rm_carrier _ _ _ _ _ Miflow)))
:=
    let args' : list (TermOver' (@rm_carrier _ _ _ _ _ Morig)) := (list_fmap _ _ (TermOver'_map ifc_get_pure) args) in
    let args'' : list (TermOver' Carrier) := list_fmap _ _ (TermOver'_map (@inject _ _ (@ri_injection _ _ injb))) args' in
    @builtin_predicate_interp _ _ _ _ _ (@rm_model_over _ _ signature _ _ Morig Carrier inja injb) p nv args''
.

Definition eval_predicate_in_iflow
    {TagType : Type}
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EF : EqDecision FromT}
    {Morig : RelaxedModel signature NondetValue FromT}
    {Miflow : RelaxedModel signature NondetValue FromT}
    (trait0 : IFCRelaxedModelTrait0 TagType Morig Miflow)
    (Carrier : Type)
    (inja : Injection FromT Carrier)
    (injb : ReversibleInjection (@rm_carrier _ _ _ _ _ Miflow) Carrier)
    (p : builtin_predicate_symbol)
    (nv : NondetValue)
    (args : list (TermOver' (@rm_carrier _ _ _ _ _ Miflow)))
:=
    let args' := (TermOver'_map (@inject _ _ (@ri_injection _ _ injb))) <$> args in
    @builtin_predicate_interp _ _ _ _ _ (@rm_model_over _ _ signature _ _ Miflow Carrier inja injb) p nv args'
.


Definition eval_function_in_orig
    {TagType : Type}
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EF : EqDecision FromT}
    {Morig : RelaxedModel signature NondetValue FromT}
    {Miflow : RelaxedModel signature NondetValue FromT}
    (trait0 : IFCRelaxedModelTrait0 TagType Morig Miflow)
    (Carrier : Type)
    (inja : Injection FromT Carrier)
    (injb : ReversibleInjection (@rm_carrier _ _ _ _ _ Morig) Carrier)
    (f : builtin_function_symbol)
    (nv : NondetValue)
    (args : list (TermOver' (@rm_carrier _ _ _ _ _ Miflow)))
    :
    TermOver' Carrier
:=
    let args' : list (TermOver' (@rm_carrier _ _ _ _ _ Morig)) := (list_fmap _ _ (TermOver'_map ifc_get_pure) args) in
    let args'' : list (TermOver' Carrier) := list_fmap _ _ (TermOver'_map (@inject _ _ (@ri_injection _ _ injb))) args' in
    @builtin_function_interp _ _ _ _ _ (@rm_model_over _ _ signature _ _ Morig Carrier inja injb) f nv args''
.

Definition eval_function_in_iflow
    {TagType : Type}
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EF : EqDecision FromT}
    {Morig : RelaxedModel signature NondetValue FromT}
    {Miflow : RelaxedModel signature NondetValue FromT}
    (trait0 : IFCRelaxedModelTrait0 TagType Morig Miflow)
    (Carrier : Type)
    (inja : Injection FromT Carrier)
    (injb : ReversibleInjection (@rm_carrier _ _ _ _ _ Miflow) Carrier)
    (f : builtin_function_symbol)
    (nv : NondetValue)
    (args : list (TermOver' (@rm_carrier _ _ _ _ _ Miflow)))
    :
    TermOver' Carrier
:=
    let args' := (TermOver'_map (@inject _ _ (@ri_injection _ _ injb))) <$> args in
    @builtin_function_interp _ _ _ _ _ (@rm_model_over _ _ signature _ _ Miflow Carrier inja injb) f nv args'
.


(* TODO need "the rest" of the natural transformation *)
Class IFCRelaxedModelTrait1
    (TagType : Type)
    {_SL : IFLattice TagType}
    {_E : EqDecision TagType}
    {_C : Countable TagType}
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EF : EqDecision FromT}
    (Morig : RelaxedModel signature NondetValue FromT)
    (Miflow : RelaxedModel signature NondetValue FromT)
:= {

    ifc_0 :: IFCRelaxedModelTrait0 TagType Morig Miflow ;

    ifc_pure_predicate:
        forall
            (Carrier Carrier' : Type)
            (inja : Injection FromT Carrier)
            (inja' : Injection FromT Carrier')
            (injb : ReversibleInjection (@rm_carrier _ _ _ _ _ Morig) Carrier)
            (injb' : ReversibleInjection (@rm_carrier _ _ _ _ _ Miflow) Carrier'),
        forall
            (p : builtin_predicate_symbol)
            (nv : NondetValue)
            args,
        eval_predicate_in_iflow ifc_0 Carrier' inja' injb' p nv args
        =
        eval_predicate_in_orig ifc_0 Carrier inja injb p nv args
    ;

    ifc_pure_function:
        forall
            (Carrier Carrier' : Type)
            (inja : Injection FromT Carrier)
            (inja' : Injection FromT Carrier')
            (injb : ReversibleInjection (@rm_carrier _ _ _ _ _ Morig) Carrier)
            (injb' : ReversibleInjection (@rm_carrier _ _ _ _ _ Miflow) Carrier'),
        forall
            (f : builtin_function_symbol)
            (nv : NondetValue)
            args,
        let r1 := eval_function_in_iflow ifc_0 Carrier' inja' injb' f nv args in
        let r2 := eval_function_in_orig ifc_0 Carrier inja injb f nv args in
        (* TODO we need to relate the two somehow *)
        True
        (* match @ri_reverse _ _ injb r1, ri_reverse r2 with
        | Some r'1, Some r'2 => False
        | _,_ => True
        end *)
    ;
}.
    