From Minuska Require Import
    prelude
    spec
    signature_morphism
.

From Coq Require Import Logic.Eqdep_dec.

#[local]
Arguments builtin_function_symbol (Signature) : clear implicits.
#[local]
Arguments builtin_predicate_symbol (Signature) : clear implicits.
#[local]
Arguments builtin_function_interp {symbol} {symbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.
#[local]
Arguments builtin_predicate_interp {symbol} {symbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.

Class Injection (FromT ToT : Type) := {
    inject : FromT -> ToT ;
    inject_inj :: Inj (=) (=) inject ;
}.

Arguments inject (FromT ToT) {Injection} _.

Definition inj_compose {A B C : Type} (g : Injection B C) (f : Injection A B) := {|
    inject := compose (@inject _ _ g) (@inject _ _ f) ;
|}. 

Class ReversibleInjection (FromT ToT : Type) := {
    ri_injection :: Injection FromT ToT ;
    ri_reverse : ToT -> option FromT ;
    ri_reverse_pf : forall from,
        ri_reverse (@inject FromT ToT ri_injection from) = Some from ;
}.

Program Definition rinj_compose
    {A B C : Type}
    (g : ReversibleInjection B C)
    (f : ReversibleInjection A B)
:= {|
    ri_injection := inj_compose (@ri_injection _ _ g) (@ri_injection _ _ f) ;
    ri_reverse := fun c =>
        b ← (@ri_reverse _ _ g c);
        (@ri_reverse _ _ f b)
|}.
Next Obligation.
    rewrite ri_reverse_pf.
    simpl.
    rewrite ri_reverse_pf.
    reflexivity.
Qed.
Fail Next Obligation.

Record RelaxedModel
    {symbol : Type}
    {symbols : Symbols symbol}
    (signature : Signature)
    (NondetValue : Type)
    (FromT : Type)
:= {
    rm_carrier :
        Type
    ;
    rm_carrier_eqdec :
        EqDecision rm_carrier
    ;
    rm_model_over :
        forall (Carrier : Type),
        Injection FromT Carrier ->
        ReversibleInjection rm_carrier Carrier ->
        ModelOver signature NondetValue Carrier
    ;
}.

Program Definition model_of_relaxed
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EFT : EqDecision FromT}
    (RM : RelaxedModel signature NondetValue FromT)
    :
    Model signature NondetValue
:= {|
    builtin_value := sum FromT (rm_carrier _ _ _ RM) ;
    builtin_model_over :=
        rm_model_over signature NondetValue FromT RM
        (sum FromT (rm_carrier _ _ _ RM))
        {| inject := inl |}
        {|
            ri_injection := {| inject := inr |} ;
            ri_reverse := fun x => match x with inr x' => Some x' | _ => None end ;
        |}
        
|}.
Next Obligation.
    destruct RM as [c ed ov].
    apply _.
Defined.
Fail Next Obligation.

Record RelaxedModelFunctorT (FromT : Type) := {
    rmf_signature : Signature -> Signature ;
    rmf_nondet : Type -> Type ;

    rmf_model :
        forall
            (signature : Signature)
            (NondetValue : Type)
            {symbol : Type}
            {symbols : Symbols symbol},
            @RelaxedModel symbol symbols signature NondetValue FromT ->
            (* (inja : Injection FromT Carrier) *)
            (* (injb : ReversibleInjection (rmf_carrier Carrier) Carrier), *)
            @RelaxedModel
                symbol
                symbols
                (rmf_signature signature)
                (rmf_nondet NondetValue)
                FromT
}.

Definition rmf_apply
    {FromT : Type}
    (f : RelaxedModelFunctorT FromT)
    {signature : Signature}
    {NondetValue : Type}
    {symbol : Type}
    {symbols : Symbols symbol}
    (M : @RelaxedModel symbol symbols signature NondetValue FromT)
    :
    @RelaxedModel
        symbol
        symbols
        (rmf_signature _ f signature)
        (rmf_nondet _ f NondetValue)
        FromT
:= 
    rmf_model _ f _ _ M
.

(* 
Definition rmf_apply
    {symbol : Type}
    {symbols : Symbols symbol}
    (FromT : Type)
    (f : RelaxedModelFunctorT FromT)
    {signature : Signature}
    {NondetValue : Type}
    (x : RelaxedModel signature NondetValue FromT)
    :
    RelaxedModel (@rmf_signature _ f signature) (@rmf_nondet _ f NondetValue) FromT
:= {|
    rm_carrier := rmf_carrier _ f (@rm_carrier _ _ _ _ _ x) ;
    rm_carrier_eqdec := rmf_carrier_eqdec _ f _ ((@rm_carrier_eqdec _ _ _ _ _ x)) ;
    rm_model_over :=
        fun (Carrier : Type)
            (inja : Injection FromT Carrier)
            (injb : ReversibleInjection _ Carrier)
        => @rmf_model_over _ f signature NondetValue symbol symbols Carrier
            (* inja *)
            (* _ *)
(*             
            {|
                ri_injection := {|
                    inject := 0
                    (* fun (a : (rmf_carrier FromT f (rm_carrier signature NondetValue FromT x))) => (@inject _ _ (@ri_injection _ _ injb) a) *)
                    (* inject := @rmf_from _ f _ _ (@inject _ _ (@ri_injection _ _ injb)) *)
                |}
            |} *)
            (* injb *)
         ;

|}. *)



Definition model_reduction
    (s1 s2 : Signature)
    (μ : SignatureMorphism s1 s2)
    (NV Carrier : Type)
    {symbol : Type}
    {symbols : Symbols symbol}
    :
    ModelOver s2 NV Carrier ->
    ModelOver s1 NV Carrier
:= fun m2 =>
{|
    builtin_function_interp :=
        fun (f : builtin_function_symbol s1)
            (nv : NV)
            (args : list (@TermOver' symbol Carrier))
        => spec.builtin_function_interp m2 (function_symbol_morphism μ f) nv args;

    builtin_predicate_interp :=
        fun (p : builtin_predicate_symbol s1)
            (nv : NV)
            (args : list (@TermOver' symbol Carrier))
        => spec.builtin_predicate_interp m2 (predicate_symbol_morphism μ p) nv args;
|}
.

Section sum.

    Definition signature_sum (s1 s2 : Signature) : Signature := {|
        builtin_function_symbol := sum (builtin_function_symbol s1) (builtin_function_symbol s2) ;
        builtin_predicate_symbol := sum (builtin_predicate_symbol s1) (builtin_predicate_symbol s2) ;
    |}.

    Definition signature_sum_morphism_1_function
        (s1 s2 : Signature)
        : (builtin_function_symbol s1) -> (builtin_function_symbol (signature_sum s1 s2))
    :=
        fun f => inl f
    .

    Definition signature_sum_morphism_1_predicate
        (s1 s2 : Signature)
        : (builtin_predicate_symbol s1) -> (builtin_predicate_symbol (signature_sum s1 s2))
    :=
        fun f => inl f
    .

    Definition signature_sum_morphism_1 (s1 s2 : Signature)
        : SignatureMorphism s1 (signature_sum s1 s2)
    := {|
        function_symbol_morphism := signature_sum_morphism_1_function s1 s2 ;
        predicate_symbol_morphism := signature_sum_morphism_1_predicate s1 s2 ;
    |}.


    Definition signature_sum_morphism_2_function
        (s1 s2 : Signature)
        : (builtin_function_symbol s2) -> (builtin_function_symbol (signature_sum s1 s2))
    :=
        fun f => inr f
    .

    Definition signature_sum_morphism_2_predicate
        (s1 s2 : Signature)
        : (builtin_predicate_symbol s2) -> (builtin_predicate_symbol (signature_sum s1 s2))
    :=
        fun f => inr f
    .

    Definition signature_sum_morphism_2 (s1 s2 : Signature)
        : SignatureMorphism s2 (signature_sum s1 s2)
    := {|
        function_symbol_morphism := signature_sum_morphism_2_function s1 s2 ;
        predicate_symbol_morphism := signature_sum_morphism_2_predicate s1 s2 ;
    |}.

    #[export]
    Program Instance signature_sum_morph_1_inj
        (s1 s2 : Signature)
        :
        SMInj (signature_sum_morphism_1 s1 s2)
    .
    Fail Next Obligation.

    #[export]
    Program Instance signature_sum_morph_2_inj
        (s1 s2 : Signature)
        :
        SMInj (signature_sum_morphism_2 s1 s2)
    .
    Fail Next Obligation.


    Definition function_interp_sum
        {symbol : Type}
        {symbols : Symbols symbol}
        (s1 s2 : Signature)
        (NV Carrier : Type)
        (m1 : ModelOver s1 NV Carrier)
        (m2 : ModelOver s2 NV Carrier)
        (f : @builtin_function_symbol (signature_sum s1 s2))
        (nv : NV)
        (args : list (@TermOver' symbol Carrier))
        :
        (@TermOver' symbol Carrier)
    :=
        match f with
        | inl f' => @builtin_function_interp symbol symbols s1 NV Carrier m1 f' nv args
        | inr f' => @builtin_function_interp symbol symbols s2 NV Carrier m2 f' nv args
        end
    .

    Definition predicate_interp_sum
        {symbol : Type}
        {symbols : Symbols symbol}
        (s1 s2 : Signature)
        (NV Carrier : Type)
        (m1 : ModelOver s1 NV Carrier)
        (m2 : ModelOver s2 NV Carrier)
        (p : @builtin_predicate_symbol (signature_sum s1 s2))
        (nv : NV)
        (args : list (@TermOver' symbol Carrier))
        :
        bool
    :=
        match p with
        | inl p' => @builtin_predicate_interp symbol symbols s1 NV Carrier m1 p' nv args
        | inr p' => @builtin_predicate_interp symbol symbols s2 NV Carrier m2 p' nv args
        end
    .

    Definition modelover_sum
        {symbol : Type}
        {symbols : Symbols symbol}
        (s1 s2 : Signature)
        (NV : Type)
        (Carrier : Type)
        (m1 : ModelOver s1 NV Carrier)
        (m2 : ModelOver s2 NV Carrier)
    :
        ModelOver (signature_sum s1 s2) NV Carrier
    := {|
        builtin_function_interp :=  function_interp_sum s1 s2 NV Carrier m1 m2;
        builtin_predicate_interp :=  predicate_interp_sum s1 s2 NV Carrier m1 m2;
    |}
    .

    Lemma modelover_sum_reduce_1
        {symbol : Type}
        {symbols : Symbols symbol}
        (s1 s2 : Signature)
        (NV : Type)
        (Carrier : Type)
        (m1 : ModelOver s1 NV Carrier)
        (m2 : ModelOver s2 NV Carrier)
    :
        model_reduction
            s1 (signature_sum s1 s2)
            (signature_sum_morphism_1 s1 s2)
            NV Carrier
            (modelover_sum s1 s2 NV Carrier m1 m2)
        = m1.
    Proof.
        unfold model_reduction.
        destruct m1 as [f1 p1]; simpl in *.
        destruct m2 as [f2 p2]; simpl in *.
        f_equal.
    Qed.

    Lemma modelover_sum_reduce_2
        {symbol : Type}
        {symbols : Symbols symbol}
        (s1 s2 : Signature)
        (NV : Type)
        (Carrier : Type)
        (m1 : ModelOver s1 NV Carrier)
        (m2 : ModelOver s2 NV Carrier)
    :
        model_reduction
            s2 (signature_sum s1 s2)
            (signature_sum_morphism_2 s1 s2)
            NV Carrier
            (modelover_sum s1 s2 NV Carrier m1 m2)
        = m2.
    Proof.
        unfold model_reduction.
        destruct m2; simpl in *.
        f_equal.
    Qed.


End sum.
