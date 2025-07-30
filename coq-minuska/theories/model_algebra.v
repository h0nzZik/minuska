From Minuska Require Import
    prelude
    spec
    signature_morphism
.

From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Logic.PropExtensionality.

#[local]
Arguments FunSymbol (Signature) : clear implicits.
#[local]
Arguments PredSymbol (Signature) : clear implicits.
#[local]
Arguments builtin_function_interp {TermSymbol} {TermSymbols signature}
  {NondetValue Carrier} (ModelOver) _ _ _
.
#[local]
Arguments builtin_predicate_interp {TermSymbol} {TermSymbols signature}
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

Program Definition inj_id (A : Type) : Injection A A :=
{| inject := fun x => x; |}
.
Fail Next Obligation.

(* Of course not.
Program Definition inj_fst (A B : Type) : Injection (prod A B) A :=
{|
    inject := fst ;
|}.
Next Obligation.
Fail Next Obligation. *)

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

Program Definition rinj_id (A : Type) : ReversibleInjection A A := {|
    ri_injection := {| inject := fun x => x; |};
    ri_reverse := fun x => Some x;
|}.
Fail Next Obligation.

Program Definition rinj_inl (A B : Type) : ReversibleInjection A (A+B) := {|
    ri_injection := {| inject := inl; |} ;
    ri_reverse := fun x => match x with inl x' => Some x' | _ => None end ;
|}.
Fail Next Obligation.

Program Definition rinj_inr (A B : Type) : ReversibleInjection B (A+B) := {|
    ri_injection := {| inject := inr; |} ;
    ri_reverse := fun x => match x with inr x' => Some x' | _ => None end ;
|}.
Fail Next Obligation.

Record RelaxedModel
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
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
    rm_carrier_countable :
        Countable rm_carrier
    ;
    rm_model_over :
        forall (Carrier : Type),
        Injection FromT Carrier ->
        ReversibleInjection rm_carrier Carrier ->
        ModelOver signature NondetValue Carrier
    ;
}.

Program Definition model_of_relaxed
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EFT : EqDecision FromT}
    {_CT : Countable FromT}
    (RM : RelaxedModel signature NondetValue FromT)
    :
    Model signature NondetValue
:= {|
    BasicValue := sum FromT (rm_carrier _ _ _ RM) ;
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
Next Obligation.
    destruct RM.
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
            {TermSymbol : Type}
            {TermSymbols : Symbols TermSymbol},
            @RelaxedModel TermSymbol TermSymbols signature NondetValue FromT ->
            (* (inja : Injection FromT Carrier) *)
            (* (injb : ReversibleInjection (rmf_carrier Carrier) Carrier), *)
            @RelaxedModel
                TermSymbol
                TermSymbols
                (rmf_signature signature)
                (rmf_nondet NondetValue)
                FromT
}.

Definition rmf_apply
    {FromT : Type}
    (f : RelaxedModelFunctorT FromT)
    {signature : Signature}
    {NondetValue : Type}
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
    (M : @RelaxedModel TermSymbol TermSymbols signature NondetValue FromT)
    :
    @RelaxedModel
        TermSymbol
        TermSymbols
        (rmf_signature _ f signature)
        (rmf_nondet _ f NondetValue)
        FromT
:= 
    rmf_model _ f _ _ M
.

Definition model_reduction
    (s1 s2 : Signature)
    (μ : SignatureMorphism s1 s2)
    (NV Carrier : Type)
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
    :
    ModelOver s2 NV Carrier ->
    ModelOver s1 NV Carrier
:= fun m2 =>
{|
    builtin_function_interp :=
        fun (f : FunSymbol s1)
            (nv : NV)
            (args : list (@TermOver' TermSymbol Carrier))
        => spec.builtin_function_interp m2 (function_TermSymbol_morphism μ f) nv args;

    builtin_predicate_interp :=
        fun (p : PredSymbol s1)
            (nv : NV)
            (args : list (@TermOver' TermSymbol Carrier))
        => spec.builtin_predicate_interp m2 (predicate_TermSymbol_morphism μ p) nv args;
|}
.

Section sum.

    Definition signature_sum (s1 s2 : Signature) : Signature := {|
        FunSymbol := sum (FunSymbol s1) (FunSymbol s2) ;
        PredSymbol := sum (PredSymbol s1) (PredSymbol s2) ;
    |}.
    
    Definition signature_sum_morphism_1_function
        (s1 s2 : Signature)
        : (FunSymbol s1) -> (FunSymbol (signature_sum s1 s2))
    :=
        fun f => inl f
    .

    Definition signature_sum_morphism_1_predicate
        (s1 s2 : Signature)
        : (PredSymbol s1) -> (PredSymbol (signature_sum s1 s2))
    :=
        fun f => inl f
    .

    Definition signature_sum_morphism_1 (s1 s2 : Signature)
        : SignatureMorphism s1 (signature_sum s1 s2)
    := {|
        function_TermSymbol_morphism := signature_sum_morphism_1_function s1 s2 ;
        predicate_TermSymbol_morphism := signature_sum_morphism_1_predicate s1 s2 ;
    |}.
    
    Definition signature_sum_morphism_2_function
        (s1 s2 : Signature)
        : (FunSymbol s2) -> (FunSymbol (signature_sum s1 s2))
    :=
        fun f => inr f
    .

    Definition signature_sum_morphism_2_predicate
        (s1 s2 : Signature)
        : (PredSymbol s2) -> (PredSymbol (signature_sum s1 s2))
    :=
        fun f => inr f
    .

    Definition signature_sum_morphism_2 (s1 s2 : Signature)
        : SignatureMorphism s2 (signature_sum s1 s2)
    := {|
        function_TermSymbol_morphism := signature_sum_morphism_2_function s1 s2 ;
        predicate_TermSymbol_morphism := signature_sum_morphism_2_predicate s1 s2 ;
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
        {TermSymbol : Type}
        {TermSymbols : Symbols TermSymbol}
        (s1 s2 : Signature)
        (NV Carrier : Type)
        (m1 : ModelOver s1 NV Carrier)
        (m2 : ModelOver s2 NV Carrier)
        (f : @FunSymbol (signature_sum s1 s2))
        (nv : NV)
        (args : list (@TermOver' TermSymbol Carrier))
        :
        option (@TermOver' TermSymbol Carrier)
    :=
        match f with
        | inl f' => @builtin_function_interp TermSymbol TermSymbols s1 NV Carrier m1 f' nv args
        | inr f' => @builtin_function_interp TermSymbol TermSymbols s2 NV Carrier m2 f' nv args
        end
    .

    Definition predicate_interp_sum
        {TermSymbol : Type}
        {TermSymbols : Symbols TermSymbol}
        (s1 s2 : Signature)
        (NV Carrier : Type)
        (m1 : ModelOver s1 NV Carrier)
        (m2 : ModelOver s2 NV Carrier)
        (p : @PredSymbol (signature_sum s1 s2))
        (nv : NV)
        (args : list (@TermOver' TermSymbol Carrier))
        :
        option bool
    :=
        match p with
        | inl p' => @builtin_predicate_interp TermSymbol TermSymbols s1 NV Carrier m1 p' nv args
        | inr p' => @builtin_predicate_interp TermSymbol TermSymbols s2 NV Carrier m2 p' nv args
        end
    .

    Definition modelover_sum
        {TermSymbol : Type}
        {TermSymbols : Symbols TermSymbol}
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
        {TermSymbol : Type}
        {TermSymbols : Symbols TermSymbol}
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
        {TermSymbol : Type}
        {TermSymbols : Symbols TermSymbol}
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

Definition modelover_nv_lift 
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
    {signature: Signature}
    {NV1 NV2 : Type}
    {Carrier : Type}
    (nvf : NV2 -> NV1)
    (m : ModelOver signature NV1 Carrier)
    :
    ModelOver signature NV2 Carrier
:= {|
    builtin_function_interp :=
        fun f nv args => @builtin_function_interp _ _ _ _ _ m f (nvf nv) args
    ;
    builtin_predicate_interp :=
        fun p nv args => @builtin_predicate_interp _ _ _ _ _ m p (nvf nv) args
    ;
|}.

(* 
Definition modelover_carrier_lift 
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
    {signature: Signature}
    {NV : Type}
    {Carrier1 Carrier2 : Type}
    (cf : ReversibleInjection Carrier1 Carrier2)
    (m : ModelOver signature NV Carrier1)
    :
    ModelOver signature NV Carrier2
:= {|
    builtin_function_interp :=
        fun f nv args => @builtin_function_interp _ _ _ _ _ m f nv ((TermOver'_map (@ri_reverse Carrier1 Carrier2 cf)) <$> args)
|}.
 *)

