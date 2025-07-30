From Minuska Require Import
    prelude
    spec
    signature_morphism
.

From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Logic.PropExtensionality.

(* 
    This is for extensible value algebras.
    For example, integers should work not only on our carrier [Vours]
    containing exclusively integers,
    but on any carrier [Carrier] in which [Z] is included.
    However, integers also need booleans (if they are to be compared).
    Thus, we have [Vdeps].
*)
Class RelaxedValueAlgebra
    (Vdeps Vours : Type)
    (NV Sy Fs Ps : Type)
:= {        
    rva_over :
        forall (Carrier : Type),
            Injection Vdeps Carrier ->
            ReversibleInjection Vours Carrier ->
            ValueAlgebra Carrier NV Sy Fs Ps
}.

(* 
    The small model of a relaxed value algebra
    contains just the dependencies in addition to own values
    of that relaxed value algebra.
 *)
Program Definition small_model_of_relaxed
    (Vdeps Vours : Type)
    (NV Sy Fs Ps : Type)
    (rva : RelaxedValueAlgebra Vdeps Vours NV Sy Fs Ps)
    :
    ValueAlgebra (Vdeps+Vours) NV Sy Fs Ps
:=
    (rva.(rva_over)
        (Vdeps+Vours)
        {| inject := inl |}
        {|
            ri_injection := {| inject := inr |} ;
            ri_reverse := fun x => match x with inr x' => Some x' | _ => None end ;
        |}
    )
.
Fail Next Obligation.

(* TODO generalize such that we can rename term symbols also *)
Definition va_reduction
    {BV Ts : Type}
    {A_Var A_Fs A_Ps A_Hps A_As A_Ms A_Qs A_HV A_NV : Type}
    {B_Var B_Fs B_Ps B_Hps B_As B_Ms B_Qs B_HV B_NV : Type}
    (μ : @BasicTypesMorphism'
        A_Var Ts A_Fs A_Ps A_Hps A_As A_Ms A_Qs BV A_HV A_NV
        B_Var Ts B_Fs B_Ps B_Hps B_As B_Ms B_Qs BV B_HV B_NV
    )
:
    ValueAlgebra BV B_NV Ts B_Fs B_Ps ->
    ValueAlgebra BV A_NV Ts A_Fs A_Ps
:= fun m2 =>
{|
    builtin_function_interp :=
        fun (f : A_Fs)
            (nv : A_NV)
            (args : list (@TermOver' Ts BV))
        => m2.(builtin_function_interp)
            (μ.(FunSymbol_morph) f)
            (μ.(NondetValue_morph) nv)
            args
    ;

    builtin_predicate_interp :=
        fun (p : A_Ps)
            (nv : A_NV)
            (args : list (@TermOver' Ts BV))
        => m2.(builtin_predicate_interp)
            (μ.(PredSymbol_morph) p)
            (μ.(NondetValue_morph) nv)
            args
    ;
|}.

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

