From Minuska Require Import
    prelude
    spec
    signature_morphism
.

From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Logic.PropExtensionality.

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
    {symbol : Type}
    {symbols : Symbols symbol}
    {signature : Signature}
    {NondetValue : Type}
    {FromT : Type}
    {_EFT : EqDecision FromT}
    {_CT : Countable FromT}
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

Program Definition model_reduction
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
    
    bps_neg_correct := _ ;
|}
.
Next Obligation.
    destruct μ as [μf μp H1μp H2μp].
    destruct m2 as [bf bp Hbp].
    simpl in *.
    assert (Hmy := Hbp (μp p) (μp p') nv l b b').
    ltac1:(ospecialize (Hmy _ _)).
    {
        rewrite H2μp.
        rewrite H.
        reflexivity.
    }
    {
        rewrite H1μp.
        exact H0.
    }
    specialize (Hmy H1 H2).
    exact Hmy.
Qed.
Fail Next Obligation.

Section sum.

    Program Definition signature_sum (s1 s2 : Signature) : Signature := {|
        builtin_function_symbol := sum (builtin_function_symbol s1) (builtin_function_symbol s2) ;
        builtin_predicate_symbol := sum (builtin_predicate_symbol s1) (builtin_predicate_symbol s2) ;
        bps_ar := fun p =>
            match p with
            | inl p' => @bps_ar s1 p'
            | inr p' => @bps_ar s2 p'
            end;
        bps_neg := fun p =>
            match p with
            | inl p' => inl <$> @bps_neg s1 p'
            | inr p' => inr <$> @bps_neg s2 p'
            end ;
        bps_neg_ar := _;
        bps_neg__sym := _;
    |}.
    Next Obligation.
        destruct p,p'; simpl in *; ltac1:(simplify_option_eq);
            apply bps_neg_ar; assumption.
    Qed.
    Next Obligation.
        destruct p, p'; simpl in *; ltac1:(simplify_option_eq);
            erewrite bps_neg__sym; simpl; try reflexivity; assumption.
    Qed.
    Fail Next Obligation.

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

    Program Definition signature_sum_morphism_1 (s1 s2 : Signature)
        : SignatureMorphism s1 (signature_sum s1 s2)
    := {|
        function_symbol_morphism := signature_sum_morphism_1_function s1 s2 ;
        predicate_symbol_morphism := signature_sum_morphism_1_predicate s1 s2 ;
    |}.
    Fail Next Obligation.

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

    Program Definition signature_sum_morphism_2 (s1 s2 : Signature)
        : SignatureMorphism s2 (signature_sum s1 s2)
    := {|
        function_symbol_morphism := signature_sum_morphism_2_function s1 s2 ;
        predicate_symbol_morphism := signature_sum_morphism_2_predicate s1 s2 ;
    |}.
    Fail Next Obligation.

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
        option (@TermOver' symbol Carrier)
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
        option bool
    :=
        match p with
        | inl p' => @builtin_predicate_interp symbol symbols s1 NV Carrier m1 p' nv args
        | inr p' => @builtin_predicate_interp symbol symbols s2 NV Carrier m2 p' nv args
        end
    .

    Program Definition modelover_sum
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
        bps_neg_correct := _;
    |}
    .
    Next Obligation.
        Check bps_neg_correct.
        destruct p,p'; simpl in *; ltac1:(simplify_option_eq).
        {
            eapply bps_neg_correct in Heqo.
            { apply Heqo. }
            { apply H0. }
            { apply H1. }
            { apply H2. }
        }
        {
            eapply bps_neg_correct in Heqo.
            { apply Heqo. }
            { apply H0. }
            { apply H1. }
            { apply H2. }
        }
    Qed.
    Fail Next Obligation.

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
        destruct m1 as [f1 p1 Hneg1]; simpl in *.
        destruct m2 as [f2 p2 Hneg2]; simpl in *.
        f_equal.
        apply proof_irrelevance.
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
        apply proof_irrelevance.
    Qed.


End sum.

Program Definition modelover_nv_lift 
    {symbol : Type}
    {symbols : Symbols symbol}
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
Next Obligation.
    eapply bps_neg_correct in H.
    { apply H. }
    { apply H0. }
    { apply H1. }
    { apply H2. }
Qed.
Fail Next Obligation.

(* 
Definition modelover_carrier_lift 
    {symbol : Type}
    {symbols : Symbols symbol}
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

