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

(* Print ModelOver. *)
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
        Injection rm_carrier Carrier ->
        ModelOver signature NondetValue Carrier
    ;
}.

Program Definition model_of_relaxed
    {symbol : Type}
    {symbols : Symbols symbol}
    (signature : Signature)
    (NondetValue : Type)
    (FromT : Type)
    {_EFT : EqDecision FromT}
    :
    RelaxedModel signature NondetValue FromT  ->
    Model signature NondetValue
:= fun RM => {|
    builtin_value := sum FromT (rm_carrier _ _ _ RM) ;
    builtin_model_over :=
        rm_model_over signature NondetValue FromT RM
        (sum FromT (rm_carrier _ _ _ RM))
        {| inject := inl |}
        {| inject := inr |}
|}.
Next Obligation.
    destruct RM as [c ed ov].
    apply _.
Defined.
Fail Next Obligation.

(* 
Definition RelaxedCarrier
    (T1 T2 : Type)
:=
    Injection T1 T2 -> Type
.

Print ModelOver.



(*
    [Param] represents a part of the carrier that is not present
    neither in the input carrier nor in the output carrier
    but should be added at some point after the transformation.
*)
Class RelaxedCarrierFunctorT (Param : Type) := {
    rcf_carrier :
        forall
            (Carrier : Type),
            RelaxedCarrier Param Carrier
    ;

    rcf_carrier_eqdec :
        forall (Carrier : Type) (inj : Injection Param Carrier),
            EqDecision Carrier ->
            EqDecision (rcf_carrier Carrier inj)
    ;

    (*
        The functor preserves injections to carrier
    *)
    rcf_from:
        forall (Carrier FromT : Type)
            (inj : Injection Param Carrier)
            (f : FromT -> Carrier),
            FromT -> (rcf_carrier Carrier inj)
    ;

    rcf_from_inj:
        forall (Carrier FromT : Type)
            (inj : Injection Param Carrier)
            (f : FromT -> Carrier)
            (finj : Inj (=) (=) f),
            Inj (=) (=) (rcf_from Carrier FromT inj f)
    ;
}. *)

Class CarrierFunctorT := {
    cf_carrier
        : Type -> Type
    ;
    cf_carrier_eqdec
        : forall T,
            EqDecision T ->
            EqDecision (cf_carrier T)
    ;

    cf_from:
        forall (T FromT : Type)(f : FromT -> T),
            FromT -> (cf_carrier T)
    ;

    cf_from_inj:
        forall (T FromT : Type)(f : FromT -> T),
            Inj (=) (=) f ->
            Inj (=) (=) (cf_from T FromT f)
    ;

}.

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

Arguments builtin_value {symbol} {symbols signature}
  {NondetValue} (Model)
.

(*
    Huh, composing two models of the same signature would be weird
    because we would have to somehow interpret a symbol applied
    to an empty list in an arbitrarily-chosen constitutent model.
*)

(* 
Fixpoint lift_sum_list {A B : Type} (l : list (sum A B))
    : option (sum (list A) (list B))
. *)

(* 
Definition is_inl {A B : Type} (x : sum A B) : bool :=
    match x with
    | inl _ => true
    | _ => false
    end
.

Definition is_inr {A B : Type} (x : sum A B) : bool :=
    match x with
    | inr _ => true
    | _ => false
    end
.

Definition from_inl {A B : Type} (x : sum A B) : option A :=
    match x with
    | inl x' => Some x'
    | _ => None
    end
.

Definition from_inr {A B : Type} (x : sum A B) : option B :=
    match x with
    | inr x' => Some x'
    | _ => None
    end
.


Fixpoint is_relatively_pure
    {symbol : Type}
    {symbols : Symbols symbol}
    {Carrier : Type}
    (p : Carrier -> bool)
    (t : @TermOver' symbol Carrier)
:=
    match t with
    | t_over c => p c
    | t_term _ xs => forallb (is_relatively_pure p) xs
    end
.

Fixpoint pure_cast
    {symbol : Type}
    {symbols : Symbols symbol}
    {Carrier Carrier' : Type}
    (cast : Carrier -> option Carrier')
    (t : @TermOver' symbol Carrier)
    : option (@TermOver' symbol Carrier')
:=
    match t with
    | t_over c => t_over <$> (cast c)
    | t_term s xs => (t_term s) <$> (list_collect (pure_cast cast <$> xs))
    end
.

About builtin_function_interp.
Definition modelover_union_function_interp 
    {symbol : Type}
    {symbols : Symbols symbol}
    (s : Signature)
    (NV : Type)
    (Carrier : Type)
    (m1 : ModelOver s NV Carrier1)
    (m2 : ModelOver s NV Carrier2)
:
    (builtin_function_symbol s) -> NV -> (list (@TermOver' symbol (sum Carrier))) -> (@TermOver' symbol Carrier1)
:=
    fun f nv args =>
    if (forallb (is_relatively_pure is_inl) args) then
        let oargs' : option (list (@TermOver' symbol Carrier1)) := list_collect (pure_cast from_inl <$> args) in
        builtin_function_interp m1 f nv <$> oargs'
    else (

    )
.

Print ModelOver.
Definition modelover_union 
    {symbol : Type}
    {symbols : Symbols symbol}
    (s : Signature)
    (NV : Type)
    (Carrier : Type)
    (m1 : ModelOver s NV Carrier1)
    (m2 : ModelOver s NV Carrier2)
:
    ModelOver s NV (sum Carrier)
:= {|
    builtin_function_interp := fun f
|}
.


Definition model_union 
    {symbol : Type}
    {symbols : Symbols symbol}
    (s : Signature)
    (NV : Type)
    (m1 : Model s NV)
    (m2 : Model s NV)
:
    Model s NV
:= {|
    builtin_value := sum (spec.builtin_value m1) (spec.builtin_value m2)
|}
. *)
