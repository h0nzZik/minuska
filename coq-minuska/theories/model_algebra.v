From Minuska Require Import
    prelude
    spec
.

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

Record SignatureMorphism (s1 s2 : Signature) := {
    function_symbol_morphism : (builtin_function_symbol s1) -> (builtin_function_symbol s2) ;
    predicate_symbol_morphism : (builtin_predicate_symbol s1) -> (builtin_predicate_symbol s2) ;
}.

Arguments function_symbol_morphism {s1 s2} s _.
Arguments predicate_symbol_morphism {s1 s2} s _.


Class SMInj {s1 s2 : Signature} (μ : SignatureMorphism s1 s2) := {
    smif :: Inj (=) (=) (function_symbol_morphism μ) ;
    smip :: Inj (=) (=) (predicate_symbol_morphism μ) ;
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
        destruct m1; simpl in *.
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
