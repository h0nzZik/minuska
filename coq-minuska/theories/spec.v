From Minuska Require Import
    prelude
.

From Equations Require Export Equations.

(*
    TermOver' is the main structure for representing
    both concrete and TermSymbolic configurations,
    as well as expression terms.
    Since Coq will not generate strong enough induction principle.
    we need to define our own.
*)
Unset Elimination Schemes.
#[universes(polymorphic=yes, cumulative=yes)]
Inductive TermOver' {T : Type} (A : Type) : Type :=
| t_over (a : A)
| t_term (s : T) (l : list (@TermOver' T A))
.
Set Elimination Schemes.

Arguments t_over {T} {A}%_type_scope a.
Arguments t_term {T} {A}%_type_scope s l%_list_scope.

Section custom_induction_principle.

    Context
        {T : Type}
        {A : Type}
        (P : @TermOver' T A -> Prop)
        (true_for_over : forall a, P (t_over a) )
        (preserved_by_term :
            forall
                (s : T)
                (l : list (@TermOver' T A)),
                Forall P l ->
                P (t_term s l)
        )
    .

    Fixpoint TermOver'_ind (p : @TermOver' T A) : P p :=
    match p with
    | t_over a => true_for_over a
    | t_term s l => preserved_by_term s l (Forall_true P l TermOver'_ind)
    end.

End custom_induction_principle.

(* Class MVariables (Variabl : Type) := {
    Variabl_eqdec :: EqDecision Variabl ;
    Variabl_countable :: Countable Variabl ;
    Variabl_infinite :: Infinite Variabl ;
}. *)

Class EDC (T : Type) := {
    edc_eqdec :: EqDecision T;
    edc_count :: Countable T;
}.



Set Primitive Projections.
CoInductive Stream (A : Type) : Type := Seq {
    hd : A;
    tl : Stream A ;
}.


Class BasicTypes := Build_BasicTypes {
    Variabl     : Type ; (* Would be [Variable] but that is a keyword in Rocq. *)
    TermSymbol  : Type ;
    FunSymbol   : Type ;
    PredSymbol  : Type ;
    HPredSymbol : Type ;
    AttrSymbol  : Type ;
    MethSymbol  : Type ;
    QuerySymbol : Type ;
    BasicValue  : Type ;
    HiddenValue : Type ;
    NondetValue : Type ;
    ProgramT    : Type ;
}.

Class BasicTypesProperties (basic_types : BasicTypes)
:= Build_BasicTypesProperties {
    Variabl_edc :: EDC basic_types.(Variabl) ;
    TermSymbol_edc :: EDC basic_types.(TermSymbol) ;
    FunSymbol_edc :: EDC basic_types.(FunSymbol) ;
    PredSymbol_edc :: EDC basic_types.(PredSymbol) ;
    HPredSymbol_edc :: EDC basic_types.(HPredSymbol) ;
    AttrSymbol_edc :: EDC basic_types.(AttrSymbol) ;
    MethSymbol_edc :: EDC basic_types.(MethSymbol) ;
    QuerySymbol_edc :: EDC basic_types.(QuerySymbol) ;
    BasicValue_edc :: EDC basic_types.(BasicValue) ;
    HiddenValue_edc :: EDC basic_types.(HiddenValue) ;
    NondetValue_edc :: EDC basic_types.(NondetValue) ;

    Variable_inf :: Infinite basic_types.(Variabl) ;
}.

Class ValueAlgebra
    (V NV : Type)
    (Sy Fs Ps : Type)
     := {        
    builtin_function_interp
        : Fs
        -> NV
        -> list (@TermOver' Sy V)
        -> option (@TermOver' Sy V) ;
        
    builtin_predicate_interp
        : Ps
        -> NV
        -> list (@TermOver' Sy V)
        -> option bool ;    
}.

Class HiddenAlgebra
    (HD V NV : Type)
    (Sy As Ms HPs : Type)
:= {
    attribute_interpretation :
        As ->
        HD ->
        list (@TermOver' Sy V) ->
        option V ;
    

    method_interpretation:
        Ms ->
        HD ->
        list (@TermOver' Sy V) ->
        option HD ;

    hidden_predicate_interpretation :
        HPs ->
        HD ->
        list (@TermOver' Sy V) ->
        option bool ;

    hidden_init : HD ;
}.


Class ProgramInfo
    (PT BVal : Type)
    (Sy Qs : Type )
    : Type
:= {
    pi_TermSymbol_interp :
        PT -> 
        Qs -> 
        list (@TermOver' Sy BVal) ->
        option (@TermOver' Sy BVal) ;
}.

Class BackgroundModelOver
    (BVal HVal NdVal Var Sy Fs Ps As Ms Qs HPs PT : Type)
:= Build_BackgroundModelOver {
    value_algebra :: ValueAlgebra BVal NdVal Sy Fs Ps;
    hidden_algebra :: HiddenAlgebra HVal BVal NdVal Sy As Ms HPs ;
    program_info :: ProgramInfo PT BVal Sy Qs;
    nondet_gen : nat -> NdVal ;
}.

Class BackgroundModel := Build_BackgroundModel {
    basic_types :: BasicTypes ;
    basic_types_properties :: BasicTypesProperties basic_types ;
  
    background_model_over :: BackgroundModelOver 
        basic_types.(BasicValue)
        basic_types.(HiddenValue)
        basic_types.(NondetValue)
        basic_types.(Variabl)
        basic_types.(TermSymbol)
        basic_types.(FunSymbol)
        basic_types.(PredSymbol)
        basic_types.(AttrSymbol)
        basic_types.(MethSymbol)
        basic_types.(QuerySymbol)
        basic_types.(HPredSymbol)
        basic_types.(ProgramT)
    ;
}.


(* A class for querying Variabls of syntactic constructs. *)
Class VarsOf
    (A : Type)
    (var: Type)
    {_Ev : EqDecision var}
    {_Cv : Countable var}
    :=
{
    vars_of : A -> gset var ;
}.

Arguments vars_of : simpl never.

#[export]
Instance VarsOf_TermSymbol
    {Σ : BackgroundModel}
    : VarsOf TermSymbol Variabl
:= {|
    vars_of := fun _ => ∅ ; 
|}.

#[export]
Instance VarsOf_builtin
    {Σ : BackgroundModel}
    : VarsOf BasicValue Variabl
:= {|
    vars_of := fun _ => ∅ ; 
|}.


#[export]
Instance VarsOf_TermOver
    {T0 : Type}
    {T var : Type}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VT : VarsOf T var}
    :
    VarsOf (@TermOver' T0 T) var
:=
{|
    vars_of := (fix go (t : @TermOver' T0 T) := 
        match t with
        | t_over x => vars_of x
        | t_term _ l => ⋃ (go <$> l)
        end
    ) ; 
|}.

Unset Elimination Schemes.
Inductive Expression2
    {Σ : BackgroundModel}
    :=
| e_ground (e : @TermOver' (TermSymbol) BasicValue)
| e_Variabl (x : Variabl)
| e_fun (f : FunSymbol) (l : list Expression2)
| e_query (q : QuerySymbol) (l : list Expression2)
| e_attr (a : AttrSymbol) (l : list Expression2)
.
Set Elimination Schemes.

Section custom_induction_principle.

    Context
        {Σ : BackgroundModel}
        (P : Expression2 -> Prop)
        (true_for_ground : forall e, P (e_ground e))
        (true_for_var : forall x, P (e_Variabl x))
        (preserved_by_fun :
            forall
                (f : FunSymbol)
                (l : list Expression2),
                Forall P l ->
                P (e_fun f l)
        )
        (preserved_by_query :
            forall
                (q : QuerySymbol)
                (l : list Expression2),
                Forall P l ->
                P (e_query q l)
        )
        (preserved_by_attribute :
            forall
                (q : AttrSymbol)
                (l : list Expression2),
                Forall P l ->
                P (e_attr q l)
        )
    .

    Fixpoint Expression2_ind (e : Expression2) : P e :=
    match e with
    | e_ground g => true_for_ground g
    | e_Variabl x => true_for_var x
    | e_fun f l => preserved_by_fun f l  (Forall_true P l Expression2_ind)
    | e_query q l => preserved_by_query q l (Forall_true P l Expression2_ind)
    | e_attr q l => preserved_by_attribute q l (Forall_true P l Expression2_ind)
    end.

End custom_induction_principle.


Fixpoint vars_of_Expression2
    {Σ : BackgroundModel}
    (t : Expression2)
    : gset Variabl :=
match t with
| e_ground _ => ∅
| e_Variabl x => {[x]}
| e_fun _ l => ⋃ (fmap vars_of_Expression2 l)
| e_query _ l => ⋃ (fmap vars_of_Expression2 l)
| e_attr _ l => ⋃ (fmap vars_of_Expression2 l)
end.


#[export]
Instance VarsOf_Expression2
    {Σ : BackgroundModel}
    : VarsOf Expression2 Variabl
:= {|
    vars_of := vars_of_Expression2 ; 
|}.


Inductive BuiltinOrVar {Σ : BackgroundModel} :=
| bov_builtin (b : BasicValue)
| bov_Variabl (x : Variabl)
.

Fixpoint TermOver_size
    {T : Type}
    {A : Type}
    (t : @TermOver' T A)
    : nat
:=
match t with
| t_over _ => 1
| t_term _ l => S (sum_list_with (S ∘ TermOver_size) l)
end.

Fixpoint TermOver'_map
    {T : Type} {A B : Type}
    (f : A -> B)
    (t : @TermOver' T A)
    : @TermOver' T B
:=
    match t with
    | t_over b => t_over (f b)
    | t_term s l => t_term s (map (TermOver'_map f) l)
    end
.

Definition TermOverBuiltin_to_TermOverBoV
    {Σ : BackgroundModel}
    {A : Type}
    (t : @TermOver' A BasicValue)
    : @TermOver' A BuiltinOrVar
:=
    TermOver'_map bov_builtin t
.


Inductive SideCondition {Σ : BackgroundModel} :=
| sc_true
| sc_false
(* positive literal *)
| sc_pred (pred : PredSymbol) (args : list Expression2)
(* negative literal *)
| sc_npred (pred : PredSymbol) (args : list Expression2)
(* Positive literal over hidden data. NOTE: we do not have negatives over hiden data *)
| sc_hpred (pred : HPredSymbol) (args : list Expression2)
| sc_and (left : SideCondition) (right : SideCondition)
| sc_or (left : SideCondition) (right : SideCondition)
.

#[export]
Instance VarsOf_list_something
    {Σ : BackgroundModel}
    {A : Type}
    {_VA: VarsOf A Variabl}
    : VarsOf (list A) Variabl
:= {|
    vars_of := fun scs => ⋃ (vars_of <$> scs)
|}.

Fixpoint vars_of_sc {Σ : BackgroundModel} (sc : SideCondition) : gset Variabl :=
match sc with
| sc_true => ∅
| sc_false => ∅
| sc_pred _ args => vars_of args
| sc_npred _ args => vars_of args
| sc_hpred _ args => vars_of args
| sc_and l r => vars_of_sc l ∪ vars_of_sc r
| sc_or l r => vars_of_sc l ∪ vars_of_sc r
end
.

#[export]
Instance  VarsOf_sc
    {Σ : BackgroundModel}
    : VarsOf SideCondition Variabl
:= {|
    vars_of := vars_of_sc ;
|}.

Variant BasicEffect0 {Σ : BackgroundModel} := 
| be_method (s : MethSymbol) (args : list Expression2)
(* This is like a binder *)
| be_remember (x : Variabl) (e : Expression2)
.

Definition Effect0 {Σ : BackgroundModel} : Type :=
    list BasicEffect0
.

Definition vars_of_Effect0'
    {Σ : BackgroundModel}
    (f : Effect0)
    : gset Variabl
:=
    fold_right (fun be vs =>
        match be with
        | be_method s args =>
            vs ∪ (union_list (fmap vars_of args))
        | be_remember x e =>
            (vs ∖ {[x]}) ∪ (vars_of e)
        end
    ) empty f
.

#[export]
Instance VarsOf_Effect0
    {Σ : BackgroundModel}
    : VarsOf Effect0 Variabl
:= {|
    vars_of := vars_of_Effect0' ; 
|}.


Record RewritingRule2
    {Σ : BackgroundModel}
    (Label : Set)
:= mkRewritingRule2
{
    r_from : @TermOver' TermSymbol BuiltinOrVar ;
    r_to : @TermOver' TermSymbol Expression2 ;
    r_scs : SideCondition ;
    r_eff : Effect0 ;
    r_label : Label ;
}.

Arguments r_from {Σ} {Label%_type_scope} r.
Arguments r_to {Σ} {Label%_type_scope} r.
Arguments r_scs {Σ} {Label%_type_scope} r.
Arguments r_eff {Σ} {Label%_type_scope} r.
Arguments r_label {Σ} {Label%_type_scope} r.


Definition vars_of_BoV
    {Σ : BackgroundModel}
    (bov : BuiltinOrVar)
    : gset Variabl
:=
match bov with
| bov_Variabl x => {[x]}
| bov_builtin _ => ∅
end.

#[export]
Instance VarsOf_BoV
    {Σ : BackgroundModel}
    : VarsOf BuiltinOrVar Variabl
:= {|
    vars_of := vars_of_BoV ; 
|}.


#[export]
Instance VarsOf_TermOver_BuiltinOrVar
    {Σ : BackgroundModel}
    :
    VarsOf (@TermOver' TermSymbol BuiltinOrVar) Variabl
.
Proof.
    apply VarsOf_TermOver.
Defined.

#[export]
Instance VarsOf_TermOver_Expression2
    {Σ : BackgroundModel}
    :
    VarsOf (@TermOver' TermSymbol Expression2) Variabl
.
Proof.
    apply VarsOf_TermOver.
Defined.

(* A rewriting theory is a list of rewriting rules. *)
Definition RewritingTheory2
    {Σ : BackgroundModel}
    (Label : Set)
    := list (RewritingRule2 Label)
.


(* A valuation is a mapping from Variabls to groun terms. *)
Definition Valuation2
    {Σ : BackgroundModel}
:=
    gmap Variabl (@TermOver' TermSymbol BasicValue)
.

(* TODO Do we even need this?*)
#[export]
Instance Subseteq_Valuation2 {Σ : BackgroundModel}
    : SubsetEq Valuation2
.
Proof.
    unfold Valuation2.
    apply _.
Defined.

#[export]
Instance VarsOf_Valuation2_
    {Σ : BackgroundModel}
    {var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    : VarsOf (gmap var (@TermOver' TermSymbol BuiltinOrVar)) var
:= {|
    vars_of := fun ρ => dom ρ ; 
|}.

#[export]
Instance VarsOf_Valuation2
    {Σ : BackgroundModel}
    : VarsOf (Valuation2) Variabl
:= {|
    vars_of := fun ρ => dom ρ ; 
|}.

Definition Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar
    {Σ : BackgroundModel}
    (ρ : Valuation2)
    (t : @TermOver' TermSymbol BasicValue)
    (bv : BuiltinOrVar)
    : Prop
:= match bv with
    | bov_builtin b => t = t_over b
    | bov_Variabl x => ρ !! x = Some t
    end
.

Equations? sat2B
    {Σ : BackgroundModel}
    (ρ : Valuation2)
    (t : @TermOver' TermSymbol BasicValue)
    (φ : @TermOver' TermSymbol BuiltinOrVar)
    : Prop
    by wf (TermOver_size φ) lt
:=
    sat2B ρ t (t_over bv) := Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar ρ t bv ;
    sat2B ρ (t_over _) (t_term s l) := False ;
    sat2B ρ (t_term s' l') (t_term s l) :=
        ((s' = s) /\
        (length l' = length l) /\
        forall i t' φ' (pf1 : l !! i = Some φ') (pf2 : l' !! i = Some t'),
            sat2B ρ t' φ'
        )
    ;
.
Proof.
    abstract(
    simpl in *;
    simpl;
    apply take_drop_middle in pf1;
    rewrite <- pf1;
    rewrite sum_list_with_app; simpl;
    ltac1:(lia)).
Defined.

Fixpoint Expression2_evaluate
    {Σ : BackgroundModel}
    (program : ProgramT)
    (h : HiddenValue)
    (ρ : Valuation2)
    (t : Expression2)
    : NondetValue -> option (@TermOver' TermSymbol BasicValue) :=
match t with
| e_ground e => fun _ =>  Some (e)
| e_Variabl x =>
    match ρ !! x with
    | Some v => fun _ =>  Some (v)
    | None => fun _ => None
    end
| e_query q l =>
    fun nv =>
    let es' := (fun e => Expression2_evaluate program h ρ e nv) <$> l in
    es ← list_collect es';
    pi_TermSymbol_interp program q es
| e_fun f l =>
    fun nv =>
    let es' := (fun e => Expression2_evaluate program h ρ e nv) <$> l in
    es ← list_collect es';
    builtin_function_interp f nv es
| e_attr a l =>
    fun nv =>
    let es' := (fun e => Expression2_evaluate program h ρ e nv) <$> l in
    es ← list_collect es';
    t_over <$> attribute_interpretation a h es
end.


Equations? sat2E
    {Σ : BackgroundModel}
    (program : ProgramT)
    (h : HiddenValue)
    (ρ : Valuation2)
    (t : @TermOver' TermSymbol BasicValue)
    (φ : @TermOver' TermSymbol Expression2)
    (nv : NondetValue)
    : Prop
    by wf (TermOver_size φ) lt
:=
    sat2E program h ρ t (t_over e) nv :=
        match Expression2_evaluate program h ρ e nv with 
        | Some t' => t' = t
        | None => False
        end ;
    sat2E program h ρ (t_over a) (t_term s l) _ := False ;
    sat2E program h ρ (t_term s' l') (t_term s l) nv := 
        s' = s /\
        length l' = length l /\
        forall i t' φ' (pf1 : l !! i = Some φ') (pf2 : l' !! i = Some t'),
            sat2E program h ρ t' φ' nv
    ;
.
Proof.
    abstract(
        simpl;
        apply take_drop_middle in pf1;
        rewrite <- pf1;
        rewrite sum_list_with_app; simpl;
        ltac1:(lia)
    ).
Defined.

Definition SideCondition_evaluate
    {Σ : BackgroundModel}
    (program : ProgramT)
    (h : HiddenValue)
    (ρ : Valuation2)
    (nv : NondetValue)
    (sc : SideCondition)
    : option bool
:=
    (
        fix go (sc : SideCondition) : option bool :=
        match sc with
        | sc_true => Some true
        | sc_false => Some false
        | sc_pred pred args => (
            let ts' := (fun e => Expression2_evaluate program h ρ e nv) <$> args in
            ts ← list_collect ts';
            builtin_predicate_interp pred nv ts
        )
        | sc_npred pred args => (
            let ts' := (fun e => Expression2_evaluate program h ρ e nv) <$> args in
            ts ← list_collect ts';
            negb <$> builtin_predicate_interp pred nv ts
        )
        | sc_hpred pred args => (
            let ts' := (fun e => Expression2_evaluate program h ρ e nv) <$> args in
            ts ← list_collect ts';
            hidden_predicate_interpretation pred h ts
        )
        | sc_and l r => 
            l' ← (go l);
            r' ← (go r);
            Some (andb l' r')
        | sc_or l r => 
            l' ← (go l);
            r' ← (go r);
            Some (orb l' r')
        end
    ) sc
.

Definition BasicEffect0_evaluate
    {Σ : BackgroundModel}
    (program : ProgramT)
    (h : HiddenValue)
    (ρ : Valuation2)
    (nv : NondetValue)
    (f : BasicEffect0)
    : option (HiddenValue*Valuation2)
:=
    match f with
    | be_method m args =>
            let ts' := (fun e => Expression2_evaluate program h ρ e nv) <$> args in
            ts ← list_collect ts';
            h' ← method_interpretation m h ts;
            Some (h', ρ)
    | be_remember x e => 
        v ← Expression2_evaluate program h ρ e nv;
        Some (h, <[x := v]>ρ)
    end
.

(* Print fold_left. *)
Definition Effect0_evaluate'
    {Σ : BackgroundModel}
    (program : ProgramT)
    (h : HiddenValue)
    (ρ : Valuation2)
    (nv : NondetValue)
    (f : Effect0)
    : option (HiddenValue*Valuation2)
:=
    fold_left
        (fun (p' : option (HiddenValue*Valuation2)) (bf : BasicEffect0) => p ← p'; BasicEffect0_evaluate program p.1 p.2 nv bf)
        f
        (Some (h,ρ))
    
.


Definition Effect0_evaluate
    {Σ : BackgroundModel}
    (program : ProgramT)
    (h : HiddenValue)
    (ρ : Valuation2)
    (nv : NondetValue)
    (f : Effect0)
    : option HiddenValue
:=
    fmap fst (Effect0_evaluate' program h ρ nv f)
.

Definition rewrites_in_valuation_under_to
    {Σ : BackgroundModel}
    {Label : Set}
    (program : ProgramT)
    (ρ : Valuation2)
    (r : RewritingRule2 Label)
    (from : (@TermOver' TermSymbol BasicValue)*(HiddenValue))
    (under : Label)
    (nv : NondetValue)
    (to : (@TermOver' TermSymbol BasicValue)*(HiddenValue))
    : Type
:= ((sat2B ρ from.1 (r_from r))
* (sat2E program from.2 ρ to.1 (r_to r) nv)
* (SideCondition_evaluate program from.2 ρ nv (r_scs r) = Some true)
* (Some to.2 = Effect0_evaluate program from.2 ρ nv (r_eff r))
* (under = r_label r)
)%type
.

Definition rewrites_to
    {Σ : BackgroundModel}
    {Label : Set}
    (program : ProgramT)
    (r : RewritingRule2 Label)
    (from : (@TermOver' TermSymbol BasicValue)*(HiddenValue))
    (under : Label)
    (nv : NondetValue)
    (to : (@TermOver' TermSymbol BasicValue)*(HiddenValue))
    : Type
:= { ρ : Valuation2 &
        rewrites_in_valuation_under_to program ρ r from under nv to
   }
.

Definition rewriting_relation
    {Σ : BackgroundModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (program : ProgramT)
    (nv : NondetValue)
    : (@TermOver' TermSymbol BasicValue)*(HiddenValue) -> (@TermOver' TermSymbol BasicValue)*(HiddenValue) -> Type
    := fun from to =>
        { r : _ & { a : _ & ((r ∈ Γ) * rewrites_to program r from a nv to)%type}}
.

Definition rewrites_to_nondet
    {Σ : BackgroundModel}
    {Label : Set}
    (program : ProgramT)
    (r : RewritingRule2 Label)
    (from : (@TermOver' TermSymbol BasicValue)*(HiddenValue))
    (under : Label)
    (to : (@TermOver' TermSymbol BasicValue)*(HiddenValue))
    : Type
:= { nv : NondetValue &
        rewrites_to program r from under nv to
   }
.

Definition rewrites_to_thy
    {Σ : BackgroundModel}
    {Label : Set}
    (program : ProgramT)
    (Γ : RewritingTheory2 Label)
    (from : (@TermOver' TermSymbol BasicValue)*(HiddenValue))
    (under : Label)
    (to : (@TermOver' TermSymbol BasicValue)*(HiddenValue))
:= { r : RewritingRule2 Label &
    ((r ∈ Γ)*(rewrites_to_nondet program r from under to))%type

}
.

Record BuiltinsBinding := {
    bb_function_names : list (string * string) ;
}.

