From Minuska Require Import
    prelude
.

From Equations Require Export Equations.

(*
    TermOver' is the main structure for representing
    both concrete and symbolic configurations,
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

Class MVariables (variable : Type) := {
    variable_eqdec :: EqDecision variable ;
    variable_countable :: Countable variable ;
    variable_infinite :: Infinite variable ;
}.

Class Symbols (symbol : Type) := {
    symbol_eqdec :: EqDecision symbol ;
    symbol_countable :: Countable symbol ;
}.

Class Signature := {
    builtin_function_symbol
        : Type ;
    builtin_function_symbol_eqdec
        :: EqDecision builtin_function_symbol ;
    builtin_function_symbol_countable
        :: Countable builtin_function_symbol ;

    builtin_predicate_symbol
        : Type ;
    builtin_predicate_symbol_eqdec
        :: EqDecision builtin_predicate_symbol ;
    builtin_predicate_symbol_countable
        :: Countable builtin_predicate_symbol ;
    
    bps_ar : builtin_predicate_symbol -> nat ;
    bps_neg : builtin_predicate_symbol -> option builtin_predicate_symbol ;
    bps_neg_ar : forall p p', bps_neg p = Some p' -> bps_ar p = bps_ar p' ;
    bps_neg__sym : forall p p', bps_neg p = Some p' -> bps_neg p' = Some p ;
}.

Class ModelOver {symbol : Type} {symbols : Symbols symbol} (signature : Signature) (NondetValue : Type) (Carrier : Type) := {        
    (* builtin_value_eqdec
        :: EqDecision Carrier ; *)

    builtin_function_interp
        : builtin_function_symbol
        -> NondetValue
        -> list (@TermOver' symbol Carrier)
        -> option (@TermOver' symbol Carrier) ;
        
    builtin_predicate_interp
        : builtin_predicate_symbol
        -> NondetValue
        -> list (@TermOver' symbol Carrier)
        -> option bool ;
    
    bps_neg_correct : forall p p' nv l b b',
        bps_neg p = Some p' ->
        length l = bps_ar p ->
        builtin_predicate_interp p' nv l = Some b ->
        builtin_predicate_interp p nv l = Some b' ->
        b = ~~ b' ;
}.

(* This should be called [Carrier] instead*)
Class Model {symbol : Type} {symbols : Symbols symbol} (signature : Signature) (NondetValue : Type) := {
    builtin_value
        : Type ;

    builtin_value_eqdec
        :: EqDecision builtin_value ;

    builtin_value_countable
        :: Countable builtin_value ;

    builtin_model_over :: ModelOver signature NondetValue builtin_value ;
}.

Set Primitive Projections.
CoInductive Stream (A : Type) : Type := Seq {
    hd : A;
    tl : Stream A ;
}.

Class ProgramInfo
    {symbol : Type}
    {symbols : Symbols symbol}
    {NondetValue : Type}
    {signature : Signature}
    {builtin : Model signature NondetValue}
    : Type
    := {
    QuerySymbol : Type ;
    QuerySymbol_eqdec :: EqDecision QuerySymbol ;
    QuerySymbol_countable :: Countable QuerySymbol ;

    ProgramT : Type ;
    pi_symbol_interp :
        ProgramT -> 
        QuerySymbol -> 
        list (@TermOver' symbol builtin_value) ->
        (@TermOver' symbol builtin_value) ;
}.

Class StaticModel := mkStaticModel {
    symbol : Type ;
    variable : Type ;
    symbols :: Symbols symbol ;
    NondetValue : Type ;
    signature :: Signature ;
    builtin :: Model signature NondetValue;
    variables :: MVariables variable ;
    program_info :: ProgramInfo ;
    nondet_gen : nat -> NondetValue ;
    (* nondet_stream : Stream NondetValue ; *)
}.

(* A class for querying variables of syntactic constructs. *)
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
Instance VarsOf_symbol
    {Σ : StaticModel}
    : VarsOf symbol variable
:= {|
    vars_of := fun _ => ∅ ; 
|}.

#[export]
Instance VarsOf_builtin
    {Σ : StaticModel}
    : VarsOf builtin_value variable
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
    {Σ : StaticModel}
    :=
| e_ground (e : @TermOver' (symbol) builtin_value)
| e_variable (x : variable)
| e_fun (f : builtin_function_symbol) (l : list Expression2)
| e_query (q : QuerySymbol) (l : list Expression2)
.
Set Elimination Schemes.

Section custom_induction_principle.

    Context
        {Σ : StaticModel}
        (P : Expression2 -> Prop)
        (true_for_ground : forall e, P (e_ground e))
        (true_for_var : forall x, P (e_variable x))
        (preserved_by_fun :
            forall
                (f : builtin_function_symbol)
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
    .

    Fixpoint Expression2_ind (e : Expression2) : P e :=
    match e with
    | e_ground g => true_for_ground g
    | e_variable x => true_for_var x
    | e_fun f l => preserved_by_fun f l  (Forall_true P l Expression2_ind)
    | e_query q l => preserved_by_query q l (Forall_true P l Expression2_ind)
    end.

End custom_induction_principle.


Fixpoint vars_of_Expression2
    {Σ : StaticModel}
    (t : Expression2)
    : gset variable :=
match t with
| e_ground _ => ∅
| e_variable x => {[x]}
| e_fun _ l => ⋃ (fmap vars_of_Expression2 l)
| e_query _ l => ⋃ (fmap vars_of_Expression2 l)
end.


#[export]
Instance VarsOf_Expression2
    {Σ : StaticModel}
    : VarsOf Expression2 variable
:= {|
    vars_of := vars_of_Expression2 ; 
|}.


Inductive BuiltinOrVar {Σ : StaticModel} :=
| bov_builtin (b : builtin_value)
| bov_variable (x : variable)
.

Definition TermOver {Σ : StaticModel} (A : Type) : Type := @TermOver' symbol A.

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

Definition TermOver_map
    {Σ : StaticModel}
    {A B : Type}
    (f : A -> B)
    (t : TermOver A)
:=
    TermOver'_map f t
.

Definition TermOverBuiltin_to_TermOverBoV
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : TermOver BuiltinOrVar
:=
    TermOver_map bov_builtin t
.


Inductive SideCondition {Σ : StaticModel} :=
| sc_true
| sc_false
| sc_atom (pred : builtin_predicate_symbol) (args : list Expression2)
| sc_and (left : SideCondition) (right : SideCondition)
| sc_or (left : SideCondition) (right : SideCondition)
.

#[export]
Instance VarsOf_list_something
    {Σ : StaticModel}
    {A : Type}
    {_VA: VarsOf A variable}
    : VarsOf (list A) variable
:= {|
    vars_of := fun scs => ⋃ (vars_of <$> scs)
|}.

Fixpoint vars_of_sc {Σ : StaticModel} (sc : SideCondition) : gset variable :=
match sc with
| sc_true => ∅
| sc_false => ∅
| sc_atom _ args => vars_of args
| sc_and l r => vars_of_sc l ∪ vars_of_sc r
| sc_or l r => vars_of_sc l ∪ vars_of_sc r
end
.

#[export]
Instance  VarsOf_sc
    {Σ : StaticModel}
    : VarsOf SideCondition variable
:= {|
    vars_of := vars_of_sc ;
|}.

Record RewritingRule2
    {Σ : StaticModel}
    (Act : Set)
:= mkRewritingRule2
{
    r_from : TermOver BuiltinOrVar ;
    r_to : TermOver Expression2 ;
    r_scs : SideCondition ;
    r_act : Act ;
}.

Arguments r_from {Σ} {Act%_type_scope} r.
Arguments r_to {Σ} {Act%_type_scope} r.
Arguments r_scs {Σ} {Act%_type_scope} r.
Arguments r_act {Σ} {Act%_type_scope} r.


Definition vars_of_BoV
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : gset variable
:=
match bov with
| bov_variable x => {[x]}
| bov_builtin _ => ∅
end.

#[export]
Instance VarsOf_BoV
    {Σ : StaticModel}
    : VarsOf BuiltinOrVar variable
:= {|
    vars_of := vars_of_BoV ; 
|}.


#[export]
Instance VarsOf_TermOver_BuiltinOrVar
    {Σ : StaticModel}
    :
    VarsOf (TermOver BuiltinOrVar) variable
.
Proof.
    apply VarsOf_TermOver.
Defined.

#[export]
Instance VarsOf_TermOver_Expression2
    {Σ : StaticModel}
    :
    VarsOf (TermOver Expression2) variable
.
Proof.
    apply VarsOf_TermOver.
Defined.

(* A rewriting theory is a list of rewriting rules. *)
Definition RewritingTheory2
    {Σ : StaticModel}
    (Act : Set)
    := list (RewritingRule2 Act)
.

(*
    Interface representing the satisfaction relation (⊨)
    between various things.
*)
Class Satisfies
    {Σ : StaticModel}
    (V A B var : Type)
    {_SV : SubsetEq V}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV: VarsOf V var}
    :=
mkSatisfies {
    (*
        `satisfies` lives in `Type`, because (1) the lowlevel language
         uses `Inductive`s to give meaning to `satisfies`,
         and in the translation from MinusL we need to do case analysis on these
         whose result is not in Prop.
    *)
    satisfies :
        V -> A -> B -> Type ;
}.

Arguments satisfies : simpl never.

(* A valuation is a mapping from variables to groun terms. *)
(* TODO why not making this a notation? *)
Definition Valuation2
    {Σ : StaticModel}
:=
    gmap variable (TermOver builtin_value)
.

(* TODO Do we even need this?*)
#[export]
Instance Subseteq_Valuation2 {Σ : StaticModel}
    : SubsetEq Valuation2
.
Proof.
    unfold Valuation2.
    apply _.
Defined.

#[export]
Instance VarsOf_Valuation2_
    {Σ : StaticModel}
    {var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    : VarsOf (gmap var (TermOver BuiltinOrVar)) var
:= {|
    vars_of := fun ρ => dom ρ ; 
|}.

#[export]
Instance VarsOf_Valuation2
    {Σ : StaticModel}
    : VarsOf (Valuation2) variable
:= {|
    vars_of := fun ρ => dom ρ ; 
|}.

Definition Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (bv : BuiltinOrVar)
    : Prop
:= match bv with
    | bov_builtin b => t = t_over b
    | bov_variable x => ρ !! x = Some t
    end
.

#[export]
Instance Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar_instnace
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        (BuiltinOrVar)
        variable
:= {|
    satisfies := fun ρ tg ts => Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar ρ tg ts ;
|}.

Equations? sat2B
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
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
    unfold satisfies in *; simpl in *;
    simpl;
    apply take_drop_middle in pf1;
    rewrite <- pf1;
    rewrite sum_list_with_app; simpl;
    ltac1:(lia)).
Defined.

Fixpoint Expression2_evaluate
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (t : Expression2)
    : NondetValue -> option (TermOver builtin_value) :=
match t with
| e_ground e => fun _ =>  Some (e)
| e_variable x =>
    match ρ !! x with
    | Some v => fun _ =>  Some (v)
    | None => fun _ => None
    end
| e_query q l =>
    fun nv =>
    let es' := (fun e => Expression2_evaluate program ρ e nv) <$> l in
    es ← list_collect es';
    Some (pi_symbol_interp program q es)
| e_fun f l =>
    fun nv =>
    let es' := (fun e => Expression2_evaluate program ρ e nv) <$> l in
    es ← list_collect es';
    builtin_function_interp f nv es
end.


Equations? sat2E
    {Σ : StaticModel}
    (program : ProgramT)
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver Expression2)
    (nv : NondetValue)
    : Prop
    by wf (TermOver_size φ) lt
:=
    sat2E program ρ t (t_over e) nv :=
        match Expression2_evaluate program ρ e nv with 
        | Some t' => t' = t
        | None => False
        end ;
    sat2E program ρ (t_over a) (t_term s l) _ := False ;
    sat2E program ρ (t_term s' l') (t_term s l) nv := 
        s' = s /\
        length l' = length l /\
        forall i t' φ' (pf1 : l !! i = Some φ') (pf2 : l' !! i = Some t'),
            sat2E program ρ t' φ' nv
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


#[export]
Instance Satisfies_TermOverBuiltin_TermOverExpression2
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (ProgramT*(NondetValue*(TermOver builtin_value)))
        (TermOver Expression2)
        variable
:= {|
    satisfies := fun ρ tgnv ts => sat2E tgnv.1 ρ (tgnv.2.2) ts (tgnv.2.1) ;
|}.

Definition SideCondition_evaluate
    {Σ : StaticModel}
    (program : ProgramT)
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
        | sc_atom pred args => (
            let ts' := (fun e => Expression2_evaluate program ρ e nv) <$> args in
            ts ← list_collect ts';
            builtin_predicate_interp pred nv ts
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

#[export]
Instance Satisfies_SideCondition
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (ProgramT*NondetValue)
        SideCondition
        variable
:= {|
    satisfies := fun ρ pgnv sc =>
        SideCondition_evaluate pgnv.1 ρ pgnv.2 sc = Some true
|}.

#[export]
Instance Satisfies_Valuation2_TermOverBuiltin_TermOverBoV
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        (TermOver builtin_value)
        (TermOver BuiltinOrVar)
        variable
:= {|
    satisfies := fun ρ tg ts => sat2B ρ tg ts
|}.

Definition rewrites_in_valuation_under_to
    {Σ : StaticModel}
    {Act : Set}
    (program : ProgramT)
    (ρ : Valuation2)
    (r : RewritingRule2 Act)
    (from : TermOver builtin_value)
    (under : Act)
    (nv : NondetValue)
    (to : TermOver builtin_value)
    : Type
:= ((satisfies ρ from (r_from r))
* (satisfies ρ (program,(nv,to)) (r_to r))
* (satisfies ρ (program,nv) (r_scs r))
* (under = r_act r)
)%type
.

Definition rewrites_to
    {Σ : StaticModel}
    {Act : Set}
    (program : ProgramT)
    (r : RewritingRule2 Act)
    (from : TermOver builtin_value)
    (under : Act)
    (nv : NondetValue)
    (to : TermOver builtin_value)
    : Type
:= { ρ : Valuation2 &
        rewrites_in_valuation_under_to program ρ r from under nv to
   }
.

Definition rewriting_relation
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    (program : ProgramT)
    (nv : NondetValue)
    : TermOver builtin_value -> TermOver builtin_value -> Type
    := fun from to =>
        { r : _ & { a : _ & ((r ∈ Γ) * rewrites_to program r from a nv to)%type}}
.

Definition rewrites_to_nondet
    {Σ : StaticModel}
    {Act : Set}
    (program : ProgramT)
    (r : RewritingRule2 Act)
    (from : TermOver builtin_value)
    (under : Act)
    (to : TermOver builtin_value)
    : Type
:= { nv : NondetValue &
        rewrites_to program r from under nv to
   }
.

Definition rewrites_to_thy
    {Σ : StaticModel}
    {Act : Set}
    (program : ProgramT)
    (Γ : RewritingTheory2 Act)
    (from : TermOver builtin_value)
    (under : Act)
    (to : TermOver builtin_value)
:= { r : RewritingRule2 Act &
    ((r ∈ Γ)*(rewrites_to_nondet program r from under to))%type

}
.

Record BuiltinsBinding := {
    bb_function_names : list (string * string) ;
}.


Variant SymbolInfo {Σ0 : Signature} :=
| si_none
| si_predicate (p : builtin_predicate_symbol) (ar : nat) (np : option string)
| si_function (f : builtin_function_symbol)
.
