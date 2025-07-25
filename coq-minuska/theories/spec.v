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
}.

Class HiddenSignature := {
    AttributeSymbol : Type;
    AttributeSymbol_eqdec :: EqDecision AttributeSymbol ;
    AttributeSymbol_countable :: Countable AttributeSymbol ;

    MethodSymbol : Type ;
    MethodSymbol_eqdec :: EqDecision MethodSymbol ;
    MethodSymbol_countable :: Countable MethodSymbol ;

    HiddenPredicateSymbol : Type ;
    HiddenPredicateSymbol_eqdec :: EqDecision HiddenPredicateSymbol;
    HiddenPredicateSymbol_countable :: Countable HiddenPredicateSymbol;
}.

Class ModelOver {symbol : Type} {symbols : Symbols symbol} (signature : Signature) (NondetValue : Type) (Carrier : Type) := {        
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
}.

Class Model {symbol : Type} {symbols : Symbols symbol} (signature : Signature) (NondetValue : Type) := {
    builtin_value
        : Type ;

    builtin_value_eqdec
        :: EqDecision builtin_value ;

    builtin_value_countable
        :: Countable builtin_value ;

    builtin_model_over :: ModelOver signature NondetValue builtin_value ;
}.


Class HiddenModel
    {symbol : Type}
    {symbols : Symbols symbol}
    (signature : Signature)
    (hidden_signature : HiddenSignature)
    {NondetValue : Type}
    (M : Model signature NondetValue)
    :=
{
    hidden_data : Type ;
    
    attribute_interpretation :
        AttributeSymbol ->
        hidden_data ->
        list (@TermOver' symbol builtin_value) ->
        option builtin_value ;
    

    method_interpretation:
        MethodSymbol ->
        hidden_data ->
        list (@TermOver' symbol builtin_value) ->
        option hidden_data ;

    hidden_predicate_interpretation :
        HiddenPredicateSymbol ->
        hidden_data ->
        list (@TermOver' symbol builtin_value) ->
        option bool ;

    hidden_init : hidden_data ;
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
        option (@TermOver' symbol builtin_value) ;
}.

Class StaticModel := mkStaticModel {
    symbol : Type ;
    variable : Type ;
    symbols :: Symbols symbol ;
    NondetValue : Type ;
    signature :: Signature ;
    hidden_signature :: HiddenSignature ;
    builtin :: Model signature NondetValue;
    hidden :: HiddenModel signature hidden_signature builtin ;
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
| e_attr (a : AttributeSymbol) (l : list Expression2)
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
        (preserved_by_attribute :
            forall
                (q : AttributeSymbol)
                (l : list Expression2),
                Forall P l ->
                P (e_attr q l)
        )
    .

    Fixpoint Expression2_ind (e : Expression2) : P e :=
    match e with
    | e_ground g => true_for_ground g
    | e_variable x => true_for_var x
    | e_fun f l => preserved_by_fun f l  (Forall_true P l Expression2_ind)
    | e_query q l => preserved_by_query q l (Forall_true P l Expression2_ind)
    | e_attr q l => preserved_by_attribute q l (Forall_true P l Expression2_ind)
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
| e_attr _ l => ⋃ (fmap vars_of_Expression2 l)
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
(* positive literal *)
| sc_pred (pred : builtin_predicate_symbol) (args : list Expression2)
(* negative literal *)
| sc_npred (pred : builtin_predicate_symbol) (args : list Expression2)
(* Positive literal over hidden data. NOTE: we do not have negatives over hiden data *)
| sc_hpred (pred : HiddenPredicateSymbol) (args : list Expression2)
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
| sc_pred _ args => vars_of args
| sc_npred _ args => vars_of args
| sc_hpred _ args => vars_of args
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

Variant BasicEffect {Σ : StaticModel} := 
| be_method (s : MethodSymbol) (args : list Expression2)
(* This is like a binder *)
| be_remember (x : variable) (e : Expression2)
.

Definition Effect {Σ : StaticModel} : Type :=
    list BasicEffect
.

Definition vars_of_Effect'
    {Σ : StaticModel}
    (f : Effect)
    : gset variable
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
Instance VarsOf_Effect
    {Σ : StaticModel}
    : VarsOf Effect variable
:= {|
    vars_of := vars_of_Effect' ; 
|}.


Record RewritingRule2
    {Σ : StaticModel}
    (Label : Set)
:= mkRewritingRule2
{
    r_from : TermOver BuiltinOrVar ;
    r_to : TermOver Expression2 ;
    r_scs : SideCondition ;
    r_eff : Effect ;
    r_label : Label ;
}.

Arguments r_from {Σ} {Label%_type_scope} r.
Arguments r_to {Σ} {Label%_type_scope} r.
Arguments r_scs {Σ} {Label%_type_scope} r.
Arguments r_eff {Σ} {Label%_type_scope} r.
Arguments r_label {Σ} {Label%_type_scope} r.


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
    (Label : Set)
    := list (RewritingRule2 Label)
.


(* A valuation is a mapping from variables to groun terms. *)
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
    simpl in *;
    simpl;
    apply take_drop_middle in pf1;
    rewrite <- pf1;
    rewrite sum_list_with_app; simpl;
    ltac1:(lia)).
Defined.

Fixpoint Expression2_evaluate
    {Σ : StaticModel}
    (program : ProgramT)
    (h : hidden_data)
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
    let es' := (fun e => Expression2_evaluate program h ρ e nv) <$> l in
    es ← list_collect es';
    pi_symbol_interp program q es
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
    {Σ : StaticModel}
    (program : ProgramT)
    (h : hidden_data)
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver Expression2)
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
    {Σ : StaticModel}
    (program : ProgramT)
    (h : hidden_data)
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

Definition BasicEffect_evaluate
    {Σ : StaticModel}
    (program : ProgramT)
    (h : hidden_data)
    (ρ : Valuation2)
    (nv : NondetValue)
    (f : BasicEffect)
    : option (hidden_data*Valuation2)
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

Definition Effect_evaluate'
    {Σ : StaticModel}
    (program : ProgramT)
    (h : hidden_data)
    (ρ : Valuation2)
    (nv : NondetValue)
    (f : Effect)
    : option (hidden_data*Valuation2)
:=
    (fold_right
        (fun (bf : BasicEffect) (p' : option (hidden_data*Valuation2)) => p ← p'; BasicEffect_evaluate program p.1 p.2 nv bf)
        (Some (h,ρ))
        f
    )
.


Definition Effect_evaluate
    {Σ : StaticModel}
    (program : ProgramT)
    (h : hidden_data)
    (ρ : Valuation2)
    (nv : NondetValue)
    (f : Effect)
    : option hidden_data
:=
    fmap fst (Effect_evaluate' program h ρ nv f)
.

Definition rewrites_in_valuation_under_to
    {Σ : StaticModel}
    {Label : Set}
    (program : ProgramT)
    (ρ : Valuation2)
    (r : RewritingRule2 Label)
    (from : (TermOver builtin_value)*(hidden_data))
    (under : Label)
    (nv : NondetValue)
    (to : (TermOver builtin_value)*(hidden_data))
    : Type
:= ((sat2B ρ from.1 (r_from r))
* (sat2E program from.2 ρ to.1 (r_to r) nv)
* (SideCondition_evaluate program from.2 ρ nv (r_scs r) = Some true)
* (Some to.2 = Effect_evaluate program from.2 ρ nv (r_eff r))
* (under = r_label r)
)%type
.

Definition rewrites_to
    {Σ : StaticModel}
    {Label : Set}
    (program : ProgramT)
    (r : RewritingRule2 Label)
    (from : (TermOver builtin_value)*(hidden_data))
    (under : Label)
    (nv : NondetValue)
    (to : (TermOver builtin_value)*(hidden_data))
    : Type
:= { ρ : Valuation2 &
        rewrites_in_valuation_under_to program ρ r from under nv to
   }
.

Definition rewriting_relation
    {Σ : StaticModel}
    {Label : Set}
    (Γ : list (RewritingRule2 Label))
    (program : ProgramT)
    (nv : NondetValue)
    : (TermOver builtin_value)*(hidden_data) -> (TermOver builtin_value)*(hidden_data) -> Type
    := fun from to =>
        { r : _ & { a : _ & ((r ∈ Γ) * rewrites_to program r from a nv to)%type}}
.

Definition rewrites_to_nondet
    {Σ : StaticModel}
    {Label : Set}
    (program : ProgramT)
    (r : RewritingRule2 Label)
    (from : (TermOver builtin_value)*(hidden_data))
    (under : Label)
    (to : (TermOver builtin_value)*(hidden_data))
    : Type
:= { nv : NondetValue &
        rewrites_to program r from under nv to
   }
.

Definition rewrites_to_thy
    {Σ : StaticModel}
    {Label : Set}
    (program : ProgramT)
    (Γ : RewritingTheory2 Label)
    (from : (TermOver builtin_value)*(hidden_data))
    (under : Label)
    (to : (TermOver builtin_value)*(hidden_data))
:= { r : RewritingRule2 Label &
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
