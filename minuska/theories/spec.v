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

(*
    Interface for builtin data types.
    We differentiate between nulary, unary, binary, and ternary
    function symbols in order not to have to dependently encode arity.
    Functions of higher arity are rare (and usually they are a sign of a poor design of the type).
    TODO: explore having them as functions from lists to option type
    - we evaluate expressions into option type anyway.
*)
Class Builtin {symbol : Type} {symbols : Symbols symbol} (NondetValue : Type) := {
    builtin_value
        : Type ;
    builtin_value_eqdec
        :: EqDecision builtin_value ;
    
    builtin_nullary_function
        : Type ;
    builtin_nullary_function_eqdec
        :: EqDecision builtin_nullary_function ;

    builtin_unary_function
        : Type ;
    builtin_unary_function_eqdec
        :: EqDecision builtin_unary_function ;

    builtin_binary_function
        : Type ;
    builtin_binary_function_eqdec
        :: EqDecision builtin_binary_function ;
    
    builtin_ternary_function
        : Type ;
    builtin_ternary_function_eqdec
        :: EqDecision builtin_ternary_function ;

    builtin_nullary_function_interp
        : builtin_nullary_function
        -> (NondetValue -> @TermOver' symbol builtin_value) ;

    builtin_unary_function_interp
        : builtin_unary_function
        -> (@TermOver' symbol builtin_value)
        -> (NondetValue -> @TermOver' symbol builtin_value) ;

    builtin_binary_function_interp
        : builtin_binary_function
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value)
        -> (NondetValue -> @TermOver' symbol builtin_value) ;

    builtin_ternary_function_interp
        : builtin_ternary_function
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value)
        -> (@TermOver' symbol builtin_value)
        -> (NondetValue -> @TermOver' symbol builtin_value) ;
}.

Set Primitive Projections.
CoInductive Stream (A : Type) : Type := Seq {
    hd : A;
    tl : Stream A ;
}.

Class StaticModel := {
    symbol : Type ;
    variable : Type ;
    symbols :: Symbols symbol ;
    NondetValue : Type ;
    builtin :: Builtin NondetValue;
    variables :: MVariables variable ;
    nondet_stream : Stream NondetValue ;
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

Inductive Expression2
    {Σ : StaticModel}
    :=
| e_ground (e : @TermOver' (symbol) builtin_value)
| e_variable (x : variable)
| e_nullary (f : builtin_nullary_function)
| e_unary (f : builtin_unary_function) (t : Expression2)
| e_binary (f : builtin_binary_function) (t1 : Expression2) (t2 : Expression2)
| e_ternary (f : builtin_ternary_function) (t1 : Expression2) (t2 : Expression2) (t3 : Expression2)
.


Fixpoint vars_of_Expression2
    {Σ : StaticModel}
    (t : Expression2)
    : gset variable :=
match t with
| e_ground _ => ∅
| e_variable x => {[x]}
| e_nullary _ => ∅
| e_unary _ t' => vars_of_Expression2 t'
| e_binary _ t1 t2 => vars_of_Expression2 t1 ∪ vars_of_Expression2 t2
| e_ternary _ t1 t2 t3 => vars_of_Expression2 t1 ∪ vars_of_Expression2 t2 ∪ vars_of_Expression2 t3
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


Fixpoint TermOver_map
    {Σ : StaticModel}
    {A B : Type}
    (f : A -> B)
    (t : TermOver A)
    : TermOver B
:=
    match t with
    | t_over b => t_over (f b)
    | t_term s l => t_term s (map (TermOver_map f) l)
    end
.

Definition TermOverBuiltin_to_TermOverBoV
    {Σ : StaticModel}
    (t : TermOver builtin_value)
    : TermOver BuiltinOrVar
:=
    TermOver_map bov_builtin t
.

Record SideCondition2
    {Σ : StaticModel}
    :=
mkSideCondition2 {
    sc_left: Expression2 ;
    sc_right: Expression2 ;
}.

#[export]
Instance VarsOf_SideCondition2
    {Σ : StaticModel}
    : VarsOf SideCondition2 variable
:= {|
    vars_of := fun c => vars_of (sc_left c) ∪ vars_of (sc_right c) ; 
|}.

#[export]
Program Instance VarsOf_list_something
    {Σ : StaticModel}
    {A : Type}
    {_VA: VarsOf A variable}
    : VarsOf (list A) variable
:= {|
    vars_of := fun scs => ⋃ (vars_of <$> scs)
|}.

Record RewritingRule2
    {Σ : StaticModel}
    (Act : Set)
:= mkRewritingRule2
{
    r_from : TermOver BuiltinOrVar ;
    r_to : TermOver Expression2 ;
    r_scs : list SideCondition2 ;
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
Definition Valuation2
    {Σ : StaticModel}
:=
    gmap variable (TermOver builtin_value)
.


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
    (ρ : Valuation2)
    (t : Expression2)
    : option (NondetValue -> TermOver builtin_value) :=
match t with
| e_ground e => Some (fun _ => e)
| e_variable x =>
    match ρ !! x with
    | Some v => Some (fun _ => v)
    | None => None
    end
| e_nullary f =>
    Some (fun nv => (builtin_nullary_function_interp f nv))
| e_unary f t =>
    e ← Expression2_evaluate ρ t;
    Some (fun nv => (builtin_unary_function_interp f (e nv) nv))
| e_binary f t1 t2 =>
    e1 ← Expression2_evaluate ρ t1;
    e2 ← Expression2_evaluate ρ t2;
    Some (fun nv => (builtin_binary_function_interp f (e1 nv) (e2 nv) nv))
| e_ternary f t1 t2 t3 =>
    e1 ← Expression2_evaluate ρ t1;
    e2 ← Expression2_evaluate ρ t2;
    e3 ← Expression2_evaluate ρ t3;
    Some (fun nv => (builtin_ternary_function_interp f (e1 nv) (e2 nv) (e3 nv) nv))
end.


Equations? sat2E
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver Expression2)
    (nv : NondetValue)
    : Prop
    by wf (TermOver_size φ) lt
:=
    sat2E ρ t (t_over e) nv :=
        match Expression2_evaluate ρ e with 
        | Some f => f nv = t
        | None => False
        end ;
    sat2E ρ (t_over a) (t_term s l) _ := False ;
    sat2E ρ (t_term s' l') (t_term s l) nv := 
        s' = s /\
        length l' = length l /\
        forall i t' φ' (pf1 : l !! i = Some φ') (pf2 : l' !! i = Some t'),
            sat2E ρ t' φ' nv
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
        (NondetValue*(TermOver builtin_value))
        (TermOver Expression2)
        variable
:= {|
    satisfies := fun ρ tgnv ts => sat2E ρ tgnv.2 ts tgnv.1 ;
|}.

#[export]
Instance Satisfies_SideCondition2
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        NondetValue
        SideCondition2
        variable
:= {|
    satisfies := fun ρ nv sc =>
        match (Expression2_evaluate ρ (sc_left sc)),(Expression2_evaluate ρ (sc_right sc)) with
        | Some v1, Some v2 => v1 nv = v2 nv
        | _, _ => False
        end
|}.


#[export]
Instance Satisfies_Valuation2_scs2
    {Σ : StaticModel}
    : Satisfies
        Valuation2
        NondetValue
        (list SideCondition2)
        variable
:= {|
    satisfies := fun ρ nv l => forall x, x ∈ l -> satisfies ρ nv x;
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
    (ρ : Valuation2)
    (r : RewritingRule2 Act)
    (from : TermOver builtin_value)
    (under : Act)
    (nv : NondetValue)
    (to : TermOver builtin_value)
    : Type
:= ((satisfies ρ from (r_from r))
* (satisfies ρ (nv,to) (r_to r))
* (satisfies ρ nv (r_scs r))
* (under = r_act r)
)%type
.

Definition rewrites_to
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule2 Act)
    (from : TermOver builtin_value)
    (under : Act)
    (to : TermOver builtin_value)
    : Type
:= { ρ : Valuation2 &
    { nv : NondetValue &
        rewrites_in_valuation_under_to ρ r from under nv to
    }
   }
.

Definition rewriting_relation
    {Σ : StaticModel}
    {Act : Set}
    (Γ : list (RewritingRule2 Act))
    : TermOver builtin_value -> TermOver builtin_value -> Type
    := fun from to =>
        { r : _ & { a : _ & ((r ∈ Γ) * rewrites_to r from a to)%type}}
.
