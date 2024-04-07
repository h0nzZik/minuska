From Minuska Require Import
    prelude
    spec_syntax
    syntax_properties
.

From Equations Require Export Equations.
             
             
#[local]       
Set Equations Transparent. 

Definition Valuation {Σ : StaticModel}
        := gmap variable GroundTerm
    .

#[export]
Instance VarsOf_valuation
    {Σ : StaticModel}
    {var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    : VarsOf (gmap var GroundTerm) var
:= {|
    vars_of := fun ρ => dom ρ ; 
|}.

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


(*Transparent Valuation.*)

Fixpoint Expression_evaluate
    {Σ : StaticModel}
    (ρ : gmap variable GroundTerm)
    (t : Expression)
    : option GroundTerm :=
match t with
| ft_element e => Some e
| ft_variable x => ρ !! x
| ft_nullary f =>
    Some (builtin_nullary_function_interp f)
| ft_unary f t =>
    e ← Expression_evaluate ρ t;
    Some (builtin_unary_function_interp f e)
| ft_binary f t1 t2 =>
    e1 ← Expression_evaluate ρ t1;
    e2 ← Expression_evaluate ρ t2;
    Some (builtin_binary_function_interp f e1 e2)
| ft_ternary f t1 t2 t3 =>
    e1 ← Expression_evaluate ρ t1;
    e2 ← Expression_evaluate ρ t2;
    e3 ← Expression_evaluate ρ t3;
    Some (builtin_ternary_function_interp f e1 e2 e3)
end.



Class Satisfies
    {Σ : StaticModel}
    (V A B var : Type)
    {_SV : SubsetEq V}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV: VarsOf V var}
    :=
mkSatisfies {
    satisfies :
        V -> A -> B -> Type ;
}.

Arguments satisfies : simpl never.


Definition val_satisfies_ap
    {Σ : StaticModel} (ρ : Valuation) (ap : AtomicProposition)
    : Type :=
match ap with
| apeq e1 e2 => 
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    v1 = v2 /\ isSome v1
end
.

#[export]
Program Instance Satisfies_val_ap
    {Σ : StaticModel} :
    Satisfies
        (gmap variable GroundTerm)
        unit
        AtomicProposition
        variable
:= {|
    satisfies := fun ρ u ap => val_satisfies_ap ρ ap ;
|}.


Inductive aoxy_satisfies_aoxz
    {Σ : StaticModel}
    {V X Y Z var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z var}
    {_S2 : Satisfies V (Y) (PreTerm' X Z) var}
    {_S3 : Satisfies V ((PreTerm' X Y)) Z var}

    :
    V ->
    ((PreTerm' X Y)) ->
    PreTerm' X Z ->
    Type :=

| asa_x:
    forall ρ x,
        aoxy_satisfies_aoxz
            ρ
            (@pt_operator X Y x)
            (@pt_operator X Z x)

| asa_operand:
    forall ρ aoxy aoxz y z,
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ y z ->
        aoxy_satisfies_aoxz
            ρ
            (pt_app_operand aoxy y)
            (pt_app_operand aoxz z)

| asa_operand_asa:
    forall ρ aoxy aoxz aoxy2 z,
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ aoxy2 z ->
        aoxy_satisfies_aoxz
        (* The right-side, the symbolic one, has more compact representation - so *)
            ρ
            (pt_app_ao aoxy aoxy2)
            (pt_app_operand aoxz z)

| asa_asa_operand:
    forall
        (ρ : V)
        (aoxy : PreTerm' X Y)
        (aoxz aoxz2 : PreTerm' X Z)
        (y : Y),
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ y aoxz2 ->
        aoxy_satisfies_aoxz
            ρ
            (pt_app_operand aoxy y)
            ((pt_app_ao aoxz aoxz2))

| asa_asa:
    forall ρ aoxy1 aoxy2 aoxz1 aoxz2,
        aoxy_satisfies_aoxz ρ aoxy1 aoxz1 ->
        aoxy_satisfies_aoxz ρ aoxy2 aoxz2 ->
        aoxy_satisfies_aoxz
            ρ
            (pt_app_ao aoxy1 aoxy2)
            (pt_app_ao aoxz1 aoxz2)
.


#[export]
Instance Satisfies_aoxy_aoxz
    {Σ : StaticModel}
    {V X Y Z var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z var}
    {_S2 : Satisfies V (Y) (PreTerm' X Z) var}
    {_S3 : Satisfies V ((PreTerm' X Y)) Z var}
    :
    Satisfies V ((PreTerm' X Y)) (PreTerm' X Z) var
:= {|
    satisfies := aoxy_satisfies_aoxz ;
|}.


Inductive aoxyo_satisfies_aoxzo
    {Σ : StaticModel}
    (V X Y Z var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z var}
    {_S2 : Satisfies V ((PreTerm' X Y)) Z var}
    {_S3 : Satisfies V ((PreTerm' X Y)) (PreTerm' X Z) var}
    : V ->
        ((Term' X Y)) ->
        (Term' X Z) ->
        Type
:=
| axysaxz_app:
    forall
        (ρ : V)
        (xy : PreTerm' X Y)
        (xz : PreTerm' X Z)
        (pf : satisfies ρ xy xz),
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@term_preterm _ _  xy) (term_preterm xz)

| axysaxz_operand:
    forall (ρ : V) (y : Y) (z : Z) (pf : satisfies ρ y z),
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@term_operand X Y y) (@term_operand X Z z)

| axysaxz_combined:
    forall (ρ : V) axy axz,
        satisfies ρ axy axz ->
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@term_preterm _ _  axy) (@term_operand X Z axz)
.

#[export]
Program Instance Satisfies_aoxyo_aoxzo
    {Σ : StaticModel}
    (V X Y Z var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z var}
    {_S2 : Satisfies V ((PreTerm' X Y)) Z var}
    {_S3 : Satisfies V ((PreTerm' X Y)) (PreTerm' X Z) var}
    :
    Satisfies V ((Term' X Y)) (Term' X Z) var
:= {|
    satisfies := aoxyo_satisfies_aoxzo V X Y Z var;
|}.

Inductive builtin_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    :
    builtin_value ->
    BuiltinOrVar ->
    Type :=

| bsbv_builtin:
    forall b,
        builtin_satisfies_BuiltinOrVar ρ b (bov_builtin b)

| bsbv_var:
    forall (b : builtin_value) (x : variable),
        ρ !! x = Some (@term_operand symbol builtin_value b) ->
        builtin_satisfies_BuiltinOrVar ρ b (bov_variable x)
.

Definition builtin_satisfies_BuiltinOrVar'
    {Σ : StaticModel}
    (ρ : Valuation)
    (b : builtin_value)
    (bov : BuiltinOrVar)
    : Type
:= builtin_satisfies_BuiltinOrVar ρ b bov.

#[export]
Instance Subseteq_Valuation {Σ : StaticModel}
    : SubsetEq Valuation
.
Proof.
    unfold Valuation.
    apply _.
Defined.

#[export]
Instance Satisfies_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation (builtin_value) BuiltinOrVar variable
:= {|
    satisfies := builtin_satisfies_BuiltinOrVar' ;
|}.

Definition PreTerm'_symbol_builtin_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : PreTerm' symbol builtin_value)
    (bov : BuiltinOrVar)
    : Type :=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (term_preterm aop)
end.

#[export]
Program Instance Satisfies__PreTerm'_symbol_builtin__BuiltinOrVar
    {Σ : StaticModel}
    : Satisfies Valuation ((PreTerm' symbol builtin_value)) BuiltinOrVar variable
:= {| 
    satisfies := PreTerm'_symbol_builtin_satisfies_BuiltinOrVar
|}.

Definition PreTerm'_symbol_builtin_satisfies'_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : (PreTerm' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Type
:= PreTerm'_symbol_builtin_satisfies_BuiltinOrVar ρ aop bov.

#[export]
Instance Satisfies_PreTerm'_symbol_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation ((PreTerm' symbol builtin_value)) BuiltinOrVar variable
:= {|
    satisfies := PreTerm'_symbol_builtin_satisfies'_BuiltinOrVar ;
|}.

(*
Definition aosb_satisfies_aosbf
    {Σ : StaticModel}
    {A B : Type}
    {_S1 : Satisfies Valuation (A) B}
    {_S2 : Satisfies Valuation (A) (PreTerm' symbol B)}
    {_S3 : Satisfies Valuation ((PreTerm' symbol A)) B}
    :
    Valuation ->
    ((PreTerm' symbol A)) ->
    PreTerm' symbol B ->
    Prop :=
    @aoxy_satisfies_aoxz
        Σ
        Valuation
        symbol
        A
        B
        _
        _
        _
        _
        _
.
*)

#[export]
Instance Satisfies__builtin__ao'B
    {Σ : StaticModel}
    {V B var : Type}
    {_SV : SubsetEq V}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VV : VarsOf V var}
    :
    Satisfies
        V
        (builtin_value)
        (PreTerm' symbol B)
        var
:= {| 
    satisfies := fun _ _ _ => false ;
|}.


#[export]
Instance Satisfies_aos__builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        ((PreTerm' symbol builtin_value))
        (PreTerm' symbol BuiltinOrVar)
        variable
.
Proof.
    apply @Satisfies_aoxy_aoxz.
    {
        apply _.
    }
    {
        apply Satisfies__builtin__ao'B.
    }
    {
        apply _.
    }
Defined.


#[export]
Instance Satisfies_aosb_aosbf
    {Σ : StaticModel}
    {A B : Type}
    {SatAB : Satisfies Valuation (A) B variable}
    {_S2 : Satisfies Valuation (A) (PreTerm' symbol B) variable}
    {SatA'B : Satisfies Valuation ((PreTerm' symbol A)) B variable}
    :
    Satisfies Valuation ((PreTerm' symbol A)) (PreTerm' symbol B) variable
.
Proof.
    apply _.
Defined.

#[export]
Instance
Satisfies_aoosb_aoosbf
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        ((Term' symbol builtin_value))
        (Term' symbol BuiltinOrVar)
        variable
.
Proof. apply _. Defined.

#[export]
Instance Satisfies_valGroundTerm_SymbolicTerm
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        GroundTerm
        SymbolicTerm
        variable
.
Proof. 
    apply _.
Defined.

Definition valuation_satisfies_sc
    {Σ : StaticModel}
    (ρ : Valuation)
    (sc : SideCondition) : Type :=
match sc with
| sc_constraint c => satisfies ρ () c
end.

#[export]
Instance Satisfies_val_sc
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        unit
        SideCondition
        variable
:= {|
    satisfies := fun a b c => valuation_satisfies_sc a c ;
|}.


Definition GroundTerm_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (g : GroundTerm)
    (bov : BuiltinOrVar)
    : Type :=
match bov with
| bov_builtin b =>
    match g with
    | term_preterm _ => False
    | term_operand b' => b = b'
    end
| bov_variable x => ρ !! x = Some g
end.

#[export]
Instance Satisfies_GroundTerm_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation (GroundTerm) BuiltinOrVar variable
:= {|
    satisfies := GroundTerm_satisfies_BuiltinOrVar ;
|}.


Definition builtin_value_satisfies_SymbolicTerm
    {Σ : StaticModel}
    :
    Valuation ->
    builtin_value ->
    SymbolicTerm ->
    Type := fun ρ b t =>
match t with
| term_preterm _ => False
| term_operand bov =>
    satisfies ρ b bov
end.

#[export]
Instance Satisfies_builtin_value_SymbolicTerm
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        builtin_value
        SymbolicTerm
        variable
:= {|
    satisfies :=  builtin_value_satisfies_SymbolicTerm ;
|}.

Definition PreTerm'_symbol_builtin_value_satisfies_BOV
    {Σ : StaticModel}
    (ρ : Valuation)
    (ao : (PreTerm' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Type
:=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (term_preterm ao) 
end
.

#[export]
Instance Satisfies__PreTerm'_symbol_builtin_value__BOV
    {Σ : StaticModel}
    {V : Type}
    :
    Satisfies
        Valuation
        ((PreTerm' symbol builtin_value))
        BuiltinOrVar
        variable
:= {|
    satisfies := PreTerm'_symbol_builtin_value_satisfies_BOV;
|}.

Definition PreTerm'_symbol_A_satisfies_SymbolicTermB'
    {Σ : StaticModel}
    (V A B var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (A) B var}
    {_S2 : Satisfies V ((PreTerm' symbol A)) B var}
    {_S3 : Satisfies V (PreTerm' symbol A) (PreTerm' symbol B) var}
    :
    V ->
    (PreTerm' symbol A) ->
    Term' symbol B ->
    Type
:=  fun ρ a =>
    satisfies
    ρ (term_preterm a)
.

#[export]
Instance Satisfies__lift_builtin_to_aosb
    {Σ : StaticModel}
    {V A B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (A) B var}
    {_S2 : Satisfies V ((PreTerm' symbol A)) B var}
    {_S3 : Satisfies V (PreTerm' symbol A) (PreTerm' symbol B) var}
    :
    Satisfies
        V
        ((PreTerm' symbol A))
        (Term' symbol B)
        var
:= {|
    satisfies :=
        PreTerm'_symbol_A_satisfies_SymbolicTermB' V A B var;
|}.

#[export]
Instance Satisfies__lift_builtin_to_aosbo
    {Σ : StaticModel}
    {V A B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {bsB : Satisfies V (A) B var}
    {sat2 : Satisfies V ((PreTerm' symbol A)) B var}
    {sat3 : Satisfies V ((PreTerm' symbol A)) (PreTerm' symbol B) var}
    :
    Satisfies V
        ((Term' symbol A))
        (Term' symbol B)
        var
.
Proof. apply _. Defined.

Definition PreTerm'_symbol_builtin_satisfies_SymbolicTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (PreTerm' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (PreTerm' symbol builtin_value) (PreTerm' symbol BuiltinOrVar) var}
    :
    V ->
    ((PreTerm' symbol builtin_value)) ->
    SymbolicTerm ->
    Type
:=  fun ρ a =>
    satisfies ρ (term_preterm a)
.

#[export]
Instance Satisfies__PreTerm'_symbol_builtin__SymbolicTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (PreTerm' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (PreTerm' symbol builtin_value) (PreTerm' symbol BuiltinOrVar) var}
    :
    Satisfies V
        ((PreTerm' symbol builtin_value))
        SymbolicTerm
        var
:= {|
    satisfies :=
        PreTerm'_symbol_builtin_satisfies_SymbolicTerm ;
|}.


#[local]
Obligation Tactic := idtac.

#[export]
Instance Satisfies_builtin_expr
    {Σ : StaticModel}:
    Satisfies
        Valuation
        builtin_value
        Expression
        variable
:= {|
    satisfies := (fun ρ b e =>
        Expression_evaluate ρ e = Some (term_operand b)
    ) ;
|}.


#[export]
Instance Satisfies_asb_expr
    {Σ : StaticModel}:
    Satisfies
        Valuation
        ((PreTerm' symbol builtin_value))
        Expression
        variable
:= {|
    satisfies := (fun ρ x e =>
        Expression_evaluate ρ e = Some (term_preterm x)
    ) ;
|}.


#[export]
Instance Satisfies__GroundTerm__ExpressionTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) Expression var}
    {_S2 : Satisfies V (PreTerm' symbol builtin_value) Expression var}
    {_S3 : Satisfies V (PreTerm' symbol builtin_value) (PreTerm' symbol Expression) var}
    :
    Satisfies
        V
        GroundTerm
        ExpressionTerm
        var
.
Proof. apply _. Defined.

#[export]
Instance Satisfies_gt_var
    {Σ : StaticModel}:
    Satisfies
        Valuation
        GroundTerm
        variable
        variable
:= {|
    satisfies := (fun ρ g x => ρ !! x = Some g)
|}.

#[export]
Instance Subseteq_ValuationLR
    {Σ : StaticModel}
    : SubsetEq (Valuation * LeftRight)
:= {
    subseteq a b := subseteq a.1 b.1 /\ a.2 = b.2
}.


(* TODO *)
#[export]
Instance VarsOf_ValuationLR
    {Σ : StaticModel}
    : VarsOf (Valuation * LeftRight) variable
:= {
    vars_of a := vars_of a.1
}.


#[export]
Instance Satisfies_sym_bov
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        symbol
        BuiltinOrVar
        variable
:= {|
    satisfies := fun _ _ _ => False ;
|}.


#[export]
Instance Satisfies_Valuation_LR_SideCondition
    {Σ : StaticModel}
    :
    Satisfies
        (Valuation * LeftRight)
        unit
        SideCondition
        variable
:= {|
    satisfies := fun ρd => let ρ := ρd.1 in
        satisfies ρ
        ;
|}.

Definition GroundTerm_satisfies_SymbolicTerm
    {Σ : StaticModel}
    : GroundTerm -> SymbolicTerm -> Type :=
    fun g φ => { ρ : Valuation & satisfies ρ g φ }
.

#[export]
Instance VarsOf_unit {Σ : StaticModel}: VarsOf unit variable := {|
    vars_of _ := ∅ ;
|}.

#[export]
Instance Subseteq_unit {Σ : StaticModel}: SubsetEq unit := 
    fun _ _ => true
.

#[export]
Instance Satisfies__GroundTerm__SymbolicTerm_inall
    {Σ : StaticModel}
    :
    Satisfies
        unit
        GroundTerm
        SymbolicTerm
        variable
:= {|
    satisfies := fun _ => GroundTerm_satisfies_SymbolicTerm ;
|}.

#[export]
Instance Satisfies_valuation_scs
    {Σ : StaticModel}
    : Satisfies
        Valuation
        unit
        (list SideCondition)
        variable
:= {|
    satisfies := fun ρ _ l => forall x, x ∈ l -> satisfies ρ () x;
|}.

#[export]
Instance
    Satisfies_symbol_B
    {Σ : StaticModel}
    {V B var : Type}
    {_SV : SubsetEq V}
    {_EDvar : EqDecision var}
    {_Covar : Countable var}
    {_VV : VarsOf V var}
    :
    Satisfies
        V
        symbol
        B
        var
:= {|
    satisfies := fun _ _ _ => False ;
|}.

Definition flattened_rewrites_in_valuation_under_to
    {Σ : StaticModel}
    {Act : Set}
    (ρ : Valuation)
    (r : RewritingRule Act)
    (from : GroundTerm)
    (under : Act)
    (to : GroundTerm)
    : Type
:= ((satisfies ρ from (fr_from r))
* (satisfies ρ to (fr_to r))
* (@satisfies Σ Valuation unit (list SideCondition) _ _ _ _ _ _ ρ tt (fr_scs r))
* (under = fr_act r)
)%type
.


Definition flattened_rewrites_to
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    (from : GroundTerm)
    (under : Act)
    (to : GroundTerm)
    : Type
:= { ρ : Valuation &
    flattened_rewrites_in_valuation_under_to ρ r from under to
   }
.

Definition Valuation2
    {Σ : StaticModel}
:=
    gmap variable (TermOver builtin_value)
.

Equations? sat2B 
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    : Prop
    by wf (TermOver_size φ) lt
:=
    sat2B ρ t (t_over (bov_builtin b)) := t = t_over b ;
    sat2B ρ t (t_over (bov_variable x)) := ρ !! x = Some t ;
    sat2B ρ (t_over _) (t_term s l) := False ;
    sat2B ρ (t_term s' l') (t_term s l) :=
        s' = s /\
        length l' = length l /\
        forall i t' φ' (pf1 : l !! i = Some φ') (pf2 : l' !! i = Some t'),
            sat2B ρ t' φ'
    ;
.
Proof.
    simpl.
    apply take_drop_middle in pf1.
    rewrite <- pf1.
    rewrite sum_list_with_app. simpl.
    ltac1:(lia).
Defined.

Lemma sat2B_uglify
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    : sat2B ρ t φ -> satisfies (fmap uglify' ρ) (uglify' t) (uglify' φ)
.
Proof.
    remember (TermOver_size φ) as sz.
    assert (Hsz: (TermOver_size φ) <= sz) by ltac1:(lia).
    clear Heqsz.
    revert t φ Hsz.
    induction sz; simpl; intros t φ Hsz.
    {
        destruct φ; simpl in Hsz; ltac1:(lia).
    }
    destruct φ; simpl in *; intros HH.
    {
        destruct a;
        ltac1:(simp sat2B in HH); subst; simpl.
        {
            constructor. constructor.
        }
        {
            unfold satisfies; simpl.
            destruct t; simpl; constructor.
            { 
                constructor.
                unfold Valuation2 in *. unfold Valuation in *.
                rewrite lookup_fmap.
                rewrite HH. simpl. reflexivity.
            }
            {
                unfold satisfies; simpl.
                unfold Valuation2 in *. unfold Valuation in *.
                rewrite lookup_fmap.
                rewrite HH. simpl. reflexivity.
            }
        }
    }
    {
        destruct t;
            ltac1:(simp sat2B in HH).
        { inversion HH. }
        {
            destruct HH as [H1 [H2 H3]].
            constructor.
            fold (@uglify' Σ).
            subst s0.

            revert l0 H2 H3.

            ltac1:(induction l using rev_ind_T); intros l' H2 H3.
            {
                simpl in H2.
                destruct l'; simpl in *.
                {
                    constructor.
                }
                {
                    ltac1:(lia).
                }
            }
            {
                destruct (analyze_list_from_end l') as [Hana|Hana]; simpl in *.
                { 
                    subst.
                    rewrite app_length in H2. simpl in *.
                    ltac1:(lia).
                }
                {
                    destruct Hana as [l'0 [x0 Hana]].
                    subst l'.
                    rewrite app_length in H2. simpl in *.
                    unfold to_PreTerm'.
                    do 2 (rewrite map_app).
                    do 2 (rewrite fold_left_app).
                    simpl.
                    unfold helper.
                    destruct (uglify' x0) eqn:Hux0;
                        destruct (uglify' x) eqn:Hux;
                        simpl in *.
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        simpl in *.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x x0.
                        constructor.
                        {
                            apply IHl.
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                intros.
                                apply H3 with (i := i);
                                    rewrite lookup_app_l;
                                    try assumption.
                                {
                                    apply lookup_lt_Some in pf1.
                                    exact pf1.
                                }
                                {
                                    apply lookup_lt_Some in pf2.
                                    exact pf2.
                                }
                            }
                        }
                        {
                            specialize (H3 (length l) (prettify' ao) (prettify' ao0)).
                            rewrite lookup_app_r in H3>[|ltac1:(lia)].
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            rewrite app_length in H2. simpl in H2.
                            rewrite lookup_app_r in H3>[|ltac1:(lia)].
                            ltac1:(replace ((length l - length l'0)) with (0) in H3 by lia).
                            specialize (H3 eq_refl).
                            specialize (IHsz (prettify' ao) (prettify' ao0)).
                            rewrite sum_list_with_app in Hsz. simpl in Hsz.
                            specialize (IHsz ltac:(lia) H3).
                            rewrite (uglify'_prettify') in IHsz.
                            rewrite (uglify'_prettify') in IHsz.
                            inversion IHsz; subst; clear IHsz.
                            assumption.
                        }
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        simpl in *.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x x0.
                        constructor.
                        {
                            apply IHl.
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                intros.
                                apply H3 with (i := i);
                                    rewrite lookup_app_l;
                                    try assumption.
                                {
                                    apply lookup_lt_Some in pf1.
                                    exact pf1.
                                }
                                {
                                    apply lookup_lt_Some in pf2.
                                    exact pf2.
                                }
                            }
                        }
                        {
                            specialize (H3 (length l) (prettify' ao) (t_over operand)).
                            rewrite lookup_app_r in H3>[|ltac1:(lia)].
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            rewrite app_length in H2. simpl in H2.
                            rewrite lookup_app_r in H3>[|ltac1:(lia)].
                            ltac1:(replace ((length l - length l'0)) with (0) in H3 by lia).
                            specialize (H3 eq_refl).
                            specialize (IHsz (prettify' ao) (t_over operand)).
                            rewrite sum_list_with_app in Hsz. simpl in Hsz.
                            specialize (IHsz ltac:(simpl;lia) H3).
                            rewrite (uglify'_prettify') in IHsz.
                            inversion IHsz; subst; clear IHsz.
                            assumption.
                        }
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        simpl in *.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x x0.
                        constructor.
                        {
                            apply IHl.
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                intros.
                                apply H3 with (i := i);
                                    rewrite lookup_app_l;
                                    try assumption.
                                {
                                    apply lookup_lt_Some in pf1.
                                    exact pf1.
                                }
                                {
                                    apply lookup_lt_Some in pf2.
                                    exact pf2.
                                }
                            }
                        }
                        {
                            specialize (H3 (length l) (t_over operand) (prettify' ao) ).
                            rewrite lookup_app_r in H3>[|ltac1:(lia)].
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            rewrite app_length in H2. simpl in H2.
                            rewrite lookup_app_r in H3>[|ltac1:(lia)].
                            ltac1:(replace ((length l - length l'0)) with (0) in H3 by lia).
                            specialize (H3 eq_refl).
                            specialize (IHsz (t_over operand) (prettify' ao)).
                            rewrite sum_list_with_app in Hsz. simpl in Hsz.
                            specialize (IHsz ltac:(simpl;lia) H3).
                            rewrite (uglify'_prettify') in IHsz.
                            inversion IHsz; subst; clear IHsz.
                        }
                    }
                    {
                        apply (f_equal prettify) in Hux.
                        apply (f_equal prettify) in Hux0.
                        simpl in *.
                        rewrite (cancel prettify uglify') in Hux.
                        rewrite (cancel prettify uglify') in Hux0.
                        subst x x0.
                        constructor.
                        {
                            apply IHl.
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                rewrite app_length in H2; simpl in H2.
                                rewrite sum_list_with_app in Hsz; simpl in Hsz. 
                                ltac1:(lia).
                            }
                            {
                                intros.
                                apply H3 with (i := i);
                                    rewrite lookup_app_l;
                                    try assumption.
                                {
                                    apply lookup_lt_Some in pf1.
                                    exact pf1.
                                }
                                {
                                    apply lookup_lt_Some in pf2.
                                    exact pf2.
                                }
                            }
                        }
                        {
                            specialize (H3 (length l) (t_over operand) (t_over operand0)).
                            rewrite lookup_app_r in H3>[|ltac1:(lia)].
                            rewrite Nat.sub_diag in H3. simpl in H3.
                            specialize (H3 eq_refl).
                            rewrite app_length in H2. simpl in H2.
                            rewrite lookup_app_r in H3>[|ltac1:(lia)].
                            ltac1:(replace ((length l - length l'0)) with (0) in H3 by lia).
                            specialize (H3 eq_refl).
                            specialize (IHsz (t_over operand) (t_over operand0)).
                            rewrite sum_list_with_app in Hsz. simpl in Hsz.
                            specialize (IHsz ltac:(simpl;lia) H3).
                            inversion IHsz; subst; clear IHsz.
                            assumption.
                        }
                    }
                }
            }
        }
    }
Qed.

Lemma uglify_sat2B
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : TermOver builtin_value)
    (φ : TermOver BuiltinOrVar)
    : satisfies (fmap uglify' ρ) (uglify' t) (uglify' φ)
    -> sat2B ρ t φ
.
Proof.
    remember (TermOver_size φ) as sz.
    assert (Hsz: (TermOver_size φ) <= sz) by ltac1:(lia).
    clear Heqsz.
    revert t φ Hsz.
    induction sz; simpl; intros t φ Hsz.
    {
        destruct φ; simpl in Hsz; ltac1:(lia).
    }
    destruct φ; simpl in *; intros HH.
    {
        destruct t;
            simpl in HH;
            inversion HH; subst; clear HH.
        {
            inversion pf; subst; clear pf;
            ltac1:(simp sat2B);
            try reflexivity.
            unfold Valuation in *.
            unfold Valuation2 in *.
            rewrite lookup_fmap in H.
            destruct (ρ !! x) eqn:Hρx;
                simpl in *.
            {
                inversion H; subst; clear H.
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                reflexivity.
            }
            { inversion H. }
        }
        {
            destruct a; simpl in *.
            {
                inversion X.
            }
            inversion X; subst; clear X.
            ltac1:(simp sat2B).
            unfold Valuation in *.
            unfold Valuation2 in *.
            rewrite lookup_fmap in H0.
            destruct (ρ!!x) eqn:Hρx; simpl in *.
            {
                inversion H0; subst; clear H0.
                apply (f_equal prettify) in H1.
                rewrite (cancel prettify uglify') in H1.
                subst t.
                simpl.
                apply f_equal.
                rewrite <- (cancel prettify uglify' (t_term s l)).
                unfold prettify.
                simpl. reflexivity.
            }
            { inversion H0. }
        }
    }
    {
        destruct t; simpl in *; ltac1:(simp sat2B).
        {
            inversion HH.
        }
        unfold satisfies in HH; simpl in HH.
        inversion HH; subst; clear HH.
        unfold satisfies in pf; simpl in pf.
        revert l0 Hsz pf;
        ltac1:(induction l using rev_ind_T); simpl in *;
            intros l0 Hsz pf.
        {
            destruct (analyze_list_from_end l0); subst; simpl in *.
            {
                inversion pf; subst; clear pf.
                (repeat split).
                intros.
                rewrite lookup_nil in pf1. inversion pf1.
            }
            {
                inversion pf; subst; clear pf.
                destruct s1 as [l' [x HH]].
                subst.
                rewrite map_app in H1.
                rewrite to_PreTerm'_app in H1.
                simpl in H1.
                unfold helper in H1.
                destruct (uglify' x) eqn:Hux.
                { inversion H1. }
                { inversion H1. }
            }
        }
        {
            destruct (analyze_list_from_end l0) as [Hnil|Hcons]; subst; simpl in *.
            {
                inversion pf; subst; clear pf.
                unfold to_PreTerm' in H2.
                rewrite map_app in H2.
                rewrite fold_left_app in H2.
                simpl in H2.
                unfold helper in H2.
                destruct (uglify' x) eqn:Hux; simpl in *.
                {
                    inversion H2.
                }
                {
                    inversion H2.
                }
            }
            {
                rewrite sum_list_with_app in Hsz. simpl in Hsz.
                rewrite map_app in pf.
                rewrite to_PreTerm'_app in pf.
                simpl in pf.
                unfold helper in pf.
                destruct Hcons as [l' [x0 Hcons]].
                subst l0.
                destruct (uglify' x) eqn:Hux; simpl in *.
                {
                    apply (f_equal prettify) in Hux.
                    rewrite (cancel prettify uglify') in Hux.
                    subst x.
                    simpl in *.
                    inversion pf; subst; clear pf.
                    {
                        subst. simpl in *.
                        unfold to_PreTerm' in H1.
                        rewrite map_app in H1.
                        rewrite fold_left_app in H1.
                        simpl in H1.
                        unfold helper in H1.
                        destruct (uglify' x0) eqn:Hux0; simpl in *.
                        {
                            inversion H1.
                        }
                        {
                            inversion H1; subst; clear H1.
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0.
                            simpl in *.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IHl1 [IHl2 IHl3]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length).
                            simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            destruct (decide (i = length l)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IHl2 in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                inversion H1i; subst; clear H1i.
                                inversion H2i; subst; clear H2i.
                                apply IHsz.
                                { simpl. ltac1:(lia). }
                                {
                                    inversion X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        eapply IHl3.
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in *.
                                        ltac1:(lia).
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in *.
                                    ltac1:(lia).
                                }
                            }
                        }
                    }
                    {
                        rewrite map_app in H1.
                        unfold to_PreTerm' in H1.
                        rewrite fold_left_app in H1.
                        simpl in H1.
                        unfold helper in H1.
                        destruct (uglify' x0) eqn:Hux0; simpl in *.
                        {
                            inversion H1; subst; clear H1.
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0; simpl in *.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length).
                            simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            destruct (decide (length l = i)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                inversion H1i; subst; clear H1i.
                                inversion H2i; subst; clear H2i.
                                apply IHsz.
                                { simpl. ltac1:(lia). }
                                {
                                    do 2 (rewrite uglify'_prettify' ).
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        eapply IH3l.
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        ltac1:(lia).                                        
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    ltac1:(lia).
                                }
                            }
                        }
                        {
                            inversion H1.
                        }
                    }
                }
                {
                    inversion pf; subst; clear pf.
                    {
                        apply (f_equal prettify) in Hux.
                        rewrite (cancel prettify uglify') in Hux.
                        subst x. simpl in *.
                        rewrite map_app in H1.
                        unfold to_PreTerm' in H1.
                        rewrite fold_left_app in H1.
                        simpl in H1.
                        unfold helper in H1.
                        destruct (uglify' x0) eqn:Hux0; simpl in *.
                        {
                            inversion H1.
                        }
                        {
                            inversion H1; subst; clear H1.
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0. simpl in *.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length); simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            destruct (decide (length l = i)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                inversion H1i; subst; clear H1i.
                                inversion H2i; subst; clear H2i.
                                apply IHsz.
                                { simpl. ltac1:(lia). }
                                {
                                    simpl.
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        eapply IH3l.
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        ltac1:(lia).                                        
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    ltac1:(lia).
                                }
                            }
                        }
                    }
                    {
                        unfold to_PreTerm' in H1.
                        rewrite map_app in H1.
                        rewrite fold_left_app in H1.
                        simpl in H1.
                        unfold helper in H1.
                        destruct (uglify' x0) eqn:Hux0; simpl in *.
                        {
                            inversion H1; subst; clear H1.
                            apply (f_equal prettify) in Hux0.
                            rewrite (cancel prettify uglify') in Hux0.
                            subst x0.
                            apply (f_equal prettify) in Hux.
                            rewrite (cancel prettify uglify') in Hux.
                            subst x.
                            specialize (IHl _ ltac:(lia) X).
                            destruct IHl as [IH1l [IH2l IH3l]].
                            subst s0.
                            split>[reflexivity|].
                            do 2 (rewrite app_length); simpl.
                            split>[ltac1:(lia)|].
                            intros i t' φ' H1i H2i.
                            destruct (decide (length l = i)).
                            {
                                subst i.
                                rewrite lookup_app_r in H1i>[|ltac1:(lia)].
                                rewrite lookup_app_r in H2i>[|ltac1:(lia)].
                                rewrite IH2l in H2i.
                                rewrite Nat.sub_diag in H1i.
                                rewrite Nat.sub_diag in H2i.
                                simpl in *.
                                inversion H1i; subst; clear H1i.
                                inversion H2i; subst; clear H2i.
                                apply IHsz.
                                { simpl. ltac1:(lia). }
                                {
                                    simpl.
                                    rewrite uglify'_prettify'.
                                    constructor.
                                    apply X0.
                                }
                            }
                            {
                                rewrite lookup_app_l in H1i.
                                {
                                    rewrite lookup_app_l in H2i.
                                    {
                                        eapply IH3l.
                                        { apply H1i. }
                                        { apply H2i. }
                                    }
                                    {
                                        apply lookup_lt_Some in H2i.
                                        rewrite app_length in H2i.
                                        simpl in H2i.
                                        ltac1:(lia).                                        
                                    }
                                }
                                {
                                    apply lookup_lt_Some in H1i.
                                    rewrite app_length in H1i.
                                    simpl in H1i.
                                    ltac1:(lia).
                                }
                            }
                        }
                        {
                            inversion H1.
                        }

                    }
                }
            }
        }
    }
Qed.


Fixpoint Expression2_evaluate
    {Σ : StaticModel}
    (ρ : Valuation2)
    (t : Expression2)
    : option (TermOver builtin_value) :=
match t with
| e_ground e => Some e
| e_variable x => ρ !! x
| e_nullary f =>
    Some (prettify (builtin_nullary_function_interp f))
| e_unary f t =>
    e ← Expression2_evaluate ρ t;
    Some (prettify (builtin_unary_function_interp f (uglify' e)))
| e_binary f t1 t2 =>
    e1 ← Expression2_evaluate ρ t1;
    e2 ← Expression2_evaluate ρ t2;
    Some (prettify (builtin_binary_function_interp f (uglify' e1) (uglify' e2)))
| e_ternary f t1 t2 t3 =>
    e1 ← Expression2_evaluate ρ t1;
    e2 ← Expression2_evaluate ρ t2;
    e3 ← Expression2_evaluate ρ t3;
    Some (prettify (builtin_ternary_function_interp f (uglify' e1) (uglify' e2) (uglify' e3)))
end.

Lemma Expression2_Expression_evaluate
    {Σ : StaticModel}
    (ρ : Valuation2)
    (e : Expression2)
    :
    Expression2_evaluate ρ e =
    prettify <$> (Expression_evaluate (fmap uglify' ρ) (Expression2_to_Expression e))
.
Proof.
    induction e; simpl.
    {
        rewrite (cancel prettify uglify').
        reflexivity.
    }
    {
        rewrite lookup_fmap.
        unfold Valuation in *. unfold Valuation2 in *.
        destruct (ρ !! x) eqn:Hρx; simpl.
        {
            simpl.
            rewrite (cancel prettify uglify').
            reflexivity.
        }
        {
            reflexivity.
        }
    }
    {
        reflexivity.
    }
    {
        rewrite IHe. clear IHe.
        rewrite option_fmap_bind.
        unfold compose.
        destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e))
            eqn:Heq; simpl.
        {
            rewrite (cancel uglify' prettify).
            reflexivity.
        }
        {
            reflexivity.
        }
    }
    {
        rewrite IHe1.
        rewrite IHe2.
        rewrite option_fmap_bind.
        destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e1)) eqn:Heq1;
            simpl.
        {
            rewrite option_fmap_bind.
            destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e2)) eqn:Heq2;
                simpl.
            {
                do 2 (rewrite (cancel uglify' prettify)).
                reflexivity.
            }
            {
                reflexivity.
            }
        }
        {
            reflexivity.
        }
    }
    {
        rewrite IHe1.
        rewrite IHe2.
        rewrite IHe3.

        rewrite option_fmap_bind.
        destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e1)) eqn:Heq1;
            simpl.
        {
            rewrite option_fmap_bind.
            destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e2)) eqn:Heq2;
                simpl.
            {
                rewrite option_fmap_bind.
                destruct (Expression_evaluate (uglify' <$> ρ) (Expression2_to_Expression e3)) eqn:Heq3;
                    simpl.
                {
                    do 3 (rewrite (cancel uglify' prettify)).
                    reflexivity.
                }
                {
                    reflexivity.
                }
            }
            {
                reflexivity.
            }
        }
        {
            reflexivity.
        }
    }
Qed.

#[export]
Instance Satisfies_TermOverBuiltin_TermOverBoV
    {Σ : StaticModel}
    : Satisfies
        Valuation
        (TermOver builtin_value)
        (TermOver BuiltinOrVar)
        variable
:= {|
    satisfies := fun ρ tg ts => satisfies ρ (uglify' tg) (uglify' ts) ;
|}.

#[export]
Instance Satisfies_TermOverBuiltin_TermOverExpression
    {Σ : StaticModel}
    : Satisfies
        Valuation
        (TermOver builtin_value)
        (TermOver Expression)
        variable
:= {|
    satisfies := fun ρ tg ts => satisfies ρ (uglify' tg) (uglify' ts) ;
|}.



Inductive flattened_rewrites_to_over
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    :
    TermOver builtin_value ->
    list Act ->
    TermOver builtin_value ->
    Type
:=
| frto_base: forall t,
        flattened_rewrites_to_over Γ t nil t
| frto_step: forall (t1 t2 t3 : TermOver builtin_value) w a r,
    r ∈ Γ ->
    flattened_rewrites_to r (uglify' t1) a (uglify' t2) ->
    flattened_rewrites_to_over Γ t2 w t3 ->
    flattened_rewrites_to_over Γ t1 (a::w) t3
.