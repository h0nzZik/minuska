From Minuska Require Import
    prelude
    spec_syntax
.



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
        V -> A -> B -> Prop ;
}.

Arguments satisfies : simpl never.


Definition val_satisfies_ap
    {Σ : StaticModel} (ρ : Valuation) (ap : AtomicProposition)
    : Prop :=
match ap with
| apeq e1 e2 => 
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    v1 = v2 /\ is_Some v1
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
    {_S2 : Satisfies V (Y) (AppliedOperator' X Z) var}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) Z var}

    :
    V ->
    ((AppliedOperator' X Y)) ->
    AppliedOperator' X Z ->
    Prop :=

| asa_x:
    forall ρ x,
        aoxy_satisfies_aoxz
            ρ
            (@ao_operator X Y x)
            (@ao_operator X Z x)

| asa_operand:
    forall ρ aoxy aoxz y z,
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ y z ->
        aoxy_satisfies_aoxz
            ρ
            (ao_app_operand aoxy y)
            (ao_app_operand aoxz z)

| asa_operand_asa:
    forall ρ aoxy aoxz aoxy2 z,
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ aoxy2 z ->
        aoxy_satisfies_aoxz
        (* The right-side, the symbolic one, has more compact representation - so *)
            ρ
            (ao_app_ao aoxy aoxy2)
            (ao_app_operand aoxz z)

| asa_asa_operand:
    forall
        (ρ : V)
        (aoxy : AppliedOperator' X Y)
        (aoxz aoxz2 : AppliedOperator' X Z)
        (y : Y),
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ y aoxz2 ->
        aoxy_satisfies_aoxz
            ρ
            (ao_app_operand aoxy y)
            ((ao_app_ao aoxz aoxz2))

| asa_asa:
    forall ρ aoxy1 aoxy2 aoxz1 aoxz2,
        aoxy_satisfies_aoxz ρ aoxy1 aoxz1 ->
        aoxy_satisfies_aoxz ρ aoxy2 aoxz2 ->
        aoxy_satisfies_aoxz
            ρ
            (ao_app_ao aoxy1 aoxy2)
            (ao_app_ao aoxz1 aoxz2)
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
    {_S2 : Satisfies V (Y) (AppliedOperator' X Z) var}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) Z var}
    :
    Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z) var
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
    {_S2 : Satisfies V ((AppliedOperator' X Y)) Z var}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z) var}
    : V ->
        ((AppliedOperatorOr' X Y)) ->
        (AppliedOperatorOr' X Z) ->
        Prop
:=
| axysaxz_app:
    forall
        (ρ : V)
        (xy : AppliedOperator' X Y)
        (xz : AppliedOperator' X Z)
        (pf : satisfies ρ xy xz),
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@aoo_app _ _  xy) (aoo_app xz)

| axysaxz_operand:
    forall (ρ : V) (y : Y) (z : Z) (pf : satisfies ρ y z),
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@aoo_operand X Y y) (@aoo_operand X Z z)

| axysaxz_combined:
    forall (ρ : V) axy axz,
        satisfies ρ axy axz ->
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@aoo_app _ _  axy) (@aoo_operand X Z axz)
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
    {_S2 : Satisfies V ((AppliedOperator' X Y)) Z var}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z) var}
    :
    Satisfies V ((AppliedOperatorOr' X Y)) (AppliedOperatorOr' X Z) var
:= {|
    satisfies := aoxyo_satisfies_aoxzo V X Y Z var;
|}.

Inductive builtin_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    :
    builtin_value ->
    BuiltinOrVar ->
    Prop :=

| bsbv_builtin:
    forall b,
        builtin_satisfies_BuiltinOrVar ρ b (bov_builtin b)

| bsbv_var:
    forall (b : builtin_value) (x : variable),
        ρ !! x = Some (@aoo_operand symbol builtin_value b) ->
        builtin_satisfies_BuiltinOrVar ρ b (bov_variable x)
.

Definition builtin_satisfies_BuiltinOrVar'
    {Σ : StaticModel}
    (ρ : Valuation)
    (b : builtin_value)
    (bov : BuiltinOrVar)
    : Prop
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

Definition AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : AppliedOperator' symbol builtin_value)
    (bov : BuiltinOrVar)
    : Prop :=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app aop)
end.

#[export]
Program Instance Satisfies__AppliedOperator'_symbol_builtin__BuiltinOrVar
    {Σ : StaticModel}
    : Satisfies Valuation ((AppliedOperator' symbol builtin_value)) BuiltinOrVar variable
:= {| 
    satisfies := AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar
|}.

Definition AppliedOperator'_symbol_builtin_satisfies'_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : (AppliedOperator' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Prop
:= AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ aop bov.

#[export]
Instance Satisfies_AppliedOperator'_symbol_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation ((AppliedOperator' symbol builtin_value)) BuiltinOrVar variable
:= {|
    satisfies := AppliedOperator'_symbol_builtin_satisfies'_BuiltinOrVar ;
|}.

(*
Definition aosb_satisfies_aosbf
    {Σ : StaticModel}
    {A B : Type}
    {_S1 : Satisfies Valuation (A) B}
    {_S2 : Satisfies Valuation (A) (AppliedOperator' symbol B)}
    {_S3 : Satisfies Valuation ((AppliedOperator' symbol A)) B}
    :
    Valuation ->
    ((AppliedOperator' symbol A)) ->
    AppliedOperator' symbol B ->
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
        (AppliedOperator' symbol B)
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
        ((AppliedOperator' symbol builtin_value))
        (AppliedOperator' symbol BuiltinOrVar)
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
    {_S2 : Satisfies Valuation (A) (AppliedOperator' symbol B) variable}
    {SatA'B : Satisfies Valuation ((AppliedOperator' symbol A)) B variable}
    :
    Satisfies Valuation ((AppliedOperator' symbol A)) (AppliedOperator' symbol B) variable
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
        ((AppliedOperatorOr' symbol builtin_value))
        (AppliedOperatorOr' symbol BuiltinOrVar)
        variable
.
Proof. apply _. Defined.

#[export]
Instance Satisfies_valGroundTerm_OpenTerm
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        GroundTerm
        OpenTerm
        variable
.
Proof. 
    apply _.
Defined.

Definition valuation_satisfies_sc
    {Σ : StaticModel}
    (ρ : Valuation)
    (sc : SideCondition) : Prop :=
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
    : Prop :=
match bov with
| bov_builtin b =>
    match g with
    | aoo_app _ => False
    | aoo_operand b' => b = b'
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


Definition builtin_value_satisfies_OpenTerm
    {Σ : StaticModel}
    :
    Valuation ->
    builtin_value ->
    OpenTerm ->
    Prop := fun ρ b t =>
match t with
| aoo_app _ => False
| aoo_operand bov =>
    satisfies ρ b bov
end.

#[export]
Instance Satisfies_builtin_value_OpenTerm
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        builtin_value
        OpenTerm
        variable
:= {|
    satisfies :=  builtin_value_satisfies_OpenTerm ;
|}.

Definition AppliedOperator'_symbol_builtin_value_satisfies_BOV
    {Σ : StaticModel}
    (ρ : Valuation)
    (ao : (AppliedOperator' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Prop
:=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app ao) 
end
.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin_value__BOV
    {Σ : StaticModel}
    {V : Type}
    :
    Satisfies
        Valuation
        ((AppliedOperator' symbol builtin_value))
        BuiltinOrVar
        variable
:= {|
    satisfies := AppliedOperator'_symbol_builtin_value_satisfies_BOV;
|}.

Definition AppliedOperator'_symbol_A_satisfies_OpenTermB'
    {Σ : StaticModel}
    (V A B var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (A) B var}
    {_S2 : Satisfies V ((AppliedOperator' symbol A)) B var}
    {_S3 : Satisfies V (AppliedOperator' symbol A) (AppliedOperator' symbol B) var}
    :
    V ->
    (AppliedOperator' symbol A) ->
    AppliedOperatorOr' symbol B ->
    Prop
:=  fun ρ a =>
    satisfies
    ρ (aoo_app a)
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
    {_S2 : Satisfies V ((AppliedOperator' symbol A)) B var}
    {_S3 : Satisfies V (AppliedOperator' symbol A) (AppliedOperator' symbol B) var}
    :
    Satisfies
        V
        ((AppliedOperator' symbol A))
        (AppliedOperatorOr' symbol B)
        var
:= {|
    satisfies :=
        AppliedOperator'_symbol_A_satisfies_OpenTermB' V A B var;
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
    {sat2 : Satisfies V ((AppliedOperator' symbol A)) B var}
    {sat3 : Satisfies V ((AppliedOperator' symbol A)) (AppliedOperator' symbol B) var}
    :
    Satisfies V
        ((AppliedOperatorOr' symbol A))
        (AppliedOperatorOr' symbol B)
        var
.
Proof. apply _. Defined.

Definition AppliedOperator'_symbol_builtin_satisfies_OpenTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol BuiltinOrVar) var}
    :
    V ->
    ((AppliedOperator' symbol builtin_value)) ->
    OpenTerm ->
    Prop
:=  fun ρ a =>
    satisfies ρ (aoo_app a)
.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin__OpenTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol BuiltinOrVar) var}
    :
    Satisfies V
        ((AppliedOperator' symbol builtin_value))
        OpenTerm
        var
:= {|
    satisfies :=
        AppliedOperator'_symbol_builtin_satisfies_OpenTerm ;
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
        Expression_evaluate ρ e = Some (aoo_operand b)
    ) ;
|}.


#[export]
Instance Satisfies_asb_expr
    {Σ : StaticModel}:
    Satisfies
        Valuation
        ((AppliedOperator' symbol builtin_value))
        Expression
        variable
:= {|
    satisfies := (fun ρ x e =>
        Expression_evaluate ρ e = Some (aoo_app x)
    ) ;
|}.


#[export]
Instance Satisfies__GroundTerm__RhsPattern
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) Expression var}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) Expression var}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol Expression) var}
    :
    Satisfies
        V
        GroundTerm
        RhsPattern
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

Definition GroundTerm_satisfies_OpenTerm
    {Σ : StaticModel}
    : GroundTerm -> OpenTerm -> Prop :=
    fun g φ => ∃ (ρ : Valuation), satisfies ρ g φ
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
Instance Satisfies__GroundTerm__OpenTerm_inall
    {Σ : StaticModel}
    :
    Satisfies
        unit
        GroundTerm
        OpenTerm
        variable
:= {|
    satisfies := fun _ => GroundTerm_satisfies_OpenTerm ;
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
    satisfies := fun ρ _ => Forall (satisfies ρ ());
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

Definition flattened_rewrites_in_valuation_to
    {Σ : StaticModel}
    (ρ : Valuation)
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= satisfies ρ from (fr_from r)
/\ satisfies ρ to (fr_to r)
/\ satisfies ρ () (fr_scs r)
.


Definition flattened_rewrites_to
    {Σ : StaticModel}
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= exists ρ, flattened_rewrites_in_valuation_to ρ r from to
.
