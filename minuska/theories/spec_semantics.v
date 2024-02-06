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
    {_S2 : Satisfies V (Y) (PreTerm' X Z) var}
    {_S3 : Satisfies V ((PreTerm' X Y)) Z var}

    :
    V ->
    ((PreTerm' X Y)) ->
    PreTerm' X Z ->
    Prop :=

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
        Prop
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
    Prop :=

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

Definition PreTerm'_symbol_builtin_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : PreTerm' symbol builtin_value)
    (bov : BuiltinOrVar)
    : Prop :=
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
    : Prop
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
    Prop := fun ρ b t =>
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
    : Prop
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
    Prop
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
    Prop
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
    : GroundTerm -> SymbolicTerm -> Prop :=
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

Definition flattened_rewrites_in_valuation_under_to
    {Σ : StaticModel}
    {Act : Set}
    (ρ : Valuation)
    (r : RewritingRule Act)
    (from : GroundTerm)
    (under : Act)
    (to : GroundTerm)
    : Prop
:= satisfies ρ from (fr_from r)
/\ satisfies ρ to (fr_to r)
/\ satisfies ρ () (fr_scs r)
/\ under = fr_act r
.


Definition flattened_rewrites_to
    {Σ : StaticModel}
    {Act : Set}
    (r : RewritingRule Act)
    (from : GroundTerm)
    (under : Act)
    (to : GroundTerm)
    : Prop
:= exists ρ,
    flattened_rewrites_in_valuation_under_to ρ r from under to
.

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



Section MinusL_sem.
    Context
        {Σ : StaticModel}
        (Act : Set)
    .

    Inductive MinusL_rewritesInVal
        (D : MinusL_LangDef Act)
        :
        (TermOver builtin_value) ->
        (TermOver builtin_value) ->
        (list Act)  ->
        Valuation ->
        (TermOver builtin_value) ->
        (TermOver builtin_value) ->
        Prop :=

    | mlr_rule : 
        forall
            (lc : TermOver BuiltinOrVar) (ld : TermOver BuiltinOrVar)
            (a : Act)
            (rc : TermOver Expression) (rd : TermOver Expression)
            (scs : list SideCondition),
            (mld_rewrite Act lc ld a rc rd scs) ∈ (mlld_decls Act D) ->
        forall (ctrl1 state1 ctrl2 state2 : TermOver builtin_value) ρ,
            satisfies ρ ctrl1 lc ->
            satisfies ρ state1 ld ->
            satisfies ρ ctrl2 rc ->
            satisfies ρ state2 rd ->
            satisfies ρ () scs ->
        MinusL_rewritesInVal D ctrl1 state1 [a] ρ ctrl2 state2
(*
    | mlr_trans :
        forall
            (ctrl1 state1 ctrl2 state2 ctrl3 state3 : TermOver builtin_value)
            (w1 w2 : list Act)
            (ρ : Valuation),
        MinusL_rewritesInVal D (ctrl1,state1) w1 ρ (ctrl2,state2) ->
        MinusL_rewritesInVal D (ctrl2,state2) w2 ρ (ctrl3,state3) ->
        MinusL_rewritesInVal D (ctrl1,state1) (w1 ++ w2) ρ (ctrl3,state3)
*)
    | mlr_context :
        forall
            (c : TermOver BuiltinOrVar)
            (h : variable)
            (scs : list SideCondition),
            (mld_context Act c h scs) ∈ (mlld_decls Act D) ->
        forall (ctrl1 state1 ctrl2 state2 r v : TermOver builtin_value)
            (w : list Act) (ρ : Valuation),
            satisfies ρ () scs ->
            satisfies ρ () (mlld_isValue Act D (ft_element (uglify' v))) ->
            satisfies ρ ctrl1 (TermOverBoV_subst c h (TermOverBuiltin_to_TermOverBoV r)) ->
            satisfies ρ ctrl2 (TermOverBoV_subst c h (TermOverBuiltin_to_TermOverBoV v)) ->
            MinusL_rewritesInVal D r state1 w ρ v state2 ->
            MinusL_rewritesInVal D ctrl1 state1 w ρ ctrl2 state2
    .

End MinusL_sem.

Inductive flattened_rewrites_to_over
    {Σ : StaticModel}
    {Act : Set}
    (Γ : RewritingTheory Act)
    :
    TermOver builtin_value ->
    list Act ->
    TermOver builtin_value ->
    Prop
:=
| frto_base: forall t,
        flattened_rewrites_to_over Γ t nil t
| frto_step: forall (t1 t2 t3 : TermOver builtin_value) w a r,
    r ∈ Γ ->
    flattened_rewrites_to r (uglify' t1) a (uglify' t2) ->
    flattened_rewrites_to_over Γ t2 w t3 ->
    flattened_rewrites_to_over Γ t1 (a::w) t3
.