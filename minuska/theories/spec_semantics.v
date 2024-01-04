From Minuska Require Import
    prelude
    spec_syntax
.

Definition Valuation {Σ : Signature}
        := gmap variable GroundTerm
    .

(*Transparent Valuation.*)

Fixpoint Expression_evaluate
    {Σ : Signature} (ρ : Valuation) (t : Expression) : option GroundTerm :=
match t with
| ft_element e => Some e
| ft_variable x => ρ !! x
| ft_unary f t =>
    e ← Expression_evaluate ρ t;
    Some (builtin_unary_function_interp f e)
| ft_binary f t1 t2 =>
    e1 ← Expression_evaluate ρ t1;
    e2 ← Expression_evaluate ρ t2;
    Some (builtin_binary_function_interp f e1 e2)
end.

Class Satisfies (A B : Type) := mkSatisfies {
    satisfies : A -> B -> Prop ;
}.

Arguments satisfies : simpl never.

Definition val_satisfies_ap
    {Σ : Signature} (ρ : Valuation) (ap : AtomicProposition)
    : Prop :=
match ap with
| apeq e1 e2 => 
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    v1 = v2 /\ is_Some v1
| ap1 p e =>
    let v := Expression_evaluate ρ e in
    match v with
    | Some vx => builtin_unary_predicate_interp p vx
    | None => False
    end
| ap2 p e1 e2 =>
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    match v1,v2 with
    | Some vx, Some vy => builtin_binary_predicate_interp p vx vy
    | _,_ => False
    end
end
.

#[export]
Instance Satisfies_val_ap
    {Σ : Signature} : Satisfies Valuation AtomicProposition
:= {|
    satisfies := val_satisfies_ap ;
|}.

Fixpoint val_satisfies_c
    {Σ : Signature} (ρ : Valuation) (c : Constraint)
    : Prop :=
match c with
| c_True => True
| c_atomic ap => satisfies ρ ap
| c_and c1 c2 => val_satisfies_c ρ c1 /\ val_satisfies_c ρ c2
| c_not c' => ~ val_satisfies_c ρ c'
end.

#[export]
Instance Satisfies_val_c
    {Σ : Signature} : Satisfies Valuation Constraint
:= {|
    satisfies := val_satisfies_c ;
|}.


Inductive aoxy_satisfies_aoxz
    {V X Y Z : Type}
    `{Satisfies (V*Y) Z}
    `{Satisfies (V*Y) (AppliedOperator' X Z)}
    `{Satisfies (V*(AppliedOperator' X Y)) Z }
    :
    (V*(AppliedOperator' X Y)) ->
    AppliedOperator' X Z ->
    Prop :=

| asa_x:
    forall ρ x,
        aoxy_satisfies_aoxz
            (ρ,(@ao_operator X Y x))
            (@ao_operator X Z x)

| asa_operand:
    forall ρ aoxy aoxz y z,
        aoxy_satisfies_aoxz (ρ,aoxy) aoxz ->
        satisfies (ρ,y) z ->
        aoxy_satisfies_aoxz
            (ρ,(ao_app_operand aoxy y))
            (ao_app_operand aoxz z)

| asa_operand_asa:
    forall ρ aoxy aoxz aoxy2 z,
        aoxy_satisfies_aoxz (ρ,aoxy) aoxz ->
        satisfies (ρ,aoxy2) z ->
        aoxy_satisfies_aoxz
        (* The right-side, the symbolic one, has more compact representation - so *)
            (ρ,(ao_app_ao aoxy aoxy2))
            (ao_app_operand aoxz z)

| asa_asa_operand:
    forall
        (ρ : V)
        (aoxy : AppliedOperator' X Y)
        (aoxz aoxz2 : AppliedOperator' X Z)
        (y : Y),
        aoxy_satisfies_aoxz (ρ,aoxy) aoxz ->
        @satisfies (V*Y) (AppliedOperator' X Z) _ (ρ, y) aoxz2 ->
        aoxy_satisfies_aoxz
            (ρ, ao_app_operand aoxy y)
            ((ao_app_ao aoxz aoxz2))

| asa_asa:
    forall ρ aoxy1 aoxy2 aoxz1 aoxz2,
        aoxy_satisfies_aoxz (ρ,aoxy1) aoxz1 ->
        aoxy_satisfies_aoxz (ρ,aoxy2) aoxz2 ->
        aoxy_satisfies_aoxz
            (ρ,(ao_app_ao aoxy1 aoxy2))
            (ao_app_ao aoxz1 aoxz2)
.


#[export]
Instance Satisfies_aoxy_aoxz
    {V X Y Z : Type}
    `{Satisfies (V*Y) Z}
    `{Satisfies (V*Y) (AppliedOperator' X Z)}
    `{Satisfies (V*(AppliedOperator' X Y)) Z }
    :
    Satisfies (V*(AppliedOperator' X Y)) (AppliedOperator' X Z)
:= {|
    satisfies := aoxy_satisfies_aoxz ;
|}.


Inductive aoxyo_satisfies_aoxzo
    (V X Y Z : Type)
    `{Satisfies (V*Y) Z}
    `{Satisfies (V*(AppliedOperator' X Y)) Z}
    `{Satisfies (V*(AppliedOperator' X Y)) (AppliedOperator' X Z)}
    : (V*(AppliedOperatorOr' X Y)) ->
      (AppliedOperatorOr' X Z) ->
      Prop
:=
| axysaxz_app:
    forall
        (ρ : V)
        (xy : AppliedOperator' X Y)
        (xz : AppliedOperator' X Z)
        (pf : satisfies (ρ,xy) xz),
        aoxyo_satisfies_aoxzo V X Y Z (ρ,(@aoo_app _ _  xy)) (aoo_app _ _ xz)

| axysaxz_operand:
    forall (ρ : V) (y : Y) (z : Z) (pf : satisfies (ρ,y) z),
        aoxyo_satisfies_aoxzo V X Y Z (ρ, @aoo_operand X Y y) (@aoo_operand X Z z)

| axysaxz_combined:
    forall (ρ : V) axy axz,
        satisfies (ρ,axy) axz ->
        aoxyo_satisfies_aoxzo V X Y Z (ρ, @aoo_app _ _  axy) (@aoo_operand X Z axz)
.

#[export]
Instance Satisfies_aoxyo_aoxzo
    {V X Y Z : Type}
    `{Satisfies (V*Y) Z}
    `{Satisfies (V*(AppliedOperator' X Y)) Z}
    `{Satisfies (V*(AppliedOperator' X Y)) (AppliedOperator' X Z)}
    :
    Satisfies (V*(AppliedOperatorOr' X Y)) (AppliedOperatorOr' X Z)
:= {|
    satisfies := aoxyo_satisfies_aoxzo V X Y Z;
|}.

Inductive builtin_satisfies_BuiltinOrVar
    {Σ : Signature}
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
    {Σ : Signature}
    (ρb : (Valuation * builtin_value))
    (bov : BuiltinOrVar)
    : Prop
:= builtin_satisfies_BuiltinOrVar ρb.1 ρb.2 bov.

#[export]
Instance Satisfies_builtin_BuiltinOrVar
    {Σ : Signature}
    :
    Satisfies (Valuation * builtin_value) BuiltinOrVar
:= {|
    satisfies := builtin_satisfies_BuiltinOrVar' ;
|}.

Definition AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar
    {Σ : Signature}
    (ρ : Valuation)
    (aop : AppliedOperator' symbol builtin_value)
    (bov : BuiltinOrVar)
    : Prop :=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app symbol builtin_value aop)
end.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin__BuiltinOrVar
    {Σ : Signature}
    : Satisfies (Valuation*(AppliedOperator' symbol builtin_value)) BuiltinOrVar
:= {| 
    satisfies := fun ρx y => AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρx.1 ρx.2 y
|}.

Definition AppliedOperator'_symbol_builtin_satisfies'_BuiltinOrVar
    {Σ : Signature}
    (ρaop : (Valuation * (AppliedOperator' symbol builtin_value)))
    (bov : BuiltinOrVar)
    : Prop
:= AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρaop.1 ρaop.2 bov.

#[export]
Instance Satisfies_AppliedOperator'_symbol_builtin_BuiltinOrVar
    {Σ : Signature}
    :
    Satisfies (Valuation * (AppliedOperator' symbol builtin_value)) BuiltinOrVar
:= {|
    satisfies := AppliedOperator'_symbol_builtin_satisfies'_BuiltinOrVar ;
|}.

Definition aosb_satisfies_aosbf
    {Σ : Signature}
    {A B : Type}
    {SatAB : Satisfies (Valuation*A) B}
    `{Satisfies (Valuation*A) (AppliedOperator' symbol B)}
    {SatA'B : Satisfies (Valuation*(AppliedOperator' symbol A)) B}
    :
    (Valuation * (AppliedOperator' symbol A)) ->
    AppliedOperator' symbol B ->
    Prop :=
    @aoxy_satisfies_aoxz
        Valuation
        symbol
        A
        B
        _
        _
        _
.

#[export]
Instance Satisfies__builtin__ao'B
    {Σ : Signature}
    {B : Type}
    :
    Satisfies
        (Valuation * builtin_value)
        (AppliedOperator' symbol B)
:= {| 
    satisfies := fun _ _ => false ;
|}.

#[export]
Instance Satisfies_aos__builtin_BuiltinOrVar
    {Σ : Signature}
    :
    Satisfies (Valuation * (AppliedOperator' symbol builtin_value)) (AppliedOperator' symbol BuiltinOrVar)
.
Proof.
    apply _.
Defined.


#[export]
Instance Satisfies_aosb_aosbf
    {Σ : Signature}
    {A B : Type}
    {SatAB : Satisfies (Valuation*A) B}
    `{Satisfies (Valuation*A) (AppliedOperator' symbol B)}
    {SatA'B : Satisfies (Valuation*(AppliedOperator' symbol A)) B}
    :
    Satisfies (Valuation * (AppliedOperator' symbol A)) (AppliedOperator' symbol B)
:= {|
    satisfies := aosb_satisfies_aosbf;
|}.


Definition aoosb_satisfies_aoosbf
    {Σ : Signature}
    :
    (Valuation*(AppliedOperatorOr' symbol builtin_value)) ->
    AppliedOperatorOr' symbol BuiltinOrVar ->
    Prop :=
    aoxyo_satisfies_aoxzo
        Valuation
        symbol
        builtin_value
        BuiltinOrVar
.

#[export]
Instance
Satisfies_aoosb_aoosbf
    {Σ : Signature}
    :
    Satisfies (Valuation * (AppliedOperatorOr' symbol builtin_value)) (AppliedOperatorOr' symbol BuiltinOrVar)
:= {|
    satisfies := aoosb_satisfies_aoosbf ;
|}.

Definition in_val_GroundTerm_satisfies_OpenTerm
    {Σ : Signature}
    (ρg : Valuation*GroundTerm)
    (φ : OpenTerm)
    : Prop := aoosb_satisfies_aoosbf ρg φ
.

#[export]
Instance Satisfies_valGroundTerm_OpenTerm
    {Σ : Signature}
    :
    Satisfies (Valuation * GroundTerm) OpenTerm
:= {|
    satisfies := in_val_GroundTerm_satisfies_OpenTerm ;
|}.

Definition valuation_satisfies_match
    {Σ : Signature}
    (ρ : Valuation)
    (m : Match) : Prop :=
match m with
| mkMatch _ x φ =>
    match ρ !! x with
    | Some g
        => satisfies (ρ, g) φ
    | _ => False
    end
end.

#[export]
Instance Satisfies_val_match
    {Σ : Signature}
    :
    Satisfies Valuation Match
:= {|
    satisfies := valuation_satisfies_match ;
|}.

Definition valuation_satisfies_sc
    {Σ : Signature}
    (ρ : Valuation)
    (sc : SideCondition) : Prop :=
match sc with
| sc_constraint c => satisfies ρ c
| sc_match m => satisfies ρ m
end.

#[export]
Instance Satisfies_val_sc
    {Σ : Signature}
    :
    Satisfies Valuation SideCondition
:= {|
    satisfies := valuation_satisfies_sc ;
|}.


Inductive A_satisfies_B_WithASideCondition
    {Σ : Signature}
    (V A B : Type)
    `{Satisfies V SideCondition}
    `{Satisfies (V*A) B}
    : (V*A) -> WithASideCondition B -> Prop :=

| asbwsc_base:
    forall (ρa : V*A) (b : B),
        satisfies (ρa) b ->
        A_satisfies_B_WithASideCondition V A B ρa (wsc_base b)

| asbwsc_sc :
    forall (ρa : V*A) (bsc : WithASideCondition B) sc,
        A_satisfies_B_WithASideCondition V A B ρa bsc ->
        satisfies ρa.1 sc ->
        A_satisfies_B_WithASideCondition V A B ρa (wsc_sc bsc sc)
.

#[export]
Instance Satisfies_A_Bsc
    {Σ : Signature}
    {V A B : Type}
    `{Satisfies V SideCondition}
    `{Satisfies (V*A) B}
    :
    Satisfies (V*A) (WithASideCondition B)
:= {|
    satisfies :=
        A_satisfies_B_WithASideCondition
        V A B;
|}.

Definition GroundTerm_satisfies_BuiltinOrVar
    {Σ : Signature}
    (ρg : Valuation*GroundTerm)
    (bov : BuiltinOrVar)
    : Prop :=
let ρ := ρg.1 in
let g := ρg.2 in
match bov with
| bov_builtin b =>
    match g with
    | aoo_app _ _ _ => False
    | aoo_operand _ _ b' => b = b'
    end
| bov_variable x => ρ !! x = Some g
end.

#[export]
Instance Satisfies_GroundTerm_BuiltinOrVar
    {Σ : Signature}
    :
    Satisfies (Valuation*GroundTerm) BuiltinOrVar
:= {|
    satisfies := GroundTerm_satisfies_BuiltinOrVar ;
|}.

Definition in_val_GroundTerm_satisfies_OpenTermWSC
    {Σ : Signature}
    : (Valuation*GroundTerm) ->
    OpenTermWSC ->
    Prop :=
    A_satisfies_B_WithASideCondition
        Valuation
        GroundTerm
        OpenTerm
.

#[export]
Instance Satisfies_GroundTerm_OpenTermWSC
    {Σ : Signature}
    :
    Satisfies (Valuation*GroundTerm) OpenTermWSC
:= {|
    satisfies := in_val_GroundTerm_satisfies_OpenTermWSC ;
|}.

Definition builtin_value_satisfies_OpenTerm
    {Σ : Signature}
    :
    (Valuation*builtin_value) ->
    OpenTerm ->
    Prop := fun ρb t =>
match t with
| aoo_app _ _ _ => False
| aoo_operand _ _ bov =>
    satisfies ρb bov
end.

#[export]
Instance Satisfies_builtin_value_OpenTerm
    {Σ : Signature}
    :
    Satisfies (Valuation*builtin_value) OpenTerm
:= {|
    satisfies :=  builtin_value_satisfies_OpenTerm ;
|}.

Definition builtin_value_satisfies_OpenTermWSC
    {Σ : Signature}
    :
    (Valuation*builtin_value) ->
    OpenTermWSC ->
    Prop :=
    A_satisfies_B_WithASideCondition
        Valuation
        builtin_value
        OpenTerm
.

#[export]
Instance Satisfies_builtin_value_OpenTermWSC
    {Σ : Signature}
    :
    Satisfies (Valuation*builtin_value) OpenTermWSC
:= {|
    satisfies := builtin_value_satisfies_OpenTermWSC ;
|}.

Definition AppliedOperator'_symbol_builtin_value_satisfies_BOV
    {Σ : Signature}
    (ρao : Valuation * (AppliedOperator' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Prop
:=
let ρ := ρao.1 in
let ao := ρao.2 in
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app _ _ ao) 
end
.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin_value__BOV
    {Σ : Signature}
    {V : Type}
    :
    Satisfies (Valuation*(AppliedOperator' symbol builtin_value)) BuiltinOrVar
:= {|
    satisfies := AppliedOperator'_symbol_builtin_value_satisfies_BOV;
|}.

Definition AppliedOperator'_symbol_A_satisfies_OpenTermB'
    {Σ : Signature}
    (V A B : Type)
    `{Satisfies (V*A) B}
    `{Satisfies (V*(AppliedOperator' symbol A)) B}
    `{Satisfies (V * AppliedOperator' symbol A) (AppliedOperator' symbol B)}
    :
    (V*(AppliedOperator' symbol A)) ->
    AppliedOperatorOr' symbol B ->
    Prop
:=  fun ρa =>
    let ρ := ρa.1 in
    let a := ρa.2 in
    aoxyo_satisfies_aoxzo V symbol A B
    (ρ,(aoo_app _ _ a))
.

#[export]
Instance Satisfies__lift_builtin_to_aosb
    {Σ : Signature}
    {V A B : Type}
    {AsB : Satisfies (V*A) B}
    {sat2 : Satisfies (V*(AppliedOperator' symbol A)) B}
    `{Satisfies (V * AppliedOperator' symbol A) (AppliedOperator' symbol B)}
    :
    Satisfies
        (V*(AppliedOperator' symbol A))
        (AppliedOperatorOr' symbol B)
:= {|
    satisfies :=
        AppliedOperator'_symbol_A_satisfies_OpenTermB' V A B ;
|}.

Definition AppliedOperator'_symbol_A_satisfies_OpenTermB
    {Σ : Signature}
    (V A B : Type)
    `{Satisfies (V*A) B}
    `{Satisfies (V*(AppliedOperator' symbol A)) B}
    `{Satisfies (V * AppliedOperator' symbol A) (AppliedOperator' symbol B)}
    :
    (V*(AppliedOperatorOr' symbol A)) ->
    AppliedOperatorOr' symbol B ->
    Prop
:=  
    aoxyo_satisfies_aoxzo V symbol A B
.

#[export]
Instance Satisfies__lift_builtin_to_aosbo
    {Σ : Signature}
    {V A B : Type}
    {bsB : Satisfies (V*A) B}
    {sat2 : Satisfies (V*(AppliedOperator' symbol A)) B}
    {sat2 : Satisfies (V*(AppliedOperator' symbol A)) (AppliedOperator' symbol B)}
    :
    Satisfies
        (V*(AppliedOperatorOr' symbol A))
        (AppliedOperatorOr' symbol B)
:= {|
    satisfies :=
        AppliedOperator'_symbol_A_satisfies_OpenTermB V A B
        ;
|}.

Definition AppliedOperator'_symbol_builtin_satisfies_OpenTerm
    {Σ : Signature}
    {V : Type}
    `{Satisfies (V * builtin_value) BuiltinOrVar}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) BuiltinOrVar}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) (AppliedOperator' symbol BuiltinOrVar)}
    :
    (V*(AppliedOperator' symbol builtin_value)) ->
    OpenTerm ->
    Prop
:=  fun ρa =>
    let ρ := ρa.1 in
    let a := ρa.2 in
    AppliedOperator'_symbol_A_satisfies_OpenTermB
        V
        builtin_value
        BuiltinOrVar
        (ρ,(aoo_app _ _ a))
.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin__OpenTerm
    {Σ : Signature}
    {V : Type}
    `{Satisfies (V * builtin_value) BuiltinOrVar}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) BuiltinOrVar}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) (AppliedOperator' symbol BuiltinOrVar)}
    :
    Satisfies
        (V*(AppliedOperator' symbol builtin_value))
        OpenTerm
:= {|
    satisfies :=
        AppliedOperator'_symbol_builtin_satisfies_OpenTerm ;
|}.

Definition AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC
    {Σ : Signature}
    :
    (Valuation*(AppliedOperator' symbol builtin_value)) ->
    OpenTermWSC ->
    Prop :=
    A_satisfies_B_WithASideCondition
        Valuation
        (AppliedOperator' symbol builtin_value)
        OpenTerm
.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin__OpenTermWSC
    {Σ : Signature}
    :
    Satisfies
        (Valuation*(AppliedOperator' symbol builtin_value))
        OpenTermWSC
:= {|
    satisfies := 
        AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC ;
|}.


Definition GroundTerm_satisfies_LhsPattern
    {Σ : Signature}
    {V : Type}
    `{Satisfies (V * builtin_value) OpenTermWSC}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) OpenTermWSC}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) (AppliedOperator' symbol OpenTermWSC)}
    :
    (V*GroundTerm) -> LhsPattern -> Prop
:= aoxyo_satisfies_aoxzo
    V
    symbol
    builtin_value
    OpenTermWSC
.

#[export]
Instance Satisfies__GroundTerm__LhsPattern
    {Σ : Signature}
    {V : Type}
    `{Satisfies (V * builtin_value) OpenTermWSC}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) OpenTermWSC}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) (AppliedOperator' symbol OpenTermWSC)}
    :
    Satisfies
        (V*GroundTerm)
        LhsPattern
:= {|
    satisfies := 
        GroundTerm_satisfies_LhsPattern
        ;
|}.


#[export]
Instance Satisfies_builtin_expr
    {Σ : Signature}:
    Satisfies (Valuation * builtin_value) Expression
:= {|
    satisfies := (fun ρb e =>
        let ρ := ρb.1 in
        let b := ρb.2 in
        Expression_evaluate ρ e = Some (aoo_operand _ _ b)
    ) ;
|}.

#[export]
Instance Satisfies_asb_expr
    {Σ : Signature}:
    Satisfies
        (Valuation * (AppliedOperator' symbol builtin_value))
        Expression
:= {|
    satisfies := (fun ρx e =>
        let ρ := ρx.1 in
        let x := ρx.2 in
        Expression_evaluate ρ e = Some (aoo_app _ _ x)
    ) ;
|}.


Definition GroundTerm_satisfies_RhsPattern
    {Σ : Signature}
    {V : Type}
    `{Satisfies (V * builtin_value) Expression}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) Expression}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) (AppliedOperator' symbol Expression)}
    :
    (V*GroundTerm) -> RhsPattern -> Prop
:= aoxyo_satisfies_aoxzo
    V
    symbol
    builtin_value
    Expression
.

#[export]
Instance Satisfies__GroundTerm__RhsPattern
    {Σ : Signature}
    {V : Type}
    `{Satisfies (V * builtin_value) Expression}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) Expression}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) (AppliedOperator' symbol Expression)}

    :
    Satisfies
        (V*GroundTerm)
        RhsPattern
:= {|
    satisfies := 
        GroundTerm_satisfies_RhsPattern
        ;
|}.


#[export]
Instance Satisfies_gt_var
    {Σ : Signature}:
    Satisfies (Valuation * GroundTerm) variable
:= {|
    satisfies := (fun ρg x => ρg.1 !! x = Some ρg.2)
|}.

Definition GroundTerm_satisfies_VarWithSc
    {Σ : Signature}:
    (Valuation*GroundTerm) ->
    WithASideCondition variable
    -> Prop :=
    A_satisfies_B_WithASideCondition
        Valuation
        GroundTerm
        variable
.

#[export]
Instance Satisfies__GroundTerm__VarWithSc
    {Σ : Signature}
    :
    Satisfies
        (Valuation*GroundTerm)
        (WithASideCondition variable)
:= {|
    satisfies :=
        GroundTerm_satisfies_VarWithSc
        ;
|}.


Definition GroundTerm_satisfies_LocalRewrite
    {Σ : Signature}
    (ρdg : (Valuation*LeftRight)*GroundTerm) (r : LocalRewrite)
    : Prop :=
let ρ := ρdg.1.1 in
let d := ρdg.1.2 in
let g := ρdg.2 in
match d with
| LR_Left => satisfies (ρ,g) (lr_from r)
| LR_Right => satisfies (ρ,g) (lr_to r)
end.

#[export]
Instance Satisfies__GroundTerm__LocalRewrite
    {Σ : Signature}
    :
    Satisfies
        ((Valuation*LeftRight)*GroundTerm)
        (LocalRewrite)
:= {|
    satisfies := 
        GroundTerm_satisfies_LocalRewrite
        ;
|}.

Definition GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    (ρdg : (Valuation*LeftRight)*GroundTerm)
    (rb : LocalRewriteOrOpenTermOrBOV)
    : Prop :=
let ρ := ρdg.1.1 in
let g := ρdg.2 in
match rb with
| lp_rewrite r
    => satisfies ρdg r
| lp_basicpat φ
    => satisfies (ρ,g) φ
| lp_bov bx
    => satisfies (ρ,g) bx
end.

#[export]
Instance Satisfies__GroundTerm__LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    :
    Satisfies
        ((Valuation*LeftRight)*GroundTerm)
        (LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies :=
        GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
        ;
|}.

Definition builtin_satisfies_LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    (ρdb : (Valuation*LeftRight)*builtin_value)
    (r : LocalRewriteOrOpenTermOrBOV)
    : Prop :=
let ρ := ρdb.1.1 in
let d := ρdb.1.2 in
let b := ρdb.2 in
match r with
| lp_rewrite r'
    => satisfies ((ρ,d),(aoo_operand _ _ b)) r'

| lp_basicpat (aoo_app _ _ _)
    => False

| lp_basicpat (aoo_operand _ _ bov)
    => satisfies (ρ,b) bov

| lp_bov bx
    => satisfies (ρ,b) bx
end.

#[export]
Instance Satisfies__builtin_value__LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    :
    Satisfies
        ((Valuation*LeftRight)*builtin_value)
        (LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies :=
        builtin_satisfies_LocalRewriteOrOpenTermOrBOV
        ;
|}.

(*
#[export]
Instance satLift1
    {Σ : Signature}
    {L R : Type}
    `{Satisfies (Valuation * L) R}
    :
    Satisfies
        ((Valuation * LeftRight) * L) R
:= {|
    satisfies := fun ρdg r => satisfies (ρdg.1.1,ρdg.2) r
|}.*)
(*
#[export] Instance _tmp
    {Σ : Signature}
    :
    Satisfies
        (Valuation * LeftRight * AppliedOperator' symbol builtin_value)
        LocalRewriteOrOpenTermOrBOV
:= {|
    satisfies := fun ρdg => satisfies (ρdg.1.1,ρdg.1.2, aoo_app _ _ ρdg.2)
|}.
*)

#[export]
Instance Satisfies_vlrglrootob
    {Σ : Signature}:
    Satisfies
        ((Valuation * LeftRight) * AppliedOperator' symbol builtin_value)
        LocalRewriteOrOpenTermOrBOV
:= {|
    satisfies := fun ρdg =>
        let ρ := ρdg.1.1 in
        let d := ρdg.1.2 in
        let g := ρdg.2 in
        satisfies ((ρ,d), aoo_app _ _ g)
        
     ;
|}.


#[export]
Instance Satisfies_vlrblrootob
    {Σ : Signature}:
    Satisfies
        ((Valuation * LeftRight) * builtin_value)
        (AppliedOperator' symbol LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies := fun _ _ => False ;
|}.


#[export]
Instance Satisfies_sym_bov
    {Σ : Signature}
    :
    Satisfies (Valuation * symbol) BuiltinOrVar
:= {|
    satisfies := fun _ _ => False ;
|}.

#[export]
Instance Satisfies_aop_lrw {Σ : Signature}:
    Satisfies
        (Valuation * LeftRight * AppliedOperator' symbol builtin_value)
        (AppliedOperator' symbol LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies := @aoxy_satisfies_aoxz
        (Valuation*LeftRight)
        symbol
        builtin_value
        LocalRewriteOrOpenTermOrBOV
        _ _ _
        ;
|}.

Definition GroundTerm_satisfies_UncondRewritingRule
    {Σ : Signature}
    : ((Valuation*LeftRight)*GroundTerm) -> UncondRewritingRule -> Prop
:=
    aoxyo_satisfies_aoxzo
        (Valuation*LeftRight)
        symbol
        builtin_value
        LocalRewriteOrOpenTermOrBOV
.

#[export]
Instance Satisfies__GroundTerm__UncondRewritingRule
    {Σ : Signature}
    :
    Satisfies
        ((Valuation*LeftRight)*GroundTerm)
        (UncondRewritingRule)
:= {|
    satisfies := 
        GroundTerm_satisfies_UncondRewritingRule
        ;
|}.

Instance Satisfies_Valuation_LR_SideCondition
    {Σ : Signature}
    :
    Satisfies (Valuation * LeftRight) SideCondition
:= {|
    satisfies := fun ρd => let ρ := ρd.1 in
        satisfies ρ
        ;
|}.

Definition GroundTerm_satisfies_RewritingRule
    {Σ : Signature}
    : ((Valuation*LeftRight)*GroundTerm) -> RewritingRule -> Prop :=
    A_satisfies_B_WithASideCondition
        (Valuation*LeftRight)
        GroundTerm
        UncondRewritingRule
.

#[export]
Instance Satisfies__GroundTerm__RewritingRule
    {Σ : Signature}
    :
    Satisfies
        ((Valuation*LeftRight)*GroundTerm)
        (RewritingRule)
:= {|
    satisfies := 
        GroundTerm_satisfies_RewritingRule
        ;
|}.

Definition GroundTerm_satisfies_OpenTerm
    {Σ : Signature}
    : GroundTerm -> OpenTerm -> Prop :=
    fun g φ => ∃ ρ, satisfies (ρ, g) φ
.

#[export]
Instance Satisfies__GroundTerm__OpenTerm_inall
    {Σ : Signature}
    :
    Satisfies
        GroundTerm
        OpenTerm
:= {|
    satisfies := GroundTerm_satisfies_OpenTerm ;
|}.

(*
#[export]
Instance Satisfies_bv_ao'
    {Σ : Signature}
    :
    Satisfies (Valuation * builtin_value) (AppliedOperator' symbol BuiltinOrVar)
:= {|
    satisfies := fun _ _ => False ;
|}.
*)

Definition rewrites_in_valuation_to
    {Σ : Signature}
    (ρ : Valuation)
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= satisfies ((ρ,LR_Left),from) r
/\ satisfies ((ρ,LR_Right),to) r
.

Definition rewrites_to
    {Σ : Signature}
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= exists ρ, rewrites_in_valuation_to ρ r from to
.

Definition RewritingTheory {Σ : Signature}
    := list RewritingRule
.

Definition rewriting_relation
    {Σ : Signature}
    (Γ : RewritingTheory)
    : relation GroundTerm
    := fun from to =>
        exists r, r ∈ Γ /\ rewrites_to r from to
.

Definition not_stuck
    {Σ : Signature}
    (Γ : RewritingTheory)
    (e : GroundTerm) : Prop
:= exists e', rewriting_relation Γ e e'.

Definition stuck
    {Σ : Signature}
    (Γ : RewritingTheory)
    (e : GroundTerm) : Prop
:= not (not_stuck Γ e).

Definition rule_weakly_well_defined
    {Σ : Signature}
    (r : RewritingRule)
    : Prop
    := ∀ ρ from,
        satisfies ((ρ,LR_Left),from) r ->
        ∃ to, satisfies ((ρ,LR_Right), to) r
.

Definition thy_weakly_well_defined
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Prop
    := ∀ r, r ∈ Γ -> rule_weakly_well_defined r
.


Definition valuation_satisfies_scs
    {Σ : Signature}
    (ρ : Valuation)
    (scs : list SideCondition)
    : Prop
:= Forall (satisfies ρ) scs
.

#[export]
Instance Satisfies_valuation_scs
    {Σ : Signature}
    : Satisfies Valuation (list SideCondition)
:= {|
    satisfies := valuation_satisfies_scs ;
|}.

(*
#[export]
Instance Satisfies_bv_pureterm
    {Σ : Signature}:
    Satisfies (Valuation * builtin_value)
    (AppliedOperator' symbol Expression)
:= {|
    satisfies := fun _ _ => False;
|}.
*)
#[export]
Program Instance
    Satisfies_symbol_Expression
    {Σ : Signature}
    :
    Satisfies (Valuation * symbol) Expression
:= {|
    satisfies := fun _ _ => False ;
|}.