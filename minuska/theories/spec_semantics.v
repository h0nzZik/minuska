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

Class Satisfies (A B : Type) := {
    satisfies : A -> B -> Prop ;
}.

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
    {X Y Z : Type}
    {Y_sat_Z : Y -> Z -> Prop}
    {AOXY_sat_Z : AppliedOperator' X Y -> Z -> Prop}:
    AppliedOperator' X Y ->
    AppliedOperator' X Z ->
    Prop :=

| asa_x:
    forall x,
        aoxy_satisfies_aoxz
            (@ao_operator X Y x)
            (@ao_operator X Z x)

| asa_operand:
    forall aoxy aoxz y z,
        aoxy_satisfies_aoxz aoxy aoxz ->
        Y_sat_Z y z ->
        aoxy_satisfies_aoxz
            (ao_app_operand aoxy y)
            (ao_app_operand aoxz z)

| asa_operand_asa:
    forall aoxy aoxz aoxy2 z,
        aoxy_satisfies_aoxz aoxy aoxz ->
        AOXY_sat_Z aoxy2 z ->
        aoxy_satisfies_aoxz
            (ao_app_ao aoxy aoxy2)
            (ao_app_operand aoxz z)

| asa_asa:
    forall aoxy1 aoxy2 aoxz1 aoxz2,
        aoxy_satisfies_aoxz aoxy1 aoxz1 ->
        aoxy_satisfies_aoxz aoxy2 aoxz2 ->
        aoxy_satisfies_aoxz
            (ao_app_ao aoxy1 aoxy2)
            (ao_app_ao aoxz1 aoxz2)
.


#[export]
Instance Satisfies_aoxy_aoxz
    {X Y Z : Type}
    {Y_sat_Z : Y -> Z -> Prop}
    {AOXY_sat_Z : AppliedOperator' X Y -> Z -> Prop}:
    Satisfies (AppliedOperator' X Y) (AppliedOperator' X Z)
:= {|
    satisfies := @aoxy_satisfies_aoxz X Y Z Y_sat_Z AOXY_sat_Z ;
|}.


Inductive aoxyo_satisfies_aoxzo
    {X Y Z : Type}
    {Y_sat_Z : Y -> Z -> Prop}
    {AOXY_sat_Z : AppliedOperator' X Y -> Z -> Prop}:
    AppliedOperatorOr' X Y ->
    AppliedOperatorOr' X Z ->
    Prop :=
| axysaxz_app:
    forall
        (xy : AppliedOperator' X Y)
        (xz : AppliedOperator' X Z)
        (pf : @aoxy_satisfies_aoxz X Y Z Y_sat_Z AOXY_sat_Z xy xz),
        aoxyo_satisfies_aoxzo (@aoo_app _ _  xy) (aoo_app _ _ xz)
| axysaxz_operand:
    forall (y : Y) (z : Z) (pf : Y_sat_Z y z),
        aoxyo_satisfies_aoxzo (@aoo_operand X Y y) (@aoo_operand X Z z)

| axysaxz_combined:
    forall axy axz,
        AOXY_sat_Z axy axz ->
        aoxyo_satisfies_aoxzo (@aoo_app _ _  axy) (@aoo_operand X Z axz)
.

#[export]
Instance Satisfies_aoxyo_aoxzo
    {X Y Z : Type}
    {Y_sat_Z : Y -> Z -> Prop}
    {AOXY_sat_Z : AppliedOperator' X Y -> Z -> Prop}:
    Satisfies (AppliedOperatorOr' X Y) (AppliedOperatorOr' X Z)
:= {|
    satisfies := @aoxyo_satisfies_aoxzo X Y Z Y_sat_Z AOXY_sat_Z ;
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
    {SatA'B : Satisfies (Valuation*(AppliedOperator' symbol A)) B}
    (ρ : Valuation)
    :
    AppliedOperator' symbol A ->
    AppliedOperator' symbol B ->
    Prop :=
    @aoxy_satisfies_aoxz
        symbol
        A
        B
        (fun x y => @satisfies _ _ SatAB (ρ,x) y)
        (fun x y => @satisfies _ _ SatA'B (ρ,x) y)
.

#[export]
Instance Satisfies_aosb_aosbf
    {Σ : Signature}
    {A B : Type}
    {SatAB : Satisfies (Valuation*A) B}
    {SatA'B : Satisfies (Valuation*(AppliedOperator' symbol A)) B}
    :
    Satisfies (Valuation * (AppliedOperator' symbol A)) (AppliedOperator' symbol B)
:= {|
    satisfies := fun ρb bov => aosb_satisfies_aosbf ρb.1 ρb.2 bov;
|}.


Definition aoosb_satisfies_aoosbf
    {Σ : Signature}
    (ρ : Valuation)
    :
    AppliedOperatorOr' symbol builtin_value ->
    AppliedOperatorOr' symbol BuiltinOrVar ->
    Prop :=
    @aoxyo_satisfies_aoxzo
        symbol
        builtin_value
        BuiltinOrVar
        (builtin_satisfies_BuiltinOrVar ρ)
        (AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ)
.

(* I do not want to make this an Instance because it would overlap with Satisfies_valGroundTerm_OpenTerm defined later in this file. *)
(*
#[export]
Instance
*)
Definition Satisfies_aoosb_aoosbf
    {Σ : Signature}
    :
    Satisfies (Valuation * (AppliedOperatorOr' symbol builtin_value)) (AppliedOperatorOr' symbol BuiltinOrVar)
:= {|
    satisfies := fun ρx y => aoosb_satisfies_aoosbf ρx.1 ρx.2 y ;
|}.

Definition in_val_GroundTerm_satisfies_OpenTerm
    {Σ : Signature}
    (ρ : Valuation)
    (g : GroundTerm)
    (φ : OpenTerm)
    : Prop := aoosb_satisfies_aoosbf ρ g φ
.

#[export]
Instance Satisfies_valGroundTerm_OpenTerm
    {Σ : Signature}
    :
    Satisfies (Valuation * GroundTerm) OpenTerm
:= {|
    satisfies := fun ρx y => in_val_GroundTerm_satisfies_OpenTerm ρx.1 ρx.2 y ;
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
| sc_constraint c => val_satisfies_c ρ c
| sc_match m => valuation_satisfies_match ρ m
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
    (A B : Type)
    (A_sat_B : A -> B -> Prop)
    (ρ : Valuation)
    : A -> WithASideCondition B -> Prop :=

| asbwsc_base:
    forall (a : A) (b : B),
        A_sat_B a b ->
        A_satisfies_B_WithASideCondition A B A_sat_B ρ a (wsc_base b)

| asbwsc_sc :
    forall (a : A) (bsc : WithASideCondition B) sc,
        A_satisfies_B_WithASideCondition A B A_sat_B ρ a bsc ->
        valuation_satisfies_sc ρ sc ->
        A_satisfies_B_WithASideCondition A B A_sat_B ρ a (wsc_sc bsc sc)
.

#[export]
Instance Satisfies_A_Bsc
    {Σ : Signature}
    {A B : Type}
    {A_sat_B : Satisfies (Valuation*A) B}
    :
    Satisfies (Valuation*A) (WithASideCondition B)
:= {|
    satisfies := fun ρx y =>
        A_satisfies_B_WithASideCondition
        A B
        (fun a b => @satisfies (Valuation*A) B A_sat_B (ρx.1,a) b)
        ρx.1 ρx.2 y ;
|}.

Definition GroundTerm_satisfies_BuiltinOrVar
    {Σ : Signature}
    (ρ : Valuation)
    (g : GroundTerm)
    (bov : BuiltinOrVar)
    : Prop :=
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
    satisfies := fun ρx y => GroundTerm_satisfies_BuiltinOrVar ρx.1 ρx.2 y ;
|}.

Definition in_val_GroundTerm_satisfies_OpenTermWSC
    {Σ : Signature}
    (ρ : Valuation):
    GroundTerm ->
    OpenTermWSC ->
    Prop :=
    A_satisfies_B_WithASideCondition
        GroundTerm
        OpenTerm
        (in_val_GroundTerm_satisfies_OpenTerm ρ)
        ρ
.

#[export]
Instance Satisfies_GroundTerm_OpenTermWSC
    {Σ : Signature}
    :
    Satisfies (Valuation*GroundTerm) OpenTermWSC
:= {|
    satisfies := fun ρx y => in_val_GroundTerm_satisfies_OpenTermWSC ρx.1 ρx.2 y ;
|}.

Definition builtin_value_satisfies_OpenTerm
    {Σ : Signature}
    (ρ : Valuation)
    :
    builtin_value ->
    OpenTerm ->
    Prop := fun b t =>
match t with
| aoo_app _ _ _ => False
| aoo_operand _ _ bov =>
    satisfies (ρ, b) bov
end.

#[export]
Instance Satisfies_builtin_value_OpenTerm
    {Σ : Signature}
    :
    Satisfies (Valuation*builtin_value) OpenTerm
:= {|
    satisfies := fun ρx y => builtin_value_satisfies_OpenTerm ρx.1 ρx.2 y ;
|}.

Definition builtin_value_satisfies_OpenTermWSC
    {Σ : Signature}
    (ρ : Valuation):
    builtin_value ->
    OpenTermWSC ->
    Prop :=
    A_satisfies_B_WithASideCondition
        builtin_value
        OpenTerm
        (builtin_value_satisfies_OpenTerm ρ)
        ρ
.

#[export]
Instance Satisfies_builtin_value_OpenTermWSC
    {Σ : Signature}
    :
    Satisfies (Valuation*builtin_value) OpenTermWSC
:= {|
    satisfies := fun ρx y => builtin_value_satisfies_OpenTermWSC ρx.1 ρx.2 y ;
|}.

Definition AppliedOperator'_symbol_builtin_value_satisfies_BOV
    {Σ : Signature}
    (ρ : Valuation)
    (ao : AppliedOperator' symbol builtin_value)
    (bov : BuiltinOrVar)
    : Prop
:=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app _ _ ao) 
end
.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin_value__BOV
    {Σ : Signature}
    :
    Satisfies (Valuation*(AppliedOperator' symbol builtin_value)) BuiltinOrVar
:= {|
    satisfies := fun ρx y => AppliedOperator'_symbol_builtin_value_satisfies_BOV ρx.1 ρx.2 y ;
|}.

Definition AppliedOperator'_symbol_A_satisfies_OpenTermB'
    {Σ : Signature}
    (A B : Type)
    (builtin_satisfies_B : A -> B -> Prop)
    AppliedOperator'_symbol_A_satisfies_B
    :
    AppliedOperator' symbol A ->
    AppliedOperatorOr' symbol B ->
    Prop
:=  fun a b => @aoxyo_satisfies_aoxzo symbol A B
    builtin_satisfies_B
    AppliedOperator'_symbol_A_satisfies_B
    (aoo_app _ _ a) b
.

#[export]
Instance Satisfies__lift_builtin_to_aosb
    {Σ : Signature}
    {A B : Type}
    {AsB : Satisfies (Valuation*A) B}
    {sat2 : Satisfies (Valuation*(AppliedOperator' symbol A)) B}
    :
    Satisfies
        (Valuation*(AppliedOperator' symbol A))
        (AppliedOperatorOr' symbol B)
:= {|
    satisfies := fun ρx y =>
        AppliedOperator'_symbol_A_satisfies_OpenTermB' A B
            (fun a b => @satisfies _ _ AsB (ρx.1,a) b)
            (fun a b => @satisfies _ _ sat2 (ρx.1,a) b)
            ρx.2
            y
        ;
|}.

Definition AppliedOperator'_symbol_builtin_satisfies_OpenTermB
    {Σ : Signature}
    (B : Type)
    (builtin_satisfies_B : builtin_value -> B -> Prop)
    AppliedOperator'_symbol_builtin_value_satisfies_B
    :
    
    AppliedOperatorOr' symbol builtin_value ->
    AppliedOperatorOr' symbol B ->
    Prop
:=  
    @aoxyo_satisfies_aoxzo symbol builtin_value B
    builtin_satisfies_B
    AppliedOperator'_symbol_builtin_value_satisfies_B
.

#[export]
Instance Satisfies__lift_builtin_to_aosbo
    {Σ : Signature}
    {B : Type}
    {bsB : Satisfies (Valuation*builtin_value) B}
    {sat2 : Satisfies (Valuation*(AppliedOperator' symbol builtin_value)) B}
    :
    Satisfies
        (Valuation*(AppliedOperatorOr' symbol builtin_value))
        (AppliedOperatorOr' symbol B)
:= {|
    satisfies := fun ρx y =>
        AppliedOperator'_symbol_builtin_satisfies_OpenTermB B
            (fun a b => @satisfies _ _ bsB (ρx.1,a) b)
            (fun a b => @satisfies _ _ sat2 (ρx.1,a) b)
            ρx.2
            y
        ;
|}.

Definition AppliedOperator'_symbol_builtin_satisfies_OpenTerm
    {Σ : Signature}
    (ρ : Valuation)
    :
    AppliedOperator' symbol builtin_value ->
    OpenTerm ->
    Prop
:=  fun a b =>
    AppliedOperator'_symbol_builtin_satisfies_OpenTermB
        BuiltinOrVar
        (builtin_satisfies_BuiltinOrVar ρ)
        (AppliedOperator'_symbol_builtin_value_satisfies_BOV ρ)
        (aoo_app _ _ a) b
.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin__OpenTerm
    {Σ : Signature}
    :
    Satisfies
        (Valuation*(AppliedOperator' symbol builtin_value))
        OpenTerm
:= {|
    satisfies := fun ρx y =>
        AppliedOperator'_symbol_builtin_satisfies_OpenTerm
            ρx.1
            ρx.2
            y
        ;
|}.

Definition AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC
    {Σ : Signature}
    (ρ : Valuation)
    :
    AppliedOperator' symbol builtin_value ->
    OpenTermWSC ->
    Prop :=
    A_satisfies_B_WithASideCondition
        (AppliedOperator' symbol builtin_value)
        OpenTerm
        (AppliedOperator'_symbol_builtin_satisfies_OpenTerm ρ)
        ρ
.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin__OpenTermWSC
    {Σ : Signature}
    :
    Satisfies
        (Valuation*(AppliedOperator' symbol builtin_value))
        OpenTermWSC
:= {|
    satisfies := fun ρx y =>
        AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC
            ρx.1
            ρx.2
            y
        ;
|}.


Definition GroundTerm_satisfies_LhsPattern
    {Σ : Signature}
    (ρ : Valuation):
    GroundTerm -> LhsPattern -> Prop
:= @aoxyo_satisfies_aoxzo
    symbol
    builtin_value
    OpenTermWSC
    (builtin_value_satisfies_OpenTermWSC ρ)
    (AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC ρ)
.

#[export]
Instance Satisfies__GroundTerm__LhsPattern
    {Σ : Signature}
    :
    Satisfies
        (Valuation*GroundTerm)
        LhsPattern
:= {|
    satisfies := fun ρx y =>
        GroundTerm_satisfies_LhsPattern
            ρx.1
            ρx.2
            y
        ;
|}.

Definition GroundTerm_satisfies_RhsPattern
    {Σ : Signature}
    (ρ : Valuation):
    GroundTerm -> RhsPattern -> Prop
:= @aoxyo_satisfies_aoxzo
    symbol
    builtin_value
    Expression
    ((fun x e => Expression_evaluate ρ e = Some x) ∘ (aoo_operand _ _))
    ((fun x e => Expression_evaluate ρ e = Some x) ∘ (aoo_app _ _))
.

#[export]
Instance Satisfies__GroundTerm__RhsPattern
    {Σ : Signature}
    :
    Satisfies
        (Valuation*GroundTerm)
        RhsPattern
:= {|
    satisfies := fun ρx y =>
        GroundTerm_satisfies_RhsPattern
            ρx.1
            ρx.2
            y
        ;
|}.

Definition GroundTerm_satisfies_VarWithSc
    {Σ : Signature}
    (ρ : Valuation):
    GroundTerm ->
    WithASideCondition variable
    -> Prop :=
    A_satisfies_B_WithASideCondition
        GroundTerm
        variable
        (fun g x => ρ !! x = Some g)
        ρ
.

#[export]
Instance Satisfies__GroundTerm__VarWithSc
    {Σ : Signature}
    :
    Satisfies
        (Valuation*GroundTerm)
        (WithASideCondition variable)
:= {|
    satisfies := fun ρx y =>
        GroundTerm_satisfies_VarWithSc
            ρx.1
            ρx.2
            y
        ;
|}.


(* No instance for these two, since they would overlap and it wouldn't be clear whether
   we are interested in the left or right side of the local rewrite *)

Definition GroundTerm_satisfies_left_LocalRewrite
    {Σ : Signature}
    (ρ : Valuation):
    GroundTerm -> LocalRewrite -> Prop :=
    fun g r => satisfies (ρ, g) (lr_from r)
.

Definition GroundTerm_satisfies_right_LocalRewrite
    {Σ : Signature}
    (ρ : Valuation):
    GroundTerm -> LocalRewrite -> Prop :=
    fun g r => satisfies (ρ,g) (lr_to r)
.

Definition GroundTerm_satisfies_LocalRewrite
    {Σ : Signature}
    (ρ : Valuation)
    (lr : LeftRight) (v : GroundTerm) (r : LocalRewrite)
    : Prop :=
match lr with
| LR_Left => GroundTerm_satisfies_left_LocalRewrite ρ v r
| LR_Right => GroundTerm_satisfies_right_LocalRewrite ρ v r
end.

#[export]
Instance Satisfies__GroundTerm__LocalRewrite
    {Σ : Signature}
    :
    Satisfies
        (Valuation*GroundTerm)
        (LeftRight*LocalRewrite)
:= {|
    satisfies := fun ρx dy =>
        GroundTerm_satisfies_LocalRewrite
            ρx.1
            dy.1
            ρx.2
            dy.2
        ;
|}.

Definition GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    (ρ : Valuation)
    (lr : LeftRight)
    (g : GroundTerm)
    (rb : LocalRewriteOrOpenTermOrBOV)
    : Prop :=
match rb with
| lp_rewrite r
    => satisfies (ρ,g) (lr,r)
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
        (Valuation*GroundTerm)
        (LeftRight*LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies := fun ρx dy =>
        GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
            ρx.1
            dy.1
            ρx.2
            dy.2
        ;
|}.

Definition builtin_satisfies_LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    (ρ : Valuation)
    (lr : LeftRight)
    (b : builtin_value)
    (rb : LocalRewriteOrOpenTermOrBOV)
    : Prop :=
match rb with
| lp_rewrite r
    => satisfies (ρ,(aoo_operand _ _ b)) (lr,r)

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
        (Valuation*builtin_value)
        (LeftRight*LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies := fun ρx dy =>
        builtin_satisfies_LocalRewriteOrOpenTermOrBOV
            ρx.1
            dy.1
            ρx.2
            dy.2
        ;
|}.

Definition GroundTerm_satisfies_UncondRewritingRule
    {Σ : Signature}
    (ρ : Valuation)
    (lr : LeftRight)
    : GroundTerm -> UncondRewritingRule -> Prop
:= @aoxyo_satisfies_aoxzo
        symbol
        builtin_value
        LocalRewriteOrOpenTermOrBOV
        (builtin_satisfies_LocalRewriteOrOpenTermOrBOV ρ lr)
        ((GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV ρ lr) ∘ (aoo_app _ _))
.

#[export]
Instance Satisfies__GroundTerm__UncondRewritingRule
    {Σ : Signature}
    :
    Satisfies
        (Valuation*GroundTerm)
        (LeftRight*UncondRewritingRule)
:= {|
    satisfies := fun ρx dy =>
        GroundTerm_satisfies_UncondRewritingRule
            ρx.1
            dy.1
            ρx.2
            dy.2
        ;
|}.

Definition GroundTerm_satisfies_RewritingRule
    {Σ : Signature}
    (ρ : Valuation)
    (lr : LeftRight)
    : GroundTerm -> RewritingRule -> Prop :=
    A_satisfies_B_WithASideCondition
        GroundTerm
        UncondRewritingRule
        (GroundTerm_satisfies_UncondRewritingRule ρ lr)
        ρ
.

#[export]
Instance Satisfies__GroundTerm__RewritingRule
    {Σ : Signature}
    :
    Satisfies
        (Valuation*GroundTerm)
        (LeftRight*RewritingRule)
:= {|
    satisfies := fun ρx dy =>
        GroundTerm_satisfies_RewritingRule
            ρx.1
            dy.1
            ρx.2
            dy.2
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

Definition rewrites_in_valuation_to
    {Σ : Signature}
    (ρ : Valuation)
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= satisfies (ρ,from) (LR_Left,r)
/\ satisfies (ρ,to) (LR_Right,r)
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
        satisfies (ρ,from) (LR_Left,r) ->
        ∃ to, satisfies (ρ,to) (LR_Right,r)
.

Definition thy_weakly_well_defined
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Prop
    := ∀ r, r ∈ Γ -> rule_weakly_well_defined r
.


Search Satisfies AppliedOperator' symbol.
