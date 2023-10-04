From Minuska Require Import
    prelude
    spec_syntax
.

Definition Valuation {Σ : Signature}
        := gmap variable Value
    .

Definition val_satisfies_ap
    {Σ : Signature} (ρ : Valuation) (ap : AtomicProposition)
    : Prop :=
match ap with
| ap1 p x =>
    match ρ !! x with
    | Some vx => builtin_unary_predicate_interp p vx
    | None => False
    end
| ap2 p x y =>
    match ρ !! x, ρ !! y with
    | Some vx, Some vy => builtin_binary_predicate_interp p vx vy
    | _,_ => False
    end
end
.

Fixpoint val_satisfies_c
    {Σ : Signature} (ρ : Valuation) (c : Constraint)
    : Prop :=
match c with
| c_True => True
| c_atomic ap => val_satisfies_ap ρ ap
| c_and c1 c2 => val_satisfies_c ρ c1 /\ val_satisfies_c ρ c2
| c_not c' => ~ val_satisfies_c ρ c'
end.

Inductive aoxy_satisfies_aoxz
    {X Y Z : Set}
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

Section with_valuation.
    Context
        {Σ : Signature}
        (ρ : Valuation)
    .

    Fixpoint Expression_evaluate
        (t : Expression) : option Value :=
    match t with
    | ft_element e => Some e
    | ft_variable x => ρ !! x
    | ft_unary f t =>
        e ← Expression_evaluate t; Some (builtin_unary_function_interp f e)
    | ft_binary f t1 t2 =>
        e1 ← Expression_evaluate t1;
        e2 ← Expression_evaluate t2;
        Some (builtin_binary_function_interp f e1 e2)
    end.

    Inductive builtin_satisfies_BuiltinOrVar:
        builtin_value ->
        BuiltinOrVar ->
        Prop :=

    | bsbv_builtin:
        forall b,
            builtin_satisfies_BuiltinOrVar b (bov_builtin b)

    | bsbv_var:
        forall b x,
            ρ !! x = Some (val_builtin b) ->
            builtin_satisfies_BuiltinOrVar b (bov_variable x)
    .

    Definition GroundTerm_satisfies_BuiltinOrVar
        (g : GroundTerm)
        (bov : BuiltinOrVar)
        : Prop :=
    match bov with
    | bov_builtin _ => False
    | bov_variable x => ρ !! x = Some (val_gterm g)
    end.

    Definition aosb_satisfies_aosbf:
        AppliedOperator' symbol builtin_value ->
        AppliedOperator' symbol BuiltinOrVar ->
        Prop :=
    @aoxy_satisfies_aoxz
        symbol
        builtin_value
        BuiltinOrVar
        builtin_satisfies_BuiltinOrVar
        GroundTerm_satisfies_BuiltinOrVar
    .

    Definition in_val_GroundTerm_satisfies_OpenTerm
        (g : GroundTerm)
        (φ : OpenTerm)
        : Prop := aosb_satisfies_aosbf g φ
    .
    (*
    match φ with
    | ot_aop aop => aosb_satisfies_aosbf g aop
    |ot_bov x => x
    end.
    *)

    Definition valuation_satisfies_sc
        (sc : SideCondition) : Prop :=
    match sc with
    | sc_constraint c => val_satisfies_c ρ c
    | sc_match x φ =>
        match ρ !! x with
        | Some (val_gterm g)
            => in_val_GroundTerm_satisfies_OpenTerm g φ
        | _ => False
        end
    end.

    Inductive in_val_GroundTerm_satisfies_OpenTermWSC:
        GroundTerm ->
        OpenTermWSC ->
        Prop :=
    | gsbc_basic:
        forall
            (g : GroundTerm)
            (φ : OpenTerm)
            (pf : in_val_GroundTerm_satisfies_OpenTerm g φ ),
            in_val_GroundTerm_satisfies_OpenTermWSC g (wsc_base φ)
    | gsbc_side:
        forall
            (g : GroundTerm)
            (φc : OpenTermWSC)
            (c : SideCondition)
            (pf1 : in_val_GroundTerm_satisfies_OpenTermWSC g φc)
            (pf2 : valuation_satisfies_sc c),
            in_val_GroundTerm_satisfies_OpenTermWSC g (wsc_sc φc c)
    .

    Definition GroundTerm_satisfies_LhsPattern:
        GroundTerm -> LhsPattern -> Prop
        := fun g φ =>
        match φ with
        | lp_aop aop =>
          @aoxy_satisfies_aoxz
            symbol
            builtin_value
            OpenTermWSC
            (fun x y => False)
            in_val_GroundTerm_satisfies_OpenTermWSC
            g aop
        | lp_otwsc otwsc =>
            in_val_GroundTerm_satisfies_OpenTermWSC g otwsc
        end.
    
    Definition GroundTerm_satisfies_RhsPattern:
        GroundTerm -> RhsPattern -> Prop
        := fun g φ =>
        match φ with 
        | rp_aop aop =>
          @aoxy_satisfies_aoxz
            symbol
            builtin_value
            Expression
            (fun b e => Expression_evaluate e = Some (val_builtin b))
            (fun g e => Expression_evaluate e = Some (val_gterm g))
            g aop
        | rp_exp exp => Expression_evaluate exp = Some (val_gterm g)
        end
    .

    Inductive Value_satisfies_VarWithSc:
        Value -> WithASideCondition variable -> Prop :=

    | vsvsc_var:
        forall x v,
            ρ !! x = Some v ->
            Value_satisfies_VarWithSc v (wsc_base x)

    | vsvsc_sc :
        forall x v sc,
            Value_satisfies_VarWithSc v x ->
            valuation_satisfies_sc sc ->
            Value_satisfies_VarWithSc v (wsc_sc x sc)
    .


    Inductive Value_satisfies_left_LocalRewrite:
        Value -> LocalRewrite -> Prop :=

    | vslr_left_var:
        forall v x e,
            Value_satisfies_VarWithSc v x ->
            Value_satisfies_left_LocalRewrite
                v (lr_var x e)
    
    | vslr_left_builtin:
        forall b e,
            Value_satisfies_left_LocalRewrite
                (val_builtin b) (lr_builtin b e)
    
    | vslr_left_pattern:
        forall g φl φr,
            GroundTerm_satisfies_LhsPattern g φl ->
            Value_satisfies_left_LocalRewrite
                (val_gterm g) (lr_pattern φl φr)

    .

    Inductive Value_satisfies_right_LocalRewrite:
        Value -> LocalRewrite -> Prop :=

    | vlsr_right_var:
        forall v x e,
            Value_satisfies_right_LocalRewrite
                v (lr_var x e)
    
    | vlsr_right_builtin:
        forall b v e,
            Expression_evaluate e = Some v ->
            Value_satisfies_right_LocalRewrite
                v (lr_builtin b e)
    
    | vlsr_right_pattern:
        forall g φl φr,
            GroundTerm_satisfies_RhsPattern g φr ->
            Value_satisfies_right_LocalRewrite
                (val_gterm g) (lr_pattern φl φr)
    .

    Definition Value_satisfies_LocalRewrite
        (lr : LeftRight) (v : Value) (r : LocalRewrite)
        : Prop :=
    match lr with
    | LR_Left => Value_satisfies_left_LocalRewrite v r
    | LR_Right => Value_satisfies_right_LocalRewrite v r
    end.

    Definition GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
        (lr : LeftRight)
        (g : GroundTerm)
        (rb : LocalRewriteOrOpenTermOrBOV)
        : Prop :=
    match rb with
    | lp_rewrite r =>
        Value_satisfies_LocalRewrite lr (val_gterm g) r
    | lp_basicpat φ =>
        in_val_GroundTerm_satisfies_OpenTerm g φ
    | lp_bov bx => False
    end.


    Definition builtin_satisfies_LocalRewriteOrOpenTermOrBOV
        (lr : LeftRight)
        (b : builtin_value)
        (rb : LocalRewriteOrOpenTermOrBOV)
        : Prop :=
    match rb with
    | lp_rewrite r =>
        Value_satisfies_LocalRewrite lr (val_builtin b) r
    | lp_basicpat φ =>
        False
    | lp_bov bx =>
        builtin_satisfies_BuiltinOrVar b bx
    end.

    Definition GroundTerm_satisfies_UncondRewritingRule
        (lr : LeftRight)
        : GroundTerm -> UncondRewritingRule -> Prop
    := @aoxy_satisfies_aoxz
            symbol
            builtin_value
            LocalRewriteOrOpenTermOrBOV
            (builtin_satisfies_LocalRewriteOrOpenTermOrBOV lr)
            (GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV lr)
    .


    (* TODO: factor out the commonalities with Value_satisfies_VarWithSc *)
    Inductive GroundTerm_satisfies_RewritingRule
        (lr : LeftRight)
        : GroundTerm -> RewritingRule -> Prop :=

    | gtsr_base:
        forall g r,
            GroundTerm_satisfies_UncondRewritingRule lr g r ->
            GroundTerm_satisfies_RewritingRule lr g (wsc_base r)

    | gtsr_sc :
        forall g r sc,
            GroundTerm_satisfies_RewritingRule lr g r ->
            valuation_satisfies_sc sc ->
            GroundTerm_satisfies_RewritingRule lr g (wsc_sc r sc)
    .



End with_valuation.


Definition GroundTerm_satisfies_OpenTerm
    {Σ : Signature}
    : GroundTerm -> OpenTerm -> Prop :=
    fun g φ => ∃ ρ, in_val_GroundTerm_satisfies_OpenTerm ρ g φ
.

Definition rewrites_in_valuation_to
    {Σ : Signature}
    (ρ : Valuation)
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= GroundTerm_satisfies_RewritingRule ρ LR_Left from r
/\ GroundTerm_satisfies_RewritingRule ρ LR_Right to r
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
        GroundTerm_satisfies_RewritingRule ρ LR_Left from r ->
        ∃ to, GroundTerm_satisfies_RewritingRule ρ LR_Right to r
.

Definition thy_weakly_well_defined
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Prop
    := ∀ r, r ∈ Γ -> rule_weakly_well_defined r
.



