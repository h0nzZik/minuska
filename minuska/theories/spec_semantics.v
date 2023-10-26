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

Definition aosb_satisfies_aosbf
    {Σ : Signature}
    (ρ : Valuation)
    :
    AppliedOperator' symbol builtin_value ->
    AppliedOperator' symbol BuiltinOrVar ->
    Prop :=
    @aoxy_satisfies_aoxz
        symbol
        builtin_value
        BuiltinOrVar
        (builtin_satisfies_BuiltinOrVar ρ)
        (AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ)
.

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

Definition in_val_GroundTerm_satisfies_OpenTerm
    {Σ : Signature}
    (ρ : Valuation)
    (g : GroundTerm)
    (φ : OpenTerm)
    : Prop := aoosb_satisfies_aoosbf ρ g φ
.

Definition valuation_satisfies_sc
    {Σ : Signature}
    (ρ : Valuation)
    (sc : SideCondition) : Prop :=
match sc with
| sc_constraint c => val_satisfies_c ρ c
| sc_match x φ =>
    match ρ !! x with
    | Some g
        => in_val_GroundTerm_satisfies_OpenTerm ρ g φ
    | _ => False
    end
end.

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


Section with_valuation.
    Context
        {Σ : Signature}
        (ρ : Valuation)
    .

    Definition GroundTerm_satisfies_BuiltinOrVar
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


    Definition in_val_GroundTerm_satisfies_OpenTermWSC:
        GroundTerm ->
        OpenTermWSC ->
        Prop :=
        A_satisfies_B_WithASideCondition
            GroundTerm
            OpenTerm
            (in_val_GroundTerm_satisfies_OpenTerm ρ)
            ρ
    .

    Definition builtin_value_satisfies_OpenTerm:
        builtin_value ->
        OpenTerm ->
        Prop := fun b t =>
    match t with
    | aoo_app _ _ _ => False
    | aoo_operand _ _ bov =>
        builtin_satisfies_BuiltinOrVar ρ b bov
    end.

    Definition builtin_value_satisfies_OpenTermWSC:
        builtin_value ->
        OpenTermWSC ->
        Prop :=
        A_satisfies_B_WithASideCondition
            builtin_value
            OpenTerm
            builtin_value_satisfies_OpenTerm
            ρ
    .

    (*
    (* TODO prove that this is equivalent to aoxyo_satisfies_aoxzo. *)
    Definition AppliedOperator'_symbol_builtin_satisfies_OpenTermB
        (B : Type)
        (AppliedOperator'_symbol_builtin_satisfies_B:
            Valuation ->
            AppliedOperator' symbol builtin_value ->
            B ->
            Prop
        )
        (builtin_satisfies_B:
            Valuation ->
            builtin_value ->
            B ->
            Prop
        )
        :
        AppliedOperator' symbol builtin_value ->
        AppliedOperatorOr' symbol B ->
        Prop
    := fun asb o =>
    match o with
    | aoo_app _ _ t =>
        @aoxy_satisfies_aoxz
        symbol
        builtin_value
        B
        (builtin_satisfies_B ρ)
        (AppliedOperator'_symbol_builtin_satisfies_B ρ)
        asb t
    | aoo_operand _ _ bov => AppliedOperator'_symbol_builtin_satisfies_B ρ asb bov
    end.
    *)

    Definition AppliedOperator'_symbol_builtin_value_satisfies_BOV
        (ao : AppliedOperator' symbol builtin_value)
        (bov : BuiltinOrVar)
        : Prop
    :=
    match bov with
    | bov_builtin _ => False
    | bov_variable x => ρ !! x = Some (aoo_app _ _ ao) 
    end
    .

    Definition AppliedOperator'_symbol_builtin_satisfies_OpenTermB'
        (B : Type)
        (builtin_satisfies_B : builtin_value -> B -> Prop)
        AppliedOperator'_symbol_builtin_value_satisfies_B
        :
        AppliedOperator' symbol builtin_value ->
        AppliedOperatorOr' symbol B ->
        Prop
    :=  fun a b => @aoxyo_satisfies_aoxzo symbol builtin_value B
        builtin_satisfies_B
        AppliedOperator'_symbol_builtin_value_satisfies_B
        (aoo_app _ _ a) b
    .

    Definition AppliedOperator'_symbol_builtin_satisfies_OpenTermB
        (B : Type)
        (builtin_satisfies_B : builtin_value -> B -> Prop)
        AppliedOperator'_symbol_builtin_value_satisfies_B
        :
        AppliedOperatorOr' symbol builtin_value ->
        AppliedOperatorOr' symbol B ->
        Prop
    :=  @aoxyo_satisfies_aoxzo symbol builtin_value B
        builtin_satisfies_B
        AppliedOperator'_symbol_builtin_value_satisfies_B
    .

    Definition AppliedOperator'_symbol_builtin_satisfies_OpenTerm:
        AppliedOperator' symbol builtin_value ->
        OpenTerm ->
        Prop
    :=  fun a b =>
        AppliedOperator'_symbol_builtin_satisfies_OpenTermB
            BuiltinOrVar
            (builtin_satisfies_BuiltinOrVar ρ)
            AppliedOperator'_symbol_builtin_value_satisfies_BOV
            (aoo_app _ _ a) b
    .
    
    Definition AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC:
        AppliedOperator' symbol builtin_value ->
        OpenTermWSC ->
        Prop :=
        A_satisfies_B_WithASideCondition
            (AppliedOperator' symbol builtin_value)
            OpenTerm
            (AppliedOperator'_symbol_builtin_satisfies_OpenTerm)
            ρ
    .

    Definition GroundTerm_satisfies_LhsPattern:
        GroundTerm -> LhsPattern -> Prop
    := @aoxyo_satisfies_aoxzo
        symbol
        builtin_value
        OpenTermWSC
        builtin_value_satisfies_OpenTermWSC
        AppliedOperator'_symbol_builtin_value_satisfies_OpenTermWSC
    .

    Definition GroundTerm_satisfies_RhsPattern:
        GroundTerm -> RhsPattern -> Prop
    := @aoxyo_satisfies_aoxzo
        symbol
        builtin_value
        Expression
        ((fun x e => Expression_evaluate ρ e = Some x) ∘ (aoo_operand _ _))
        ((fun x e => Expression_evaluate ρ e = Some x) ∘ (aoo_app _ _))
    .

    Definition GroundTerm_satisfies_VarWithSc:
        GroundTerm ->
        WithASideCondition variable
        -> Prop :=
        A_satisfies_B_WithASideCondition
            GroundTerm
            variable
            (fun g x => ρ !! x = Some g)
            ρ
    .

    Definition GroundTerm_satisfies_left_LocalRewrite:
        GroundTerm -> LocalRewrite -> Prop :=
        fun g r => GroundTerm_satisfies_LhsPattern g (lr_from r)
    .

    Definition GroundTerm_satisfies_right_LocalRewrite:
        GroundTerm -> LocalRewrite -> Prop :=
        fun g r => GroundTerm_satisfies_RhsPattern g (lr_to r)
    .

    Definition GroundTerm_satisfies_LocalRewrite
        (lr : LeftRight) (v : GroundTerm) (r : LocalRewrite)
        : Prop :=
    match lr with
    | LR_Left => GroundTerm_satisfies_left_LocalRewrite v r
    | LR_Right => GroundTerm_satisfies_right_LocalRewrite v r
    end.

    Definition GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
        (lr : LeftRight)
        (g : GroundTerm)
        (rb : LocalRewriteOrOpenTermOrBOV)
        : Prop :=
    match rb with
    | lp_rewrite r =>
        GroundTerm_satisfies_LocalRewrite lr g r
    | lp_basicpat φ =>
        in_val_GroundTerm_satisfies_OpenTerm ρ g φ
    | lp_bov bx => GroundTerm_satisfies_BuiltinOrVar g bx
    end.

    Definition builtin_satisfies_LocalRewriteOrOpenTermOrBOV
        (lr : LeftRight)
        (b : builtin_value)
        (rb : LocalRewriteOrOpenTermOrBOV)
        : Prop :=
    match rb with
    | lp_rewrite r =>
        GroundTerm_satisfies_LocalRewrite lr (aoo_operand _ _ b) r
    | lp_basicpat (aoo_app _ _ _) =>
        False
    | lp_basicpat (aoo_operand _ _ bov) =>
        builtin_satisfies_BuiltinOrVar ρ b bov
    | lp_bov bx =>
        builtin_satisfies_BuiltinOrVar ρ b bx
    end.

    Definition GroundTerm_satisfies_UncondRewritingRule
        (lr : LeftRight)
        : GroundTerm -> UncondRewritingRule -> Prop
    := @aoxyo_satisfies_aoxzo
            symbol
            builtin_value
            LocalRewriteOrOpenTermOrBOV
            (builtin_satisfies_LocalRewriteOrOpenTermOrBOV lr)
            ((GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV lr) ∘ (aoo_app _ _))
    .


    (* TODO: factor out the commonalities with GroundTerm_satisfies_VarWithSc *)
    Definition GroundTerm_satisfies_RewritingRule
        (lr : LeftRight)
        : GroundTerm -> RewritingRule -> Prop :=
        A_satisfies_B_WithASideCondition
            GroundTerm
            UncondRewritingRule
            (GroundTerm_satisfies_UncondRewritingRule lr)
            ρ
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



