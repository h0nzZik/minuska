From stdpp Require Import finite.

From Minuska Require Import
    prelude
    spec
    basic_properties
.

Variant MinusL_Decl {Σ : StaticModel} (Act : Set) :=
| mld_rewrite
    (lc : TermOver BuiltinOrVar) (ld : TermOver BuiltinOrVar)
    (a : Act)
    (rc : TermOver Expression2) (rd : TermOver Expression2)
    (scs : SideCondition)
| mld_context
    (ctx : TermOver BuiltinOrVar)
    (h : variable)
    (c : SideCondition)
.

#[export]
Instance MinusL_Decl_eqDec
    {Σ : StaticModel}
    (Act : Set)
    {_eA : EqDecision Act}
    :
    EqDecision (MinusL_Decl Act)
.
Proof.
    ltac1:(solve_decision).
Defined.

Definition actions_of_decl
    {Σ : StaticModel}
    (Act : Set)
    (d : MinusL_Decl Act)
    : list Act
:=
match d with
| mld_rewrite _ _ _ a _ _ _ => [a]
| mld_context _ _ _ _ => []
end.


Record MinusL_LangDef
    {Σ : StaticModel}
    (Act : Set)
    : Type
 := mkMinusL_LangDef {
    mlld_isValue_c : SideCondition ;
    mlld_isNonValue_c : SideCondition ;
    mlld_isValue_var : variable ;
    mlld_decls : list (MinusL_Decl Act) ;
}.

Definition MinusL_LangDef_wf
    {Σ : StaticModel}
    (Act : Set)
    (D : MinusL_LangDef Act)
    : Prop
:=
    vars_of (mlld_isValue_c Act D) = {[ mlld_isValue_var Act D ]}
    /\
    vars_of (mlld_isNonValue_c Act D) = {[ mlld_isValue_var Act D ]}
    /\ (
        ∀ c h scs,
        (mld_context Act c h scs) ∈ (mlld_decls Act D) ->
        h <> (mlld_isValue_var Act D)
        /\ (length (filter (eq h) (vars_of_to_l2r c)) = 1)
        /\ (h ∉ vars_of scs)
    )
.
(*
    ∀ c h Hh scs Hhscs,
        (mld_context Act c h Hh scs Hhscs) ∈ (mlld_decls Act D) ->
        h ∉ vars_of (mlld_isValue_scs Act D)
.
*)
Definition MinusL_isValue
    {Σ : StaticModel}
    (Act : Set)
    (D : MinusL_LangDef Act)
    :
    Expression2 -> SideCondition
:=
    let x := (mlld_isValue_var Act D) in
    let c := mlld_isValue_c Act D in
    fun e => SideCondition_subst c x e
.

Definition MinusL_isNonValue
    {Σ : StaticModel}
    (Act : Set)
    (D : MinusL_LangDef Act)
    :
    Expression2 -> SideCondition
:=
    let x := (mlld_isValue_var Act D) in
    let c := mlld_isNonValue_c Act D in
    fun e => SideCondition_subst c x e
.

Definition actions_of_ldef
    {Σ : StaticModel}
    (Act : Set)
    (D : MinusL_LangDef Act)
    : list Act
:=
    concat (map (actions_of_decl Act) (mlld_decls Act D))
.


#[export]
Instance VarsOf_MinusL_Decl
    {Σ : StaticModel}
    (Act : Set)
    : VarsOf (MinusL_Decl Act) variable
:= {|
    vars_of := fun D => match D with
    | mld_rewrite _ lc ld _ rc rd scs => (vars_of lc) ∪ vars_of ld ∪
        vars_of rc ∪ vars_of rd ∪ vars_of scs
    | mld_context _ c h scs => (vars_of c) ∪ {[h]} ∪ vars_of scs
    end ; 
|}.

#[export]
Instance VarsOf_MinusL_LangDef
    {Σ : StaticModel}
    (Act : Set)
    : VarsOf (MinusL_LangDef Act) variable
:= {|
    vars_of := fun D => union_list (vars_of <$> (mlld_decls Act D)) ; 
|}.

