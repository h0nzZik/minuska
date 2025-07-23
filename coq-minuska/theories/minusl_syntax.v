From stdpp Require Import finite.

From Minuska Require Import
    prelude
    spec
    basic_properties
.

Variant MinusL_Decl {Σ : StaticModel} (Label : Set) :=
| mld_rewrite
    (lc : TermOver BuiltinOrVar) (ld : TermOver BuiltinOrVar)
    (a : Label)
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
    (Label : Set)
    {_eA : EqDecision Label}
    :
    EqDecision (MinusL_Decl Label)
.
Proof.
    ltac1:(solve_decision).
Defined.

Definition actions_of_decl
    {Σ : StaticModel}
    (Label : Set)
    (d : MinusL_Decl Label)
    : list Label
:=
match d with
| mld_rewrite _ _ _ a _ _ _ => [a]
| mld_context _ _ _ _ => []
end.


Record MinusL_LangDef
    {Σ : StaticModel}
    (Label : Set)
    : Type
 := mkMinusL_LangDef {
    mlld_isValue_c : SideCondition ;
    mlld_isNonValue_c : SideCondition ;
    mlld_isValue_var : variable ;
    mlld_decls : list (MinusL_Decl Label) ;
}.

Definition MinusL_LangDef_wf
    {Σ : StaticModel}
    (Label : Set)
    (D : MinusL_LangDef Label)
    : Prop
:=
    vars_of (mlld_isValue_c Label D) = {[ mlld_isValue_var Label D ]}
    /\
    vars_of (mlld_isNonValue_c Label D) = {[ mlld_isValue_var Label D ]}
    /\ (
        ∀ c h scs,
        (mld_context Label c h scs) ∈ (mlld_decls Label D) ->
        h <> (mlld_isValue_var Label D)
        /\ (length (filter (eq h) (vars_of_to_l2r c)) = 1)
        /\ (h ∉ vars_of scs)
    )
.
(*
    ∀ c h Hh scs Hhscs,
        (mld_context Label c h Hh scs Hhscs) ∈ (mlld_decls Label D) ->
        h ∉ vars_of (mlld_isValue_scs Label D)
.
*)
Definition MinusL_isValue
    {Σ : StaticModel}
    (Label : Set)
    (D : MinusL_LangDef Label)
    :
    Expression2 -> SideCondition
:=
    let x := (mlld_isValue_var Label D) in
    let c := mlld_isValue_c Label D in
    fun e => SideCondition_subst c x e
.

Definition MinusL_isNonValue
    {Σ : StaticModel}
    (Label : Set)
    (D : MinusL_LangDef Label)
    :
    Expression2 -> SideCondition
:=
    let x := (mlld_isValue_var Label D) in
    let c := mlld_isNonValue_c Label D in
    fun e => SideCondition_subst c x e
.

Definition actions_of_ldef
    {Σ : StaticModel}
    (Label : Set)
    (D : MinusL_LangDef Label)
    : list Label
:=
    concat (map (actions_of_decl Label) (mlld_decls Label D))
.


#[export]
Instance VarsOf_MinusL_Decl
    {Σ : StaticModel}
    (Label : Set)
    : VarsOf (MinusL_Decl Label) variable
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
    (Label : Set)
    : VarsOf (MinusL_LangDef Label) variable
:= {|
    vars_of := fun D => union_list (vars_of <$> (mlld_decls Label D)) ; 
|}.

