From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    minusl_syntax
    termoverbov_subst
.

Require Import Ring.
Require Import ArithRing.
Require Import Coq.Logic.FunctionalExtensionality.

(*
    @pre: topSymbol, cseqSymbol, holeSymbol, contVariable, and dataVariable have to be fresh enough
*)
Definition ctx_heat
    {Σ : StaticModel}
    {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (contVariable dataVariable : variable)
    (isValue : Expression2 -> SideCondition)
    (isNonValue : Expression2 -> SideCondition)
    (c : TermOver BuiltinOrVar)
    (h : variable) (* occurs once in `c` *)
    (cond : SideCondition)
    :
    RewritingRule2 Act
:= {|
    r_from := ((t_term topSymbol [
        (t_term cseqSymbol [
            c;
            (t_over (bov_variable contVariable))
        ]);
        t_over (bov_variable dataVariable)])
    );
    r_to   := ((t_term topSymbol [
        (t_term cseqSymbol [
            (t_over (e_variable h));
            (t_term cseqSymbol [
                (TermOverBoV_to_TermOverExpr2
                    (TermOverBoV_subst c h (t_term holeSymbol []))
                );
                (t_over (e_variable contVariable))
            ])
        ]);
        t_over (e_variable dataVariable)])
    );
    r_scs := cond;
    r_act := invisible_act ;
|}.

Definition ctx_cool
    {Σ : StaticModel}
    {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (contVariable dataVariable : variable)
    (isValue : Expression2 -> SideCondition)
    (isNonValue : Expression2 -> SideCondition)
    (c : TermOver BuiltinOrVar)
    (h : variable)
    :
    RewritingRule2 Act
:= {|
    r_from := ((t_term topSymbol [
        (t_term cseqSymbol [
            (t_over (bov_variable h));
            (t_term cseqSymbol [
                (TermOverBoV_subst c h (t_term holeSymbol []));
                (t_over (bov_variable contVariable))
            ])
        ]);
        t_over (bov_variable dataVariable)])
    );

    r_to   := ((t_term topSymbol [
        (t_term cseqSymbol [
            (TermOverBoV_to_TermOverExpr2 c);
            (t_over (e_variable contVariable))
        ]);
        t_over (e_variable dataVariable)])
    );

    r_scs := isValue (e_variable h);

    r_act := invisible_act ;
|}.


Definition CompileT {Σ : StaticModel} {Act : Set} : Type :=
    MinusL_LangDef Act -> RewritingTheory2 Act
.

Definition down2
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (continuationVariable : variable)
    (ctrl data : TermOver BuiltinOrVar)
    : TermOver BuiltinOrVar
:=
    t_term topSymbol
        [
            (t_term cseqSymbol
                [
                    ctrl;
                    t_over (bov_variable continuationVariable)
                ]
            );
            data
        ]
.

Definition down2E
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (continuationVariable : variable)
    (ctrl data : TermOver Expression2)
    : TermOver Expression2
:=
    t_term topSymbol
        [
            (t_term cseqSymbol
                [
                    ctrl;
                    t_over (e_variable continuationVariable)
                ]
            );
            data
        ]
.

Definition downC
    {Σ : StaticModel}
    (topSymbol cseqSymbol : symbol)
    (ctrl data continuation : TermOver builtin_value)
    : TermOver builtin_value
:=
    t_term topSymbol
        [
            (t_term cseqSymbol
                [
                    ctrl;
                    continuation
                ]
            );
            data
        ]
.

Definition compile' {Σ : StaticModel} {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable)
    (isValue : Expression2 -> SideCondition)
    (isNonValue : Expression2 -> SideCondition)
    (avoid : gset variable)
    (d : MinusL_Decl Act)
    : (list (RewritingRule2 Act))
:=
    match d with
    | mld_rewrite _ lc ld a rc rd cond => [
        ({|
            r_from := (down2 topSymbol cseqSymbol continuationVariable lc ld) ;
            r_to := (down2E topSymbol cseqSymbol continuationVariable rc rd) ;
            r_scs := cond ;
            r_act := a;
        |})
        ]
    | mld_context _ c h scs =>
        let vars := vars_of_to_l2r c in
        let scs_vars := elements (vars_of scs) in
        let lavoid := elements avoid in
        let contVariable := fresh (h::(vars++scs_vars++lavoid)) in
        let dataVariable := fresh (h::contVariable::(vars++scs_vars++lavoid)) in
         [
            (ctx_heat
                invisible_act
                topSymbol cseqSymbol holeSymbol
                contVariable dataVariable
                isValue
                isNonValue
                c h scs
            );
            (ctx_cool
                invisible_act
                topSymbol cseqSymbol holeSymbol
                contVariable dataVariable
                isValue
                isNonValue
                c h
            )
        ]
    end
.

Definition compile {Σ : StaticModel}
    {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (continuationVariable : variable)
    : CompileT :=
    fun D => concat (map (
        compile'
            invisible_act
            topSymbol
            cseqSymbol
            holeSymbol
            continuationVariable
            (MinusL_isValue Act D)
            (MinusL_isNonValue Act D)
            (
                (vars_of (mlld_isValue_c Act D))
                ∪
                (vars_of (mlld_isNonValue_c Act D))
            )
        ) (mlld_decls Act D))
.
