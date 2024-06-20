From Minuska Require Import
    prelude
    spec
    basic_properties
    lowlang
    properties
    basic_matching
    varsof
    syntax_properties
    minusl_syntax
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
    (isValue : Expression -> (list SideCondition))
    (c : TermOver BuiltinOrVar)
    (h : variable) (* occurs once in `c` *)
    (scs : list SideCondition)
    :
    RewritingRule Act
:= {|
    fr_from := (uglify' (t_term topSymbol [
        (t_term cseqSymbol [
            c;
            (t_over (bov_variable contVariable))
        ]);
        t_over (bov_variable dataVariable)])
    );
    fr_to   := (uglify' (t_term topSymbol [
        (t_term cseqSymbol [
            (t_over (ft_variable h));
            (t_term cseqSymbol [
                (TermOverBoV_to_TermOverExpr
                    (TermOverBoV_subst c h (t_term holeSymbol []))
                );
                (t_over (ft_variable contVariable))
            ])
        ]);
        t_over (ft_variable dataVariable)])
    );
    fr_scs := scs;
    fr_act := invisible_act ;
|}.

Definition ctx_cool
    {Σ : StaticModel}
    {Act : Set}
    (invisible_act : Act)
    (topSymbol cseqSymbol holeSymbol : symbol)
    (contVariable dataVariable : variable)
    (isValue : Expression -> (list SideCondition))
    (c : TermOver BuiltinOrVar)
    (h : variable)
    :
    RewritingRule Act
:= {|
    fr_from := (uglify' (t_term topSymbol [
        (t_term cseqSymbol [
            (t_over (bov_variable h));
            (t_term cseqSymbol [
                (TermOverBoV_subst c h (t_term holeSymbol []));
                (t_over (bov_variable contVariable))
            ])
        ]);
        t_over (bov_variable dataVariable)])
    );

    fr_to   := (uglify' (t_term topSymbol [
        (t_term cseqSymbol [
            (TermOverBoV_to_TermOverExpr c);
            (t_over (ft_variable contVariable))
        ]);
        t_over (ft_variable dataVariable)])
    );

    fr_scs := isValue (ft_variable h);

    fr_act := invisible_act ;
|}.


Definition CompileT {Σ : StaticModel} {Act : Set} : Type :=
    MinusL_LangDef Act -> RewritingTheory Act
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
    (ctrl data : TermOver Expression)
    : TermOver Expression
:=
    t_term topSymbol
        [
            (t_term cseqSymbol
                [
                    ctrl;
                    t_over (ft_variable continuationVariable)
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
    (isValue : Expression -> (list SideCondition))
    (avoid : gset variable)
    (d : MinusL_Decl Act)
    : (list (RewritingRule Act))
:=
    match d with
    | mld_rewrite _ lc ld a rc rd scs => [
        ({|
            fr_from := uglify' (down2 topSymbol cseqSymbol continuationVariable lc ld) ;
            fr_to := uglify' (down2E topSymbol cseqSymbol continuationVariable rc rd) ;
            fr_scs := scs ;
            fr_act := a;
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
                c h scs
            );
            (ctx_cool
                invisible_act
                topSymbol cseqSymbol holeSymbol
                contVariable dataVariable
                isValue
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
            (vars_of (mlld_isValue_scs Act D))
        ) (mlld_decls Act D))
.
