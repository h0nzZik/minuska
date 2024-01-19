From Minuska Require Import
    prelude
    spec_syntax
    flattened
    notations
    default_static_model
    builtins
.


Import default_builtin.
Export default_builtin.Notations.


Arguments ft_unary {Σ} f (t).
Arguments ft_binary {Σ} f (t1) (t2).
Arguments ft_ternary {Σ} f (t1) (t2) (t3).


Fixpoint OpenTerm_to_ExprTerm'
    {Σ : StaticModel}
    (t : AppliedOperator' symbol BuiltinOrVar)
    : AppliedOperator' symbol Expression
:=
match t with
| ao_operator s => ao_operator s
| ao_app_operand ao (bov_variable x)
    => ao_app_operand (OpenTerm_to_ExprTerm' ao) (ft_variable x)
| ao_app_operand ao (bov_builtin b)
    => ao_app_operand (OpenTerm_to_ExprTerm' ao) (ft_element (aoo_operand b))
| ao_app_ao ao1 ao2
    => ao_app_ao (OpenTerm_to_ExprTerm' ao1) (OpenTerm_to_ExprTerm' ao2)
end
.

Definition OpenTerm_to_ExprTerm
    {Σ : StaticModel}
    (t : AppliedOperatorOr' symbol BuiltinOrVar)
    : AppliedOperatorOr' symbol Expression
:=
match t with
| aoo_operand (bov_variable x) => aoo_operand (ft_variable x)
| aoo_operand (bov_builtin b) => aoo_operand (ft_element (aoo_operand b))
| aoo_app t' => aoo_app (OpenTerm_to_ExprTerm' t')
end
.

Definition label {Σ : StaticModel} :=
    string
.


Definition ContextTemplate
    {Σ : StaticModel}
:=
    forall (br:BasicResolver) (r:Resolver),
    AppliedOperatorOr' symbol operand_type ->
    AppliedOperatorOr' symbol operand_type
.


Notation
    "( 'context-template' x 'with' h )"
    :=
    (fun (_:BasicResolver) (_:Resolver) (h : AppliedOperatorOr' symbol operand_type) => x)
.



Record ContextDeclaration {Σ : StaticModel}
:= mkContextDeclaration {
    cd_label : label ;
    cd_sym : symbol ;
    cd_arity : nat ;
    cd_position : nat ;
    cd_isValue : Expression -> Expression ;
    cd_cseq_context : ContextTemplate;
}.

Record StrictnessDeclaration {Σ : StaticModel}
:= mkStrictnessDeclaration {
    sd_sym : symbol ;
    sd_arity : nat ;
    sd_positions : list nat ;
    sd_isValue : Expression -> Expression ;
    sd_cseq_context : ContextTemplate ;
}.


Notation
    "( 'symbol' s 'of' 'arity' a 'strict' 'in' l 'with-result' r 'by-template' t )"
    :=
    (
        (
            {|
                sd_sym := s ;
                sd_arity := a ;
                sd_positions := l ;
                sd_isValue := r ;
                sd_cseq_context := t ;
            |}
        )
    )
.

Class Defaults {Σ : StaticModel} := {
    default_cseq_name : string ;
    default_empty_cseq_name : string ;
    default_context_template : ContextTemplate ;
    default_isValue : Expression -> Expression ;
}.

Notation
    "( 'symbol' s 'of' 'arity' a 'strict' 'in' l )"
:=
    (
        (
            {|
                sd_sym := s ;
                sd_arity := a ;
                sd_positions := l ;
                sd_isValue := default_isValue ;
                sd_cseq_context := default_context_template ;
            |}
        )
    )
.

Definition strictness_to_contexts
    {Σ : StaticModel}
    (sym_to_str : symbol -> string)
    (str_to_sym : string -> symbol)
    (str_to_label : string -> label)
    (sd : StrictnessDeclaration)
    : list ContextDeclaration
:=
    map (fun position => {|
            cd_label := (str_to_label (sym_to_str (sd_sym sd) +:+ ("-" +:+ (pretty position)))) ;
            cd_sym := sd_sym sd ;
            cd_arity := sd_arity sd ;
            cd_position := position ;
            cd_isValue := sd_isValue sd ;
            cd_cseq_context := @sd_cseq_context Σ sd ;
        |})
        (sd_positions sd)
.

Record RuleDeclaration {Σ : StaticModel}
:= mkRuleDeclaration {
    rd_label : label ;
    rd_rule : FlattenedRewritingRule ;
}.

Arguments mkRuleDeclaration {Σ} rd_label rd_rule.

Inductive Declaration {Σ : StaticModel} :=
| decl_rule (r : RuleDeclaration)
| decl_ctx (c : ContextDeclaration)
| decl_strict (s : StrictnessDeclaration)
.

(*Coercion decl_rule : RuleDeclaration >-> Declaration.*)

Notation "'rule' '[' n ']:' l ~> r"
    := ((mkRuleDeclaration
        n (rule (l) ~> (r) requires nil)
    ))
    (at level 200)
.

Notation "'rule' '[' n ']:' l ~> r 'where' s"
    := ((mkRuleDeclaration
        n (rule (l) ~> (r) requires (cons (sc_constraint (apeq ((ft_nullary b_true)) (s))) nil))
    ))
    (at level 200)
.

Definition argument_name
    (idx : nat)
    : string
:=
    "X_" +:+ (pretty idx)
.

Definition argument_sequence
    {Σ : StaticModel}
    (to_var : string -> variable)
    (arity : nat)
    : list variable
:=
    to_var <$> (argument_name <$> (seq 0 arity))
.

Definition NamedFlattenedRewritingRule
    {Σ : StaticModel}
    : Type
:=
    prod label FlattenedRewritingRule
.


Record State {Σ : StaticModel}
:= mkState {
    st_rules : gmap label FlattenedRewritingRule ;
    st_log : string ;
}.

Arguments mkState {Σ} st_rules st_log%string_scope.

Definition process_rule_declaration
    {Σ : StaticModel}
    (s : State)
    (r : RuleDeclaration)
    : State
:=
match (st_rules s) !! (rd_label r) with
| Some _
    => (mkState
        (st_rules s)
        ((st_log s) +:+ ("Rule with name '" +:+ (rd_label r) ++ "' already present"))%string)
| None
    => mkState
        (<[(rd_label r) := (rd_rule r)]>(st_rules s))
        (st_log s)
end
.

Section wsm.
(*
    Context
        {Σ : StaticModel}
        (to_var : string -> variable)
        (to_sym : string -> symbol)
    .
*)
    #[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).

    Definition to_var := fun x:string => x.
    Definition to_sym := fun x:string => x.
    
    Definition REST_SEQ : variable := to_var "$REST_SEQ".

    Definition cseq {defaults : Defaults} {T : Type}
    :=
        (@apply_symbol' Σ T (to_sym default_cseq_name))
    .

    Definition emptyCseq {defaults : Defaults} {T : Type}
    :=
        (@apply_symbol' Σ T (to_sym default_empty_cseq_name))
    .

    Definition freezer
        {T : Type}
        (sym : string)
        (position : nat)
    :=
        (@apply_symbol' Σ T (to_sym ("freezer_" +:+ sym +:+ "_" +:+ (pretty position))))
    .

    Check foldr.

    Definition heating_rule_seq
        {defaults : Defaults}
        (lbl : label)
        (freezerLbl : label)
        (sym : symbol)
        (arity : nat)
        (position : nat)
        (isValue : Expression -> Expression)
        (cseq_context : ContextTemplate)
        : RuleDeclaration
    :=
        let vars : list variable
            := argument_sequence to_var arity in
        let lhs_vars : list (AppliedOperatorOr' symbol BuiltinOrVar)
            := (aoo_operand <$> (bov_variable <$> vars)) in
        let rhs_vars : list (AppliedOperatorOr' symbol Expression)
            := (aoo_operand <$> (ft_variable <$> vars)) in
        let selected_var : variable
            := to_var (argument_name position) in
        let lhs_selected_var : (AppliedOperatorOr' symbol BuiltinOrVar)
            := aoo_operand (bov_variable selected_var) in
        let force_cseq_context
            := ((fun _:TagLHS => cseq_context _ _) mkTagLHS) in
        (* all operands on the left are already evaluated *)
        let side_condition : Expression
            := foldr (fun a b => (a && b)%rs) (true)%rs (isValue <$> (firstn (position) (ft_variable <$> vars) )) in
        rule [lbl]:
            cseq_context _ _ (cseq ([
                (apply_symbol' sym lhs_vars);
                (aoo_operand (bov_variable REST_SEQ))
            ])%list)
         ~> OpenTerm_to_ExprTerm ((force_cseq_context (cseq ([
                lhs_selected_var;
                cseq ([
                    (freezer freezerLbl position (delete position lhs_vars));
                    (aoo_operand (bov_variable REST_SEQ))
                ])%list
            ])%list)))
            where (( ~~ (isValue (ft_variable selected_var)) ) && side_condition )
    .


    Definition cooling_rule
        {defaults : Defaults}
        (lbl : label)
        (freezerLbl : label)
        (sym : symbol)
        (arity : nat)
        (position : nat)
        (isValue : Expression -> Expression)
        (cseq_context : ContextTemplate)
        : RuleDeclaration
    :=
        let vars : list variable
            := argument_sequence to_var arity in
        let lhs_vars : list (AppliedOperatorOr' symbol BuiltinOrVar)
            := (aoo_operand <$> (bov_variable <$> vars)) in
        let rhs_vars : list (AppliedOperatorOr' symbol Expression)
            := (aoo_operand <$> (ft_variable <$> vars)) in
        let selected_var : variable
            := to_var (argument_name position) in
        let lhs_selected_var : (AppliedOperatorOr' symbol BuiltinOrVar)
            := aoo_operand (bov_variable selected_var) in
        let force_cseq_context
            := ((fun _:TagLHS => cseq_context _ _) mkTagLHS) in
        rule [lbl]:
            cseq_context _ _ (cseq (
                ([
                lhs_selected_var;
                cseq ([
                    (freezer freezerLbl position (delete position lhs_vars));
                    (aoo_operand (bov_variable REST_SEQ))
                ])%list
            ])%list
           ))
         ~> OpenTerm_to_ExprTerm ((force_cseq_context (cseq [
                (apply_symbol' sym lhs_vars);
                (aoo_operand (bov_variable REST_SEQ))
            ])%list))
            where (isValue (ft_variable selected_var))
    .

    Definition process_context_declaration
        {defaults : Defaults}
        (s : State)
        (c : ContextDeclaration)
        : State
    := 
        let hr : RuleDeclaration
            := heating_rule_seq
                    ((cd_label c) +:+ "-heat")
                    (cd_label c)
                    (cd_sym c)
                    (cd_arity c)
                    (cd_position c)
                    (cd_isValue c)
                    (@cd_cseq_context Σ c)
            in
        let cr : RuleDeclaration
            := cooling_rule
                    ((cd_label c) +:+ "-cool")
                    (cd_label c)
                    (cd_sym c)
                    (cd_arity c)
                    (cd_position c)
                    (cd_isValue c)
                    (@cd_cseq_context Σ c)
            in
        
        process_rule_declaration
            (process_rule_declaration s hr)
            cr
    .

    Definition process_strictness_declaration
        {defaults : Defaults}
        (s : State)
        (c : StrictnessDeclaration)
        : State
    :=
        foldr
            (fun a b => process_context_declaration b a)
            s
            (strictness_to_contexts id id id c)
    .

    Definition initialState
        {Σ : StaticModel}
        : State
    := {|
        st_rules := ∅ ;
        st_log := "";
    |}.



    Definition process_declaration
        {defaults : Defaults}
        (s : State)
        (d : Declaration)
        : State
    :=
    match d with
    | decl_rule rd => process_rule_declaration s rd
    | decl_ctx cd => process_context_declaration s cd
    | decl_strict sd => process_strictness_declaration s sd
    end.

    Definition process_declarations
        {defaults : Defaults}
        (ld : list Declaration)
        : State
    :=
        fold_left process_declaration ld initialState
    .

    Definition to_theory
        {Σ : StaticModel}
        (s : State)
        : FlattenedRewritingTheory*(list string)
    :=
        let l := (map_to_list (st_rules s)) in
        (l.*2,l.*1)
    .

End wsm.



