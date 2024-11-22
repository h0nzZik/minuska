From Minuska Require Import
    prelude
    spec
    notations
    default_static_model
    builtins
.


(* Import default_builtin.
Export default_builtin.Notations. *)

Arguments e_fun {Σ} f l%_list_scope.

Definition SymbolicTerm_to_ExprTerm
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    : TermOver Expression2
:=
    TermOver_map (fun x:BuiltinOrVar =>
        match x with
        | bov_builtin b => e_ground (t_over b)
        | bov_variable x => e_variable x
        end ) t
.

Definition label {Σ : StaticModel} :=
    string
.


Definition ContextTemplate
    {Σ : StaticModel}
:=
    forall (br:BasicResolver) (r:Resolver),
    TermOver operand_type ->
    TermOver operand_type
.


Notation
    "( 'context-template' x 'with' h )"
    :=
    (fun (_:BasicResolver) (_:Resolver) (h : TermOver operand_type) => x)
.



Record ContextDeclaration {Σ : StaticModel}
:= mkContextDeclaration {
    cd_label : label ;
    cd_sym : symbol ;
    cd_arity : nat ;
    cd_position : nat ;
    cd_positions_to_wait_for : list nat ;
    cd_isValue : Expression2 -> SideCondition2 ;
    cd_isNonValue : Expression2 -> SideCondition2 ;
    cd_cseq_context : ContextTemplate;
}.

Record StrictnessDeclaration {Σ : StaticModel}
:= mkStrictnessDeclaration {
    sd_sym : symbol ;
    sd_arity : nat ;
    sd_positions : list nat ;
    sd_isValue : Expression2 -> SideCondition2 ;
    sd_isNonValue : Expression2 -> SideCondition2 ;
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
    default_isValue : Expression2 -> Expression2 ;
    default_isNonValue : Expression2 -> Expression2 ;
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
Check imap.
Definition strictness_to_contexts
    {Σ : StaticModel}
    (sym_to_str : symbol -> string)
    (str_to_sym : string -> symbol)
    (str_to_label : string -> label)
    (sd : StrictnessDeclaration)
    : list ContextDeclaration
:=
    imap (fun idx position => {|
            cd_label := (str_to_label (sym_to_str (sd_sym sd) +:+ ("-" +:+ (pretty position)))) ;
            cd_sym := sd_sym sd ;
            cd_arity := sd_arity sd ;
            cd_position := position ;
            cd_positions_to_wait_for := (firstn idx (sd_positions sd));
            cd_isValue := sd_isValue sd ;
            cd_isNonValue := sd_isNonValue sd ;
            cd_cseq_context := @sd_cseq_context Σ sd ;
        |})
        (sd_positions sd)
.

Record RuleDeclaration {Σ : StaticModel} (Act : Set)
:= mkRuleDeclaration {
    rd_label : label ;
    rd_rule : RewritingRule2 Act ;
}.

Arguments mkRuleDeclaration {Σ} {Act} rd_label rd_rule.
Arguments rd_label {Σ} {Act}%_type_scope r.
Arguments rd_rule {Σ} {Act}%_type_scope r.

Inductive Declaration {Σ : StaticModel} {Act : Set} :=
| decl_rule (r : @RuleDeclaration Σ Act)
| decl_ctx (c : ContextDeclaration)
| decl_strict (s : StrictnessDeclaration)
.

(*Coercion decl_rule : RuleDeclaration >-> Declaration.*)

Notation "'rule' '[' n ']:' l '~>{' a '}' r"
    := ((mkRuleDeclaration
        n (rule (l) ~>{ (a) } (r) requires nil)
    ))
    (at level 200)
.

Notation "'rule' '[' n ']:' l '~>{' a '}' r 'where' s"
    := ((mkRuleDeclaration
        n (rule (l) ~>{a} (r) requires s)
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

Record State {Σ : StaticModel} {Act : Set}
:= mkState {
    st_rules : gmap label (RewritingRule2 Act) ;
    st_log : string ;
}.

Arguments mkState {Σ} {Act} st_rules st_log%_string_scope.

Definition process_rule_declaration
    {Σ : StaticModel}
    {Act : Set}
    (s : State)
    (r : RuleDeclaration Act)
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
    Context
        (Act : Set)
        (default_act : Act)
    .
    Context
        (β : Builtin MyUnit)
    .

    #[local]
    Instance Σ : StaticModel := default_model β.

    Definition to_var := fun x:string => x.
    Definition to_sym := fun x:string => x.
    
    Definition REST_SEQ : variable := to_var "$REST_SEQ".

    Definition cseq {defaults : Defaults} {T : Type}
    :=
        @t_term _ T (to_sym default_cseq_name)
    .

    Definition emptyCseq {defaults : Defaults} {T : Type}
    :=
        @t_term _ T (to_sym default_empty_cseq_name)
    .

    Definition freezer
        {T : Type}
        (sym : string)
        (position : nat)
    :=
        @t_term _ T (to_sym ("freezer_" +:+ sym +:+ "_" +:+ (pretty position)))
    .

    Definition heating_rule_seq
        {defaults : Defaults}
        (lbl : label)
        (freezerLbl : label)
        (sym : symbol)
        (arity : nat)
        (positions_to_wait_for : list nat)
        (position : nat)
        (isValue : Expression2 -> SideCondition2)
        (isNonValue : Expression2 -> SideCondition2)
        (cseq_context : ContextTemplate)
        : RuleDeclaration Act
    :=
        let vars : list variable
            := argument_sequence to_var arity in
        let lhs_vars : list (TermOver BuiltinOrVar)
            := (t_over <$> (bov_variable <$> vars)) in
        let rhs_vars : list (TermOver Expression2)
            := (t_over <$> (e_variable <$> vars)) in
        let selected_var : variable
            := to_var (argument_name position) in
        let lhs_selected_var : (TermOver BuiltinOrVar)
            := t_over (bov_variable selected_var) in
        let force_cseq_context
            := ((fun _:TagLHS => cseq_context _ _) mkTagLHS) in
        (* all operands on the left are already evaluated *)
        let side_condition : list SideCondition2
            := (isValue <$> ((e_variable <$> (to_var <$> (argument_name <$> positions_to_wait_for))) )) in
        rule [lbl]:
            cseq_context _ _ (cseq ([
                (t_term sym lhs_vars);
                (t_over (bov_variable REST_SEQ))
            ])%list)
         ~>{default_act} SymbolicTerm_to_ExprTerm ((force_cseq_context (cseq ([
                lhs_selected_var;
                cseq ([
                    (freezer freezerLbl position (delete position lhs_vars));
                    (t_over (bov_variable REST_SEQ))
                ])%list
            ])%list)))
            where ([(isNonValue (e_variable selected_var))] ++ side_condition)
    .


    Definition cooling_rule
        {defaults : Defaults}
        (lbl : label)
        (freezerLbl : label)
        (sym : symbol)
        (arity : nat)
        (position : nat)
        (isValue : Expression2 -> SideCondition2)
        (cseq_context : ContextTemplate)
        : RuleDeclaration Act
    :=
        let vars : list variable
            := argument_sequence to_var arity in
        let lhs_vars : list (TermOver BuiltinOrVar)
            := (t_over <$> (bov_variable <$> vars)) in
        let rhs_vars : list (TermOver Expression2)
            := (t_over <$> (e_variable <$> vars)) in
        let selected_var : variable
            := to_var (argument_name position) in
        let lhs_selected_var : (TermOver BuiltinOrVar)
            := t_over (bov_variable selected_var) in
        let force_cseq_context
            := ((fun _:TagLHS => cseq_context _ _) mkTagLHS) in
        rule [lbl]:
            cseq_context _ _ (cseq (
                ([
                lhs_selected_var;
                cseq ([
                    (freezer freezerLbl position (delete position lhs_vars));
                    (t_over (bov_variable REST_SEQ))
                ])%list
            ])%list
           ))
         ~>{default_act} SymbolicTerm_to_ExprTerm ((force_cseq_context (cseq [
                (t_term sym lhs_vars);
                (t_over (bov_variable REST_SEQ))
            ])%list))
            where [(isValue (e_variable selected_var))]
    .

    Definition process_context_declaration
        {defaults : Defaults}
        (s : State)
        (c : ContextDeclaration)
        : State
    := 
        let hr : RuleDeclaration Act
            := heating_rule_seq
                    ((cd_label c) +:+ "-heat")
                    (cd_label c)
                    (cd_sym c)
                    (cd_arity c)
                    (cd_positions_to_wait_for c)
                    (cd_position c)
                    (cd_isValue c)
                    (cd_isNonValue c)
                    (@cd_cseq_context Σ c)
            in
        let cr : RuleDeclaration Act
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
        : @State Σ Act
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
        : (list (RewritingRule2 Act))*(list string)
    :=
        let l := (map_to_list (st_rules s)) in
        (l.*2,l.*1)
    .

End wsm.



