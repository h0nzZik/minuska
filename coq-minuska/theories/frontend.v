From Minuska Require Import
    prelude
    spec
    notations
    default_static_model
    builtins
    properties
.

Arguments e_fun {Σ} f l%_list_scope.

Definition SymbolicTerm_to_ExprTerm
    {Σ : BackgroundModel}
    (t : @TermOver' TermSymbol BuiltinOrVar)
    : @TermOver' TermSymbol Expression2
:=
    TermOver_map (fun x:BuiltinOrVar =>
        match x with
        | bov_builtin b => e_ground (t_over b)
        | bov_Variabl x => e_Variabl x
        end ) t
.



Fixpoint to_transform_sym
    {A A' B : Type}
    (f : A -> A')
    (t : @TermOver' A B)
    :
    @TermOver' A' B
:=
    match t with
    | t_over o => t_over o
    | t_term s l => t_term (f s) ((to_transform_sym f) <$>l)
    end
.

Record BuiltinRepr := {
    br_kind : string ;
    br_value : string ;
}.

Inductive StringExpression
:=
| se_ground
    (g : @TermOver' string BuiltinRepr)
| se_Variabl
    (x : string)
| se_apply
    (s : string)
    (l : list StringExpression)
.

Definition list_collect_e
    {A : Type}
    (l : list (A+string))
    : (list A)+string
:=
    foldr (fun ox ol => match ox, ol with inl x, inl l' => inl (x::l') | inl x, inr e => inr e | inr e, inl _ => inr e | inr e1, inr e2 => inr (e1 +:+ e2) end) (inl []) l
.

Fixpoint TermOver'_e_map
    {T : Type} {A B : Type}
    (f : A -> B+string)
    (t : @TermOver' T A)
    : (@TermOver' T B)+string
:=
    match t with
    | t_over b =>
        match f b with
        | inl b' => inl (t_over b')
        | inr e => inr e
        end
    | t_term s l =>
        match (list_collect_e ((TermOver'_e_map f) <$> l)) with
        | inl l' => inl (t_term s l')
        | inr e => inr e
        end
    end
.

(* TODO use an error monad *)
Definition toss_to_e_tosb
    {Σ : BackgroundModel}
    {A : Type}
    (f : BuiltinRepr -> option BasicValue)
    (t : @TermOver' A BuiltinRepr)
    :
    (@TermOver' A BasicValue)+string
:=
    TermOver'_e_map (fun (x:BuiltinRepr) => match f x with Some y => inl y | None =>
    inr ("Can't convert (" +:+ x.(br_kind) +:+ ", " +:+ x.(br_value) +:+ ") to builtin")
    end) t
.

Class Realization (Bu Sy Va P HP F A Q M : Type) := {
    realize_br : BuiltinRepr -> option Bu ;
    string2sym : string -> Sy ;
    string2var : string -> Va ;
    string2m : string -> option M ;
    string2qfa : string -> option (Q+F+A) ;
    string2p : string -> option (P+HP)
}.

Fixpoint se_to_Expression
    {Σ : BackgroundModel}
    {R : Realization BasicValue TermSymbol Variabl PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol}
    (se : StringExpression)
    :
    Expression2+string
:=
    match se with
    | se_ground g =>
        match toss_to_e_tosb realize_br g with
        | inl g' => inl (e_ground (to_transform_sym string2sym g'))
        | inr e => inr e
        end
    | se_Variabl x =>
        inl (e_Variabl (string2var x))
    | se_apply s l =>
        match (string2qfa s) with
        | None => inr ("The string " +:+ s +:+ " does not represent a function or a query")
        | Some (s') => 
            let l' := (se_to_Expression) <$> l in
            match list_collect_e l' with
            | inl l'' => 
                match s' with
                | inl (inl q) => inl (e_query q l'')
                | inl (inr f) => inl (e_fun f l'')
                | inr a => inl (e_attr a l'')
                end
            | inr e => inr e
            end
        end
    end
.


Inductive StringSideCondition
:=
| ssc_true
| ssc_false
| ssc_pred
    (pred : string)
    (args : list (StringExpression))
| ssc_npred
    (pred : string)
    (args : list (StringExpression))
| ssc_and
    (left : (StringSideCondition))
    (right : (StringSideCondition))
| ssc_or
    (left : (StringSideCondition))
    (right : (StringSideCondition))
.

Fixpoint ssc_to_sc
    {Σ : BackgroundModel}
    {R : Realization BasicValue TermSymbol Variabl PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol}
    (ssc : StringSideCondition)
    :
    SideCondition+string
:=
    match ssc with
    | ssc_true => inl sc_true
    | ssc_false => inl sc_false
    | ssc_pred p args =>
        match string2p p with
        | Some p' =>
            match list_collect_e ((se_to_Expression) <$> args) with
            | inl args' => 
                match p' with
                | inl vp => inl (sc_pred vp args')
                | inr hp => inl (sc_hpred hp args')
                end
            | inr e => inr e
            end
        | None => inr ("Can't convert string '" +:+ p +:+ "' to predicate (or hidden predicate) TermSymbol")
        end
    | ssc_npred p args =>
        match string2p p with
        | Some p' =>
            match list_collect_e ((se_to_Expression) <$> args) with
            | inl args' => 
                match p' with
                | inl vp => inl (sc_npred vp args')
                | inr hp => inr ("The hidden predicate TermSymbol '" +:+ p +:+ "' can't be negated")
                end
            | inr e => inr e
            end
        | None => inr ("Can't convert string '" +:+ p +:+ "' to predicate (or hidden predicate) TermSymbol")
        end
    | ssc_and l r =>
        match ssc_to_sc l with
        | inl left' =>
            match ssc_to_sc r with
            | inl right' => inl (sc_and left' right')
            | inr e => inr e
            end
        | inr e => inr e
        end
    | ssc_or l r =>
        match ssc_to_sc l with
        | inl left' =>
            match ssc_to_sc r with
            | inl right' => inl (sc_or left' right')
            | inr e => inr e
            end
        | inr e => inr e
        end
    end
.

Definition tosse_to_e_tose
    {Σ : BackgroundModel}
    {R : Realization BasicValue TermSymbol Variabl PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol}
    (t : @TermOver' string StringExpression)
    :
    (@TermOver' TermSymbol Expression2)+string
:=
    match TermOver'_e_map (se_to_Expression) t with
    | inl t' => let t'' := to_transform_sym string2sym t' in
        inl t''
    | inr e => inr e
    end
.

Variant StringBuiltinOrVar :=
| sbov_builtin (b : BuiltinRepr)
| sbov_var (x : string)
.

Definition sbov_to_e_bov
    {Σ : BackgroundModel}
    {R : Realization BasicValue TermSymbol Variabl PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol}
    (sbov : StringBuiltinOrVar)
    :
    BuiltinOrVar+string
:=
    match sbov with
    | sbov_var x => inl (bov_Variabl (string2var x))
    | sbov_builtin b =>
        match (realize_br b) with
        | Some b' => inl (bov_builtin b')
        | None => inr ("Can't convert (" +:+ b.(br_kind) +:+ ", " +:+ b.(br_value) +:+ ") to builtin")
        end
    end
.

Record StringRewritingRule
    (Label : Set)
:= mkStringRewritingRule
{
    sr_from : @TermOver' string StringBuiltinOrVar ;
    sr_to : @TermOver' string StringExpression ;
    sr_scs : StringSideCondition ;
    sr_label : Label ;
}.

Definition transl_string_pattern
    {Σ : BackgroundModel}
    (Label : Set)
    {R : Realization BasicValue TermSymbol Variabl PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol}
    (p : @TermOver' string StringBuiltinOrVar)
    :
    (@TermOver' TermSymbol BuiltinOrVar)+string
:=
    match TermOver'_e_map (sbov_to_e_bov) p with
    | inr e => inr e
    | inl p'' => inl (to_transform_sym string2sym p'')
    end
.

Definition srr_to_rr
    {Σ : BackgroundModel}
    (Label : Set)
    {R : Realization BasicValue TermSymbol Variabl PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol}
    (srr : StringRewritingRule Label)
    :
    (RewritingRule2 Label)+string
:=
    match srr with
    | mkStringRewritingRule _ from to scs act =>
        match transl_string_pattern Label from with
        | inl from' =>
            match tosse_to_e_tose to with
            | inl to' =>
                match ssc_to_sc scs with
                | inl scs' =>
                    inl {|
                        r_from := from';
                        r_to := to';
                        r_scs := scs';
                        (* TODO we do not support effects in the frontend yet *)
                        r_eff := [];
                        r_label := act;
                    |}
                | inr e => inr e
                end
            | inr e => inr e
            end
        | inr e => inr e
        end
    end
.

Definition realize_thy
    {Σ : BackgroundModel}
    (Label : Set)
    {R : Realization BasicValue TermSymbol Variabl PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol}
    (srrl : list (StringRewritingRule Label))
    :
    (list (RewritingRule2 Label))+string
:=
    list_collect_e (map (srr_to_rr Label) srrl)
.

Definition sSymbolicTerm_to_ExprTerm
    (t : @TermOver' string StringBuiltinOrVar)
    : @TermOver' string StringExpression
:=
    TermOver'_map (fun x:StringBuiltinOrVar =>
        match x with
        | sbov_builtin b => se_ground (t_over b)
        | sbov_var x => se_Variabl x
        end ) t
.


Definition ContextTemplate := @TermOver' string StringBuiltinOrVar -> @TermOver' string StringBuiltinOrVar.

Record ContextDeclaration
:= mkContextDeclaration {
    cd_label : string ;
    cd_sym : string ;
    cd_arity : nat ;
    cd_position : nat ;
    cd_positions_to_wait_for : list nat ;
    cd_isValue : StringExpression -> StringSideCondition ;
    cd_cseq_context : ContextTemplate;
}.

Record StrictnessDeclaration
:= mkStrictnessDeclaration {
    sd_sym : string ;
    sd_arity : nat ;
    sd_positions : list nat ;
    sd_isValue : StringExpression -> StringSideCondition ;
    sd_cseq_context : ContextTemplate ;
}.

Class Defaults := mkDefaults {
    default_cseq_name : string ;
    default_empty_cseq_name : string ;
    default_context_template : ContextTemplate ;
    default_isValue : StringExpression -> StringSideCondition ;
}.

Definition strictness_to_contexts
    (sd : StrictnessDeclaration)
    : list ContextDeclaration
:=
    imap (fun idx position => {|
            cd_label := (((sd_sym sd) +:+ ("-" +:+ (pretty position)))) ;
            cd_sym := sd_sym sd ;
            cd_arity := sd_arity sd ;
            cd_position := position ;
            cd_positions_to_wait_for := (firstn idx (sd_positions sd));
            cd_isValue := sd_isValue sd ;
            cd_cseq_context := sd_cseq_context sd ;
        |})
        (sd_positions sd)
.

Record RuleDeclaration (Label : Set)
:= mkRuleDeclaration {
    rd_label : string ;
    rd_rule : StringRewritingRule Label ;
}.

Inductive Declaration (Label : Set) :=
| decl_rule (r : RuleDeclaration Label)
| decl_ctx (c : ContextDeclaration)
| decl_strict (s : StrictnessDeclaration)
.

Definition argument_name
    (idx : nat)
    : string
:=
    "X_" +:+ (pretty idx)
.

Definition argument_sequence
    (arity : nat)
    : list string
:=
    (argument_name <$> (seq 0 arity))
.

Record State (Label : Set)
:= mkState {
    st_rules : (gmap string (StringRewritingRule Label)) ;
}.

Definition process_rule_declaration
    {Label : Set}
    (s : State Label)
    (r : RuleDeclaration Label)
    : (State Label)+string
:=
match (st_rules _ s) !! (rd_label _ r) with
| Some _
    => inr
        ("Rule with name '" +:+ (rd_label _ r) ++ "' already present")%string
| None
    => inl (mkState Label
        (<[(rd_label _ r) := (rd_rule _ r)]>(st_rules _ s))
    )
end
.

Fixpoint try_neg_s
    (sc : StringSideCondition)
    : option StringSideCondition
:= 
    match sc with
    | ssc_true => Some ssc_false
    | ssc_false => Some ssc_true
    | ssc_and sc1 sc2 =>
        sc1' ← try_neg_s  sc1;
        sc2' ← try_neg_s  sc2;
        Some (ssc_or sc1' sc2')
    | ssc_or sc1 sc2 =>
        sc1' ← try_neg_s  sc1;
        sc2' ← try_neg_s  sc2;
        Some (ssc_and sc1' sc2')
    | ssc_pred p l => Some (ssc_npred p l)
    | ssc_npred p l => Some (ssc_pred p l)
    end
.


Section wsm.
    Context
        (Label : Set)
        (default_label : Label)
    .
    Definition REST_SEQ : string := "$REST_SEQ".

    Definition cseq {defaults : Defaults} {T : Type}
    :=
        @t_term _ T (default_cseq_name)
    .

    Definition emptyCseq {defaults : Defaults} {T : Type}
    :=
        @t_term _ T (default_empty_cseq_name)
    .

    Definition freezer
        {T : Type}
        (sym : string)
        (position : nat)
    :=
        @t_term _ T (("freezer_" +:+ sym +:+ "_" +:+ (pretty position)))
    .

    Definition heating_rule_seq
        {defaults : Defaults}
        (lbl : string)
        (freezerLbl : string)
        (sym : string)
        (arity : nat)
        (positions_to_wait_for : list nat)
        (position : nat)
        (isValue : StringExpression -> StringSideCondition)
        (cseq_context : ContextTemplate)
        : (RuleDeclaration Label)+string
    :=
        let vars : list string
            := argument_sequence arity in
        let lhs_vars : list (@TermOver' string StringBuiltinOrVar)
            := (map t_over (map sbov_var vars)) in
        let rhs_vars : list (@TermOver' string StringExpression)
            := (map t_over (map se_Variabl vars)) in
        let selected_var : string
            := (argument_name position) in
        match try_neg_s (isValue (se_Variabl selected_var)) with
        | None => inr "Cannot negate given isValue condition"
        | Some is_value_neg => inl (
            let lhs_selected_var : (@TermOver' string StringBuiltinOrVar)
                := t_over (sbov_var selected_var) in
            (* all operands on the left are already evaluated *)
            let side_condition : StringSideCondition
                := foldr  ssc_and (ssc_true) (isValue <$> ((se_Variabl <$> ((argument_name <$> positions_to_wait_for))) )) in
            (mkRuleDeclaration _ lbl {|
                sr_from := (cseq_context (cseq ([
                    (t_term sym lhs_vars);
                    (t_over (sbov_var REST_SEQ))
                ])%list));
                sr_to := (sSymbolicTerm_to_ExprTerm (cseq_context (cseq ([
                    lhs_selected_var;
                    cseq ([
                        (freezer freezerLbl position (delete position lhs_vars));
                        (t_over (sbov_var REST_SEQ))
                    ])%list
                ]))));
                sr_scs := (ssc_and (is_value_neg) side_condition) ;
                sr_label := default_label ;
            |})
            )
        end
    .


    Definition cooling_rule
        {defaults : Defaults}
        (lbl : string)
        (freezerLbl : string)
        (sym : string)
        (arity : nat)
        (position : nat)
        (isValue : StringExpression -> StringSideCondition)
        (cseq_context : ContextTemplate)
        : RuleDeclaration Label
    :=
        let vars : list string
            := argument_sequence arity in
        let lhs_vars : list (@TermOver' string StringBuiltinOrVar)
            := (map t_over (map sbov_var vars)) in
        let rhs_vars : list (@TermOver' string StringExpression)
            := (map t_over (map se_Variabl vars)) in
        let selected_var : string
            := (argument_name position) in
        let lhs_selected_var : (@TermOver' string StringBuiltinOrVar)
            := t_over (sbov_var selected_var) in
        (mkRuleDeclaration _ lbl {|
            sr_from := (cseq_context (cseq (
                ([
                lhs_selected_var;
                cseq ([
                    (freezer freezerLbl position (delete position lhs_vars));
                    (t_over (sbov_var REST_SEQ))
                ])%list
            ])%list
           )));
            sr_to := (sSymbolicTerm_to_ExprTerm (cseq_context ((cseq [
                (t_term sym lhs_vars);
                (t_over (sbov_var REST_SEQ))
            ])%list)));
            sr_label := default_label;
            sr_scs := (isValue (se_Variabl selected_var));
        |})
    .

    Definition process_context_declaration
        {defaults : Defaults}
        (s : State Label)
        (c : ContextDeclaration)
        : (State Label)+string
    := 
        let hr' : (RuleDeclaration Label)+string
            := heating_rule_seq
                    ((cd_label c) +:+ "-heat")
                    (cd_label c)
                    (cd_sym c)
                    (cd_arity c)
                    (cd_positions_to_wait_for c)
                    (cd_position c)
                    (cd_isValue c)
                    (cd_cseq_context c)
            in
        match hr' with
        | inl hr => (
            let cr : RuleDeclaration Label
                := cooling_rule
                        ((cd_label c) +:+ "-cool")
                        (cd_label c)
                        (cd_sym c)
                        (cd_arity c)
                        (cd_position c)
                        (cd_isValue c)
                        (cd_cseq_context c)
                in
            
            match (process_rule_declaration s hr) with
            | inl s' =>
                process_rule_declaration
                    s'
                    cr
            | inr err_s =>
                inr ("Cannot process declaration: " +:+ err_s)
            end
        )
        | (inr err_s) =>
            inr ("Invalid 'context' declaration: " +:+ err_s)
        end
    .

    Definition process_strictness_declaration
        {defaults : Defaults}
        (s : State Label)
        (c : StrictnessDeclaration)
        : (State Label)+string
    :=
        foldr
            (fun a b' => match b' with inr s => inr s | inl b => process_context_declaration b a end)
            (inl s)
            (strictness_to_contexts c)
    .

    Definition initialState
        : State Label
    := {|
        st_rules := ∅ ;
    |}.



    Definition process_declaration
        {defaults : Defaults}
        (s : State Label)
        (d : Declaration Label)
        : (State Label)+string
    :=
    match d with
    | decl_rule _ rd => process_rule_declaration s rd
    | decl_ctx _ cd => process_context_declaration s cd
    | decl_strict _ sd => process_strictness_declaration s sd
    end.

    Definition process_declarations
        {defaults : Defaults}
        (ld : list (Declaration Label))
        : (State Label)+string
    :=
        fold_left (fun s' d => match s' with inl s => process_declaration s d | inr s => inr s end) ld (inl initialState)
    .

    Definition to_theory
        (s : State Label)
        : (list (StringRewritingRule Label))*(list string)
    :=
        let l := (map_to_list (st_rules _ s)) in
        (l.*2,l.*1)
    .

End wsm.
