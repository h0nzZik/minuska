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
| se_variable
    (x : string)
| se_applyf
    (s : string)
    (l : list StringExpression)
| se_applyq
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
    {Σ : StaticModel}
    {A : Type}
    (f : BuiltinRepr -> option builtin_value)
    (t : @TermOver' A BuiltinRepr)
    :
    (@TermOver' A builtin_value)+string
:=
    TermOver'_e_map (fun (x:BuiltinRepr) => match f x with Some y => inl y | None =>
    inr ("Can't convert (" +:+ x.(br_kind) +:+ ", " +:+ x.(br_value) +:+ ") to builtin")
    end) t
.

Class Realization {Σ : StaticModel} := {
    realize_br : BuiltinRepr -> option builtin_value ;
    string2sym : string -> symbol ;
    string2var : string -> variable ;
    string2q : string -> option QuerySymbol ;
    string2f : string -> option builtin_function_symbol ;
    string2p : string -> option builtin_predicate_symbol;
}.

Fixpoint se_to_Expression
    {Σ : StaticModel}
    {R : Realization}
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
    | se_variable x =>
        inl (e_variable (string2var x))
    | se_applyf s l =>
        match (string2f s) with
        | None => inr ("Can't convert " +:+ s +:+ " to function symbol")
        | Some (f) => 
            let l' := (se_to_Expression) <$> l in
            match list_collect_e l' with
            | inl l'' => inl (e_fun f l'')
            | inr e => inr e
            end
        end
    | se_applyq s l =>
        match (string2q s) with
        | None => inr ("Can't convert " +:+ s +:+ " to query symbol")
        | Some (q) => 
            let l' := (se_to_Expression) <$> l in
            match list_collect_e l' with
            | inl l'' => inl (e_query q l'')
            | inr e => inr e
            end
        end

    end
.


Inductive StringSideCondition
:=
| ssc_true
| ssc_false
| ssc_atom
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
    {Σ : StaticModel}
    {R : Realization}
    (ssc : StringSideCondition)
    :
    SideCondition+string
:=
    match ssc with
    | ssc_true => inl sc_true
    | ssc_false => inl sc_false
    | ssc_atom p args =>
        match string2p p with
        | Some p' =>
            match list_collect_e ((se_to_Expression) <$> args) with
            | inl args' => inl (sc_atom p' args')
            | inr e => inr e
            end
        | None => inr ("Can't convert string '" +:+ p +:+ "' to predicate symbol")
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
    {Σ : StaticModel}
    {R : Realization}
    (t : @TermOver' string StringExpression)
    :
    (TermOver Expression2)+string
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
    {Σ : StaticModel}
    {R : Realization}
    (sbov : StringBuiltinOrVar)
    :
    BuiltinOrVar+string
:=
    match sbov with
    | sbov_var x => inl (bov_variable (string2var x))
    | sbov_builtin b =>
        match (realize_br b) with
        | Some b' => inl (bov_builtin b')
        | None => inr ("Can't convert (" +:+ b.(br_kind) +:+ ", " +:+ b.(br_value) +:+ ") to builtin")
        end
    end
.

Record StringRewritingRule
    (Act : Set)
:= mkStringRewritingRule
{
    sr_from : @TermOver' string StringBuiltinOrVar ;
    sr_to : @TermOver' string StringExpression ;
    sr_scs : StringSideCondition ;
    sr_act : Act ;
}.

Definition transl_string_pattern
    {Σ : StaticModel}
    (Act : Set)
    {R : Realization}
    (p : @TermOver' string StringBuiltinOrVar)
    :
    (TermOver BuiltinOrVar)+string
:=
    match TermOver'_e_map (sbov_to_e_bov) p with
    | inr e => inr e
    | inl p'' => inl (to_transform_sym string2sym p'')
    end
.

Definition srr_to_rr
    {Σ : StaticModel}
    (Act : Set)
    {R : Realization}
    (srr : StringRewritingRule Act)
    :
    (RewritingRule2 Act)+string
:=
    match srr with
    | mkStringRewritingRule _ from to scs act =>
        match transl_string_pattern Act from with
        | inl from' =>
            match tosse_to_e_tose to with
            | inl to' =>
                match ssc_to_sc scs with
                | inl scs' =>
                    inl {|
                        r_from := from';
                        r_to := to';
                        r_scs := scs';
                        r_act := act;
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
    {Σ : StaticModel}
    (Act : Set)
    {R : Realization}
    (srrl : list (StringRewritingRule Act))
    :
    (list (RewritingRule2 Act))+string
:=
    list_collect_e (map (srr_to_rr Act) srrl)
.

Definition sSymbolicTerm_to_ExprTerm
    (t : @TermOver' string StringBuiltinOrVar)
    : @TermOver' string StringExpression
:=
    TermOver'_map (fun x:StringBuiltinOrVar =>
        match x with
        | sbov_builtin b => se_ground (t_over b)
        | sbov_var x => se_variable x
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

Record RuleDeclaration (Act : Set)
:= mkRuleDeclaration {
    rd_label : string ;
    rd_rule : StringRewritingRule Act ;
}.

Inductive Declaration (Act : Set) :=
| decl_rule (r : RuleDeclaration Act)
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

Record State (Act : Set)
:= mkState {
    st_rules : (gmap string (StringRewritingRule Act)) ;
}.

Definition process_rule_declaration
    {Act : Set}
    (s : State Act)
    (r : RuleDeclaration Act)
    : (State Act)+string
:=
match (st_rules _ s) !! (rd_label _ r) with
| Some _
    => inr
        ("Rule with name '" +:+ (rd_label _ r) ++ "' already present")%string
| None
    => inl (mkState Act
        (<[(rd_label _ r) := (rd_rule _ r)]>(st_rules _ s))
    )
end
.

Fixpoint try_neg_s
    (sbps_ar : string -> nat)
    (sbps_neg : string -> option string)
    (sc : StringSideCondition)
    : option StringSideCondition
:= 
    match sc with
    | ssc_true => Some ssc_false
    | ssc_false => Some ssc_true
    | ssc_and sc1 sc2 =>
        sc1' ← try_neg_s sbps_ar sbps_neg sc1;
        sc2' ← try_neg_s sbps_ar sbps_neg sc2;
        Some (ssc_or sc1' sc2')
    | ssc_or sc1 sc2 =>
        sc1' ← try_neg_s sbps_ar sbps_neg sc1;
        sc2' ← try_neg_s sbps_ar sbps_neg sc2;
        Some (ssc_and sc1' sc2')
    | ssc_atom p l =>
        if decide (length l = sbps_ar p) then 
            p' ← sbps_neg p;
            Some (ssc_atom p' l)
        else None
    end
.


Section wsm.
    Context
        (Act : Set)
        (default_act : Act)
    .
    Context
        (* (signature : Signature) *)
        (* (β : Model signature MyUnit) *)
        (* (my_program_info : ProgramInfo) *)
        (sbps_ar : string -> nat)
        (sbps_neg : string -> option string)
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
        : (RuleDeclaration Act)+string
    :=
        let vars : list string
            := argument_sequence arity in
        let lhs_vars : list (@TermOver' string StringBuiltinOrVar)
            := (map t_over (map sbov_var vars)) in
        let rhs_vars : list (@TermOver' string StringExpression)
            := (map t_over (map se_variable vars)) in
        let selected_var : string
            := (argument_name position) in
        match try_neg_s sbps_ar sbps_neg (isValue (se_variable selected_var)) with
        | None => inr "Cannot negate given isValue condition"
        | Some is_value_neg => inl (
            let lhs_selected_var : (@TermOver' string StringBuiltinOrVar)
                := t_over (sbov_var selected_var) in
            (* all operands on the left are already evaluated *)
            let side_condition : StringSideCondition
                := foldr  ssc_and (ssc_true) (isValue <$> ((se_variable <$> ((argument_name <$> positions_to_wait_for))) )) in
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
                sr_act := default_act ;
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
        : RuleDeclaration Act
    :=
        let vars : list string
            := argument_sequence arity in
        let lhs_vars : list (@TermOver' string StringBuiltinOrVar)
            := (map t_over (map sbov_var vars)) in
        let rhs_vars : list (@TermOver' string StringExpression)
            := (map t_over (map se_variable vars)) in
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
            sr_act := default_act;
            sr_scs := (isValue (se_variable selected_var));
        |})
    .

    Definition process_context_declaration
        {defaults : Defaults}
        (s : State Act)
        (c : ContextDeclaration)
        : (State Act)+string
    := 
        let hr' : (RuleDeclaration Act)+string
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
            let cr : RuleDeclaration Act
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
        (s : State Act)
        (c : StrictnessDeclaration)
        : (State Act)+string
    :=
        foldr
            (fun a b' => match b' with inr s => inr s | inl b => process_context_declaration b a end)
            (inl s)
            (strictness_to_contexts c)
    .

    Definition initialState
        : State Act
    := {|
        st_rules := ∅ ;
    |}.



    Definition process_declaration
        {defaults : Defaults}
        (s : State Act)
        (d : Declaration Act)
        : (State Act)+string
    :=
    match d with
    | decl_rule _ rd => process_rule_declaration s rd
    | decl_ctx _ cd => process_context_declaration s cd
    | decl_strict _ sd => process_strictness_declaration s sd
    end.

    Definition process_declarations
        {defaults : Defaults}
        (ld : list (Declaration Act))
        : (State Act)+string
    :=
        fold_left (fun s' d => match s' with inl s => process_declaration s d | inr s => inr s end) ld (inl initialState)
    .

    Definition to_theory
        (s : State Act)
        : (list (StringRewritingRule Act))*(list string)
    :=
        let l := (map_to_list (st_rules _ s)) in
        (l.*2,l.*1)
    .

End wsm.
