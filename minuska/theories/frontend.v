From Minuska Require Import
    prelude
    spec_syntax
    flattened
    notations
    builtins
.


Import default_builtin.
Export default_builtin.Notations.

Definition label {Σ : StaticModel} :=
    string
.

Record ContextDeclaration {Σ : StaticModel}
:= mkContextDeclaration {
    cd_label : label ;
    cd_variable : variable ;
    cd_pattern : AppliedOperatorOr' symbol BuiltinOrVar ;
}.


Record RuleDeclaration {Σ : StaticModel}
:= mkRuleDeclaration {
    rd_label : label ;
    rd_rule : FlattenedRewritingRule ;
}.

Arguments mkRuleDeclaration {Σ} rd_label rd_rule.

Inductive Declaration {Σ : StaticModel} :=
| decl_rule (r : RuleDeclaration)
| decl_ctx (c : ContextDeclaration)
.

(*
Coercion decl_rule :
    RuleDeclaration >-> Declaration
.
Coercion decl_ctx :
    ContextDeclaration >-> Declaration
.
*)

Notation "'rule' '[' n ']:' l => r"
    := (decl_rule (mkRuleDeclaration
        n (rule l => r requires [])
    ))
    (at level 200)
.

Notation "'rule' '[' n ']:' l => r 'where' s"
    := (decl_rule (mkRuleDeclaration
        n (rule l => r requires [sc_constraint (apeq (true)%rule_scs s%rule_scs)])
    ))
    (at level 200)
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


Definition initialState
    {Σ : StaticModel}
    : State
:= {|
    st_rules := ∅ ;
    st_log := "";
|}.

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

(* TODO implement *)
Definition process_context_declaration
    {Σ : StaticModel}
    (s : State)
    (c : ContextDeclaration)
    : State
:= s.

Definition process_declaration
    {Σ : StaticModel}
    (s : State)
    (d : Declaration)
    : State
:=
match d with
| decl_rule rd => process_rule_declaration s rd
| decl_ctx cd => process_context_declaration s cd
end.

Definition process_declarations
    {Σ : StaticModel}
    (ld : list Declaration)
    : State
:=
    fold_left process_declaration ld initialState
.


Definition to_theory
    {Σ : StaticModel}
    (s : State)
    : FlattenedRewritingTheory
:=
    (map_to_list (st_rules s)).*2
.
