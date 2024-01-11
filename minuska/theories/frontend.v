From Minuska Require Import
    prelude
    spec_syntax
    flattened
    notations
.


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

Notation "'rule' '[' n ']' l => r 'requires' s"
    := (mkRuleDeclaration
        n (rule l => r requires s)
    )
    (at level 200)
.


Inductive Declaration {Σ : StaticModel} :=
| decl_rule (r : RuleDeclaration)
| decl_ctx (c : ContextDeclaration)
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