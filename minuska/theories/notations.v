
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    flattened
.

Declare Scope RuleScope.
Declare Scope ConcreteScope.

Delimit Scope RuleScope with rs.
Delimit Scope ConcreteScope with concrete.

Definition to_AppliedOperatorOr'
    {Σ : StaticModel}
    {T : Type}
    (x : ((T)+(AppliedOperator' symbol T)))
    : AppliedOperatorOr' symbol T
:=
match x with
| inl x' => aoo_operand x'
| inr x' => aoo_app x'
end
.


Record ExprAndBoV {Σ : StaticModel} : Type := mkExprAndBoV {
    eab_expr : Expression ;
    eab_bov : BuiltinOrVar ;
}.

Arguments mkExprAndBoV {Σ} eab_expr eab_bov.

Class TagLHS := mkTagLHS {}.
Class TagRHS := mkTagRHS {}.

Class Resolver {Σ : StaticModel} := {
    operand_type : Type ;
    inject_variable : variable -> operand_type ;
}.

#[export]
Instance Resolver_lhs {Σ : StaticModel} {_T1 : TagLHS} : Resolver := {    
    operand_type := BuiltinOrVar;
    inject_variable := bov_variable;
}.

#[export]
Instance Resolver_rhs {Σ : StaticModel} {_T2 : TagRHS} : Resolver := {
    operand_type := Expression ;
    inject_variable := ft_variable;
}.

Class ToAOO {Σ : StaticModel} {_resolver : Resolver}
    (to_aoo_F : Type)
:= {
    to_aoo_opt : to_aoo_F -> (AppliedOperatorOr' symbol operand_type) ;
}.

#[export]
Instance ToAOO_id {Σ : StaticModel}{_resolver : Resolver}
    : ToAOO (AppliedOperatorOr' symbol operand_type) :=
{|
    to_aoo_opt := fun x => x;
|}.

#[export]
Instance ToAOO_inj {Σ : StaticModel}{_resolver : Resolver}
    : ToAOO  (operand_type)
:= {|
    to_aoo_opt := aoo_operand;
|}.


Arguments to_aoo_opt {Σ _resolver} {to_aoo_F}%type_scope {ToAOO} _.

Notation "'$' x" :=
    (inject_variable x)
    (* to_AppliedOperatorOr' (inl (inject_variable x)) *)
    (at level 40)
.

Structure MyApplyConcrete {Σ : StaticModel} := {
    mac_T2 : Type ;
    my_apply_c :
        AppliedOperator' symbol builtin_value ->
        mac_T2 ->
        AppliedOperator' symbol builtin_value ;
}.

Arguments my_apply_c {_} {m} _ _.
Arguments my_apply_c : simpl never.

Definition MyApplyConcrete_operand {Σ : StaticModel} : MyApplyConcrete := {|
    my_apply_c := fun x y => ao_app_operand x y ;
|}.
Canonical MyApplyConcrete_operand.

Definition MyApplyConcrete_ao {Σ : StaticModel} : MyApplyConcrete := {|
    my_apply_c := fun x y => @ao_app_ao symbol builtin_value x y ;
|}.
Canonical MyApplyConcrete_ao.


Definition to_AppliedOperator'
    {Σ : StaticModel}
    {T : Type}
    (s : symbol)
    (l : list ((AppliedOperatorOr' symbol T)))
    : AppliedOperator' symbol T
:=
    fold_left
        (fun a b =>
            match b with
            | aoo_operand b' => ao_app_operand a b'
            | aoo_app b' => ao_app_ao a b'
            end
        )
        l
        (ao_operator s)
.

Definition apply_symbol
    {Σ : StaticModel}
    {_r : Resolver}
    (s : symbol)
: 
    list ((AppliedOperatorOr' symbol operand_type)) ->
    AppliedOperatorOr' symbol operand_type
:=
    fun l =>
    (to_AppliedOperatorOr' (inr (to_AppliedOperator' ((s):symbol) l)))
.

Notation "[]" := ([]%list) : RuleScope.

(*
    We need to infer the type of 'A' before choosing the function.
*)
Definition myap (A B : Type) (x : A) (f : A -> B) : B := f x.
Definition myap2 (A B : Type) (f : A -> B) (x : A)  : B := f x.

Notation "'[' x ']'"
:=
    (@cons
        ((AppliedOperatorOr' symbol operand_type))
        (myap _ (AppliedOperatorOr' symbol operand_type) x to_aoo_opt)
        (*myap2 _ (AppliedOperatorOr' symbol operand_type) to_aoo_opt x*)
        (*(@to_aoo_opt _ _ _ _ (x))*)
        (@nil ((AppliedOperatorOr' symbol operand_type)))
    )
    : RuleScope
.

Notation "'[' x , y , .. , z ']'"
:=
    (@cons ((AppliedOperatorOr' symbol operand_type)) (to_aoo_opt x)
    (@cons 
        ((AppliedOperatorOr' symbol operand_type))
        (*(to_aoo_opt y)*)
        (myap _ (AppliedOperatorOr' symbol operand_type) y to_aoo_opt)
        (*myap2 _ (AppliedOperatorOr' symbol operand_type) to_aoo_opt y*)
        .. 
        (
            @cons ((AppliedOperatorOr' symbol operand_type))
            (* (to_aoo_opt z) *)
            (myap _ (AppliedOperatorOr' symbol operand_type) z to_aoo_opt)
            (*myap2 _ (AppliedOperatorOr' symbol operand_type) to_aoo_opt z*)
            (@nil ((AppliedOperatorOr' symbol operand_type)))
        )
        ..))
    : RuleScope
.

Notation "'llrule' l ~> r 'requires' s"
    := (@mkFlattenedRewritingRule
        _
        ((fun (_:TagLHS) => l) mkTagLHS)%rs
        ((fun (_:TagRHS) => r) mkTagRHS)%rs
        ((fun (_:TagRHS) => s) mkTagRHS)%rs
        
    )
    (at level 200)
.

Notation "'rule' l ~> r 'requires' s"
    := (llrule
        (l)
        ~>
        (r) 
        requires
        s
    )
    (at level 200)
.
