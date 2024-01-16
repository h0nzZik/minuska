
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
Class TagGround := mkTagGround {}.

Class BasicResolver {Σ : StaticModel} := {
    operand_type : Type ;
}.

Class Resolver {Σ : StaticModel} {_BR : BasicResolver} := {
    inject_variable : variable -> operand_type ;
}.

#[export]
Instance BasicResolver_lhs {Σ : StaticModel}
    {_T1 : TagLHS}
    : BasicResolver
:= {    
    operand_type := BuiltinOrVar;
}.

#[export]
Instance BasicResolver_rhs {Σ : StaticModel}
    {_T2 : TagRHS}
    : BasicResolver
:= {
    operand_type := Expression ;
}.

#[export]
Instance BasicResolver_ground {Σ : StaticModel}
    {_T2 : TagGround}
    : BasicResolver
:= {
    operand_type := builtin_value ;
}.

#[export]
Instance Resolver_lhs {Σ : StaticModel} {_T1 : TagLHS} : Resolver := {    
    inject_variable := bov_variable;
}.

#[export]
Instance Resolver_rhs {Σ : StaticModel} {_T2 : TagRHS} : Resolver := {
    inject_variable := ft_variable;
}.


Class ToAOO {Σ : StaticModel} {_basic_resolver : BasicResolver}
    (to_aoo_F : Type)
:= {
    to_aoo_opt : to_aoo_F -> (AppliedOperatorOr' symbol operand_type) ;
}.

#[export]
Instance ToAOO_id {Σ : StaticModel} {_basic_resolver : BasicResolver}
    : ToAOO (AppliedOperatorOr' symbol operand_type) :=
{|
    to_aoo_opt := fun x => x;
|}.

(* I have no idea why I need the indirection through T. *)
#[export]
Instance ToAOO_inj {Σ : StaticModel} {_basic_resolver : BasicResolver}
    {T : Type}
    {_eq: TCEq T operand_type}
    : ToAOO  (T)
.
Proof. inversion _eq. subst. constructor. apply aoo_operand. Defined.
(*
:= {|
    to_aoo_opt := aoo_operand;
|}.
*)

Arguments to_aoo_opt {Σ _basic_resolver} {to_aoo_F}%type_scope {ToAOO} _.

Notation "'$' x" :=
    (inject_variable x)
    (at level 40)
.

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

Definition apply_symbol'
    {Σ : StaticModel}
    {T : Type}
    (s : symbol)
: 
    list ((AppliedOperatorOr' symbol T)) ->
    AppliedOperatorOr' symbol T
:=
    fun l =>
    (to_AppliedOperatorOr' (inr (to_AppliedOperator' ((s):symbol) l)))
.


Definition apply_symbol
    {Σ : StaticModel}
    {_br : BasicResolver}
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
    (@cons ((AppliedOperatorOr' symbol operand_type))
        (myap _ (AppliedOperatorOr' symbol operand_type) x to_aoo_opt)
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


Notation "( 'ground' g )" := ((fun (_:TagGround) => (g)) mkTagGround).
