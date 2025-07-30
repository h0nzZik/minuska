
From Minuska Require Import
    prelude
    spec
.

Declare Scope RuleScope.
Declare Scope ConcreteScope.

Delimit Scope RuleScope with rs.
Delimit Scope ConcreteScope with concrete.


Record ExprAndBoV {Σ : BackgroundModel} : Type := mkExprAndBoV {
    eab_expr : Expression2 ;
    eab_bov : BuiltinOrVar ;
}.

Arguments mkExprAndBoV {Σ} eab_expr eab_bov.
(* 
Class TagLHS := mkTagLHS {}.
Class TagRHS := mkTagRHS {}.
Class TagGround := mkTagGround {}.

Class BasicResolver {Σ : BackgroundModel} := {
    operand_type : Type ;
}.

Class Resolver {Σ : BackgroundModel} {_BR : BasicResolver} := {
    inject_Variabl : Variabl -> operand_type ;
}.

#[export]
Instance BasicResolver_lhs {Σ : BackgroundModel}
    {_T1 : TagLHS}
    : BasicResolver
:= {    
    operand_type := BuiltinOrVar;
}.

#[export]
Instance BasicResolver_rhs {Σ : BackgroundModel}
    {_T2 : TagRHS}
    : BasicResolver
:= {
    operand_type := Expression2 ;
}.

#[export]
Instance BasicResolver_ground {Σ : BackgroundModel}
    {_T2 : TagGround}
    : BasicResolver
:= {
    operand_type := BasicValue ;
}.

#[export]
Instance Resolver_lhs {Σ : BackgroundModel} {_T1 : TagLHS} : Resolver := {    
    inject_Variabl := (*t_over ∘*) bov_Variabl;
}.

#[export]
Instance Resolver_rhs {Σ : BackgroundModel} {_T2 : TagRHS} : Resolver := {
    inject_Variabl := (*t_over ∘ *) e_Variabl;
}. *)

(*

Class ToAOO {Σ : BackgroundModel} {_basic_resolver : BasicResolver}
    (to_aoo_F : Type)
:= {
    to_aoo_opt : to_aoo_F -> (@TermOver' TermSymbol operand_type) ;
}.

#[export]
Instance ToAOO_id {Σ : BackgroundModel} {_basic_resolver : BasicResolver}
    {T : Type}
    {_eq: TCEq T (@TermOver' TermSymbol operand_type)}
    : ToAOO T
.
Proof. inversion _eq. subst. constructor. intros x. exact x. Defined.
(*
{|
    to_aoo_opt := fun x => x;
|}.
*)
(* I have no idea why I need the indirection through T. *)
#[export]
Instance ToAOO_inj {Σ : BackgroundModel} {_basic_resolver : BasicResolver}
    {T : Type}
    {_eq: TCEq T operand_type}
    : ToAOO  (T)
.
Proof. inversion _eq. subst. constructor. apply term_operand. Defined.
(*
:= {|
    to_aoo_opt := term_operand;
|}.
*)

Arguments to_aoo_opt {Σ _basic_resolver} {to_aoo_F}%_type_scope {ToAOO} _.

*)
(* 
Notation "'$' x" :=
    (inject_Variabl x)
    (at level 40)
. *)
(* 
Notation "'llrule' l '~>{' a '}' r 'requires' s"
    := (@mkRewritingRule2
        _
        _
        ((fun (_:TagLHS) => l) mkTagLHS)%rs
        ((fun (_:TagRHS) => r) mkTagRHS)%rs
        ((fun (_:TagRHS) => s) mkTagRHS)%rs
        a
        
    )
    (at level 200)
.

Notation "'rule' l '~>{' a '}' r 'requires' s"
    := (llrule
        (l)
        ~>{a}
        (r) 
        requires
        s
    )
    (at level 200)
.


Notation "( 'ground' g )" := ((fun (_:TagGround) => (g)) mkTagGround). *)
