From Minuska Require Import
    prelude
    spec
    properties
.

Definition SubT {Σ : StaticModel} : Type
:=
    list (variable*(TermOver BuiltinOrVar))%type
.

Fixpoint sub_app {Σ : StaticModel} (s : SubT) (t : TermOver BuiltinOrVar) : TermOver BuiltinOrVar :=
match s with
| [] => t
| (x,t')::s' => sub_app s' (TermOverBoV_subst t x t')
end
.


Fixpoint sub_app_e {Σ : StaticModel} (s : SubT) (t : TermOver Expression2) : TermOver Expression2 :=
match s with
| [] => t
| (x,t')::s' => sub_app_e s' (TermOverBoV_subst_expr2 t' x t)
end
.

Class UnificationAlgorithm
    {Σ : StaticModel}
:= {
    ua_unify :
        TermOver BuiltinOrVar ->
        TermOver BuiltinOrVar ->
        option SubT
    ;
    
    ua_unify_sound :
        forall
            (t1 t2 : TermOver BuiltinOrVar)
            (u : SubT),
        ua_unify t1 t2 = Some u ->
        (sub_app u t1 = sub_app u t2) /\
        (
            forall u',
                sub_app u' t1 = sub_app u' t2 ->
                exists rest,
                forall (x : variable),
                    sub_app (u ++ rest) (t_over (bov_variable x)) = sub_app u' (t_over (bov_variable x))
        )
    ;

    ua_unify_complete :
        forall (t1 t2 : TermOver BuiltinOrVar),
            ua_unify t1 t2 = None ->
            forall (s : SubT),
                sub_app s t1 <> sub_app s t2
    ;
}.