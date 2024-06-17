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
        sub_app u t1 = sub_app u t2
    ;

    ua_unify_complete :
        forall (t1 t2 : TermOver BuiltinOrVar),
            ua_unify t1 t2 = None ->
            forall (s : SubT),
                sub_app s t1 <> sub_app s t2
    ;
}.