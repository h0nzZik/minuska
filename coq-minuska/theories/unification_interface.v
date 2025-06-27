From Minuska Require Import
    prelude
    spec
    substitution_parallel
.

Definition eqn {Σ : StaticModel} : Type :=
    ((TermOver BuiltinOrVar)*(TermOver BuiltinOrVar))%type
.

Definition is_unifier_of {Σ : StaticModel} (s : SubP) (l : list eqn) :=
  Forall (fun '(e1, e2) => subp_app s e1 = subp_app s e2) l
.


Class UnificationAlgorithm
    {Σ : StaticModel}
:= {
    ua_unify :
        TermOver BuiltinOrVar ->
        TermOver BuiltinOrVar ->
        option SubP
    ;
    
    ua_unify_sound :
        forall
            (t1 t2 : TermOver BuiltinOrVar)
            (u : SubP),
        ua_unify t1 t2 = Some u ->
        (subp_app u t1 = subp_app u t2) /\
        (
            forall (u' : SubP),
                subp_app u' t1 = subp_app u' t2 ->
                    map_subseteq u u'
        )
    ;

    ua_unify_complete :
        forall (t1 t2 : TermOver BuiltinOrVar),
            ua_unify t1 t2 = None ->
            forall (s : SubP),
                subp_app s t1 <> subp_app s t2
    ;
}.
