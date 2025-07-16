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
            (u : gmap variable (TermOver BuiltinOrVar)),
        ua_unify t1 t2 = Some u ->
        (subp_app u t1 = subp_app u t2) /\
        (
            forall (u' : gmap variable (TermOver BuiltinOrVar)),
                subp_is_normal u' ->
                dom u' ∪ subp_codom u' ⊆ vars_of t1 ∪ vars_of t2 ->
                dom u' ## subp_codom u' ->
                subp_app u' t1 = subp_app u' t2 ->
                exists (u'' : gmap variable (TermOver BuiltinOrVar)),
                    u' = subp_precompose u'' u
                (* I think that [u ⊆ u'] would be too strong.
                   For example, we may have a unifier u = {x -> f(5)}
                   and u' = {x -> f(y)}, and clearly u ⊆ u' does not hold
                   despite u being a specialization of u'
                 *)
                    (* u ⊆ u' *)
        )
    ;

    ua_unify_complete :
        forall (t1 t2 : TermOver BuiltinOrVar),
            ua_unify t1 t2 = None ->
            forall (s : SubP),
                subp_app s t1 <> subp_app s t2
    ;
}.
