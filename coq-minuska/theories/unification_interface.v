From Minuska Require Import
    prelude
    spec
    substitution_parallel
.

Definition eqn {Σ : BackgroundModel} : Type :=
    ((@TermOver' TermSymbol BuiltinOrVar)*(@TermOver' TermSymbol BuiltinOrVar))%type
.

Definition is_unifier_of {Σ : BackgroundModel} (s : SubP) (l : list eqn) :=
  Forall (fun '(e1, e2) => subp_app s e1 = subp_app s e2) l
.


Class UnificationAlgorithm
    {Σ : BackgroundModel}
:= {
    ua_unify :
        @TermOver' TermSymbol BuiltinOrVar ->
        @TermOver' TermSymbol BuiltinOrVar ->
        option SubP
    ;
    
    ua_unify_sound :
        forall
            (t1 t2 : @TermOver' TermSymbol BuiltinOrVar)
            (u : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar)),
        ua_unify t1 t2 = Some u ->
        (subp_app u t1 = subp_app u t2) /\
        (
            forall (u' : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar)),
                subp_is_normal u' ->
                dom u' ∪ subp_codom u' ⊆ vars_of t1 ∪ vars_of t2 ->
                dom u' ## subp_codom u' ->
                subp_app u' t1 = subp_app u' t2 ->
                exists (u'' : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar)),
                    (* u' = subp_precompose u'' u *)
                    u' = subp_restrict (vars_of t1 ∪ vars_of t2) (subp_compose u'' u)
                (* I think that [u ⊆ u'] would be too strong.
                   For example, we may have a unifier u = {x -> f(5)}
                   and u' = {x -> f(y)}, and clearly u ⊆ u' does not hold
                   despite u being a specialization of u'
                 *)
                    (* u ⊆ u' *)
        )
    ;

    ua_unify_complete :
        forall (t1 t2 : @TermOver' TermSymbol BuiltinOrVar),
            ua_unify t1 t2 = None ->
            forall (s : SubP),
                dom s ## subp_codom s ->
                subp_app s t1 <> subp_app s t2
    ;
}.
