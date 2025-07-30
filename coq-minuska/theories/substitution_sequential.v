From Minuska Require Import
    prelude
    spec
    termoverbov_subst (* TermOverBoV_subst *)
.

Definition SubS {Σ : BackgroundModel} : Type
:=
    list (Variabl*(@TermOver' TermSymbol BuiltinOrVar))%type
.

Definition subt_closed {Σ : BackgroundModel} (s : SubS) :=
    forall k v, s !! k = Some v -> vars_of v.2 = ∅
.

(* TODO use fold *)
Fixpoint subs_app {Σ : BackgroundModel} (s : SubS) (t : @TermOver' TermSymbol BuiltinOrVar) : @TermOver' TermSymbol BuiltinOrVar :=
match s with
| [] => t
| (x,t')::s' => subs_app s' (TermOverBoV_subst t x t')
end
.
