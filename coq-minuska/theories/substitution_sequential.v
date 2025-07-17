From Minuska Require Import
    prelude
    spec
    termoverbov_subst (* TermOverBoV_subst *)
.

Definition SubS {Σ : StaticModel} : Type
:=
    list (variable*(TermOver BuiltinOrVar))%type
.

Definition subt_closed {Σ : StaticModel} (s : SubS) :=
    forall k v, s !! k = Some v -> vars_of v.2 = ∅
.

(* TODO use fold *)
Fixpoint subs_app {Σ : StaticModel} (s : SubS) (t : TermOver BuiltinOrVar) : TermOver BuiltinOrVar :=
match s with
| [] => t
| (x,t')::s' => subs_app s' (TermOverBoV_subst t x t')
end
.
