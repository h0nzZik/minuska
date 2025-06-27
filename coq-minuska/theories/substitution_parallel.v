From Minuska Require Import
    prelude
    spec
.


(* 'parallel' substitution *)
Definition SubP {Σ : StaticModel} : Type
:=
    gmap variable (TermOver BuiltinOrVar)
.

Fixpoint subp_app {Σ : StaticModel} (s : SubP) (t : TermOver BuiltinOrVar) : TermOver BuiltinOrVar :=
match t with
  | t_over (bov_variable v) => let t'_opt := s !! v in
    match t'_opt with
      | None => t
      | Some t' => t'
    end
  | t_term sm l => t_term sm (map (λ t' : TermOver BuiltinOrVar, subp_app s t') l)
  | _ => t
end
.

