From Minuska Require Import
    prelude
    spec
    basic_properties
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

Definition subp_dom
  {Σ : StaticModel}
  (s : SubP)
: gset variable
:=
  dom s
.

(* Check @map_img. *)
Definition subp_codom
  {Σ : StaticModel}
  (s : SubP)
: gset variable
:=
  let img' : listset (TermOver BuiltinOrVar) := map_img s in
  let img : list (TermOver BuiltinOrVar) := elements img' in
  let vs : list (gset variable) := vars_of <$> img in
  ⋃ (vs)
.

(* a after b *)
Definition subp_compose
  {Σ : StaticModel}
  (a b : SubP)
:=
  union (fmap (fun p => subp_app b p) a) b
.

