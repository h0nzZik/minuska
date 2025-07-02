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

(* 
#[export]
Instance union_subp {Σ : StaticModel} : Union SubP.
Proof.
    unfold SubP.
    apply _.
Defined. *)


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

Definition subp_normalize
  {Σ : StaticModel}
  (a : gmap variable (TermOver BuiltinOrVar))
  : gmap variable (TermOver BuiltinOrVar)
:=
  filter
    (fun kv => t_over (bov_variable kv.1) <> kv.2)
    a
.

Definition subp_is_normal
  {Σ : StaticModel}
  (a : gmap variable (TermOver BuiltinOrVar))
  : Prop
:=
  subp_normalize a = a
.

(* a after b *)
Definition subp_compose
  {Σ : StaticModel}
  (a b : gmap variable (TermOver BuiltinOrVar))
:=
  subp_normalize
    (union
      ((filter (fun kv => kv.1 ∉ subp_dom b) a))
      (fmap (subp_app a) b) 
    )
.

