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

(* a after b *)
(* 
  examples:
    1. a={(y,0)}, b={(x,f(y))} ==> {(x, f(0))}
    2. a={(x,f(y))}, b={(y,0)} ==> {(x,f(y)), (y, 0)}

 *)
 (* About filter. *)
Definition subp_compose
  {Σ : StaticModel}
  (a b : SubP)
:=
  union (fmap (subp_app b) (filter (fun kv => kv.1 ∉ subp_codom b) a)) (fmap (subp_app a) b)
.
