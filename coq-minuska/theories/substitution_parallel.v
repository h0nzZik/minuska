From Minuska Require Import
    prelude
    spec
    basic_properties
.


(* 'parallel' substitution *)
Definition SubP {Σ : BackgroundModel} : Type
:=
    gmap Variabl (@TermOver' TermSymbol BuiltinOrVar)
.

(* 
#[export]
Instance union_subp {Σ : BackgroundModel} : Union SubP.
Proof.
    unfold SubP.
    apply _.
Defined. *)


Fixpoint subp_app {Σ : BackgroundModel} (s : SubP) (t : @TermOver' TermSymbol BuiltinOrVar) : @TermOver' TermSymbol BuiltinOrVar :=
match t with
  | t_over (bov_Variabl v) => let t'_opt := s !! v in
    match t'_opt with
      | None => t
      | Some t' => t'
    end
  | t_term sm l => t_term sm (map (λ t' : @TermOver' TermSymbol BuiltinOrVar, subp_app s t') l)
  | _ => t
end
.

Definition subp_dom
  {Σ : BackgroundModel}
  (s : SubP)
: gset Variabl
:=
  dom s
.

(* Check @map_img. *)
Definition subp_codom
  {Σ : BackgroundModel}
  (s : SubP)
: gset Variabl
:=
  let img' : listset (@TermOver' TermSymbol BuiltinOrVar) := map_img s in
  let img : list (@TermOver' TermSymbol BuiltinOrVar) := elements img' in
  let vs : list (gset Variabl) := vars_of <$> img in
  ⋃ (vs)
.

Definition subp_normalize
  {Σ : BackgroundModel}
  (a : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar))
  : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar)
:=
  filter
    (fun kv => t_over (bov_Variabl kv.1) <> kv.2)
    a
.

Definition subp_is_normal
  {Σ : BackgroundModel}
  (a : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar))
  : Prop
:=
  subp_normalize a = a
.

(* a after b *)
Definition subp_compose
  {Σ : BackgroundModel}
  (a b : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar))
:=
  subp_normalize
    (union
      ((filter (fun kv => kv.1 ∉ subp_dom b) a))
      (fmap (subp_app a) b) 
    )
.

Definition subp_id
  {Σ : BackgroundModel}
  :
  gmap Variabl (@TermOver' TermSymbol BuiltinOrVar)
:=
  empty
.

Definition RestrictP {Σ : BackgroundModel} (to : gset Variabl) : (prod (Variabl) (@TermOver' TermSymbol BuiltinOrVar)) -> Prop :=
  fun x => x.1 ∈ to
.

#[export]
Instance restrictp_decision {Σ : BackgroundModel} (to : gset Variabl) : forall x, Decision (RestrictP to x).
Proof.
  intros x.
  unfold RestrictP.
  apply _.
Defined.

Definition subp_restrict
  {Σ : BackgroundModel}
  (to : gset Variabl)
  : SubP -> SubP
:=
  filter (RestrictP to)
.

Definition subp_precompose
  {Σ : BackgroundModel}
  (a b : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar))
:=
      (fmap (subp_app a) b) 
.
