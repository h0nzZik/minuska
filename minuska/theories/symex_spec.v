From Minuska Require Import
    prelude
    spec
.

Class SymbolicExecutor
  {Σ : StaticModel}
  {Act : Set}
  (Γ : RewritingTheory2 Act)
  (Γwf: RewritingTheory2_wf_alt Γ)
  :=
{
  se_State :
    Type
  ;

  se_State_interp :
      se_State ->
      TermOver builtin_value ->
      Prop
  ;

  se_next :
    se_State ->
    list se_State
  ;

  se_next_sound:
    forall (s s' : se_State),
      s' ∈ se_next s ->
      forall (g g' : TermOver builtin_value),
        se_State_interp s g ->
        se_State_interp s' g' ->
          { nv : NondetValue &
          rewriting_relation Γ nv g g' }
  ;

  se_next_complete:
    forall (s : se_State) (g g' : TermOver builtin_value) (nv : NondetValue),
      se_State_interp s g ->
      rewriting_relation Γ nv g g' ->
      exists (s' : se_State),
        s' ∈ se_next s /\
        se_State_interp s' g'
  ;

}.
