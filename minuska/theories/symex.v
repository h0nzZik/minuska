From Minuska Require Import
    prelude
    spec
    properties
    minusl_syntax
    syntax_properties
    unification_interface
    symex_spec
.


Require Import Wellfounded.
From stdpp Require Import lexico well_founded.

Require Import Program.
From Coq Require Import Logic.Eqdep_dec.

From Equations Require Export Equations.

Module Implementation.

  Fixpoint toe_to_cpat
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
  :
    ((TermOver BuiltinOrVar)*(list SideCondition2))%type
  :=
  match t with
  | t_over e =>
      let x : variable := fresh avoid in
      (t_over (bov_variable x), [{|sc_left := (e_variable x); sc_right := e|}])
  | t_term s l =>
      let go' := (fix go' (avoid' : list variable) (ts : list (TermOver Expression2)) : ((list (TermOver BuiltinOrVar))*(list SideCondition2))%type :=
        match ts with
        | [] => ([], [])
        | t'::ts' =>
          let tmp := toe_to_cpat avoid' t' in
          let rest := go' (avoid' ++ elements (vars_of (tmp.2))) ts' in
          (tmp.1::rest.1, (tmp.2 ++ rest.2))
        end
      ) in
      let l' := go' avoid l in
      (t_term s (fst l'), snd l')
  end
  .

  Lemma elem_of_list_singleton_inv
    {A : Type}
    (x y : A)
    :
    x ∈ [y] -> x = y
  .
  Proof.
    intros H.
    rewrite elem_of_list_singleton in H.
    exact H.
  Qed.

  Lemma toe_to_cpat_correct_1
    {Σ : StaticModel}
    (avoid : list variable)
    (t : TermOver Expression2)
    (g : TermOver builtin_value)
  :
    ({ ρ : Valuation2 & satisfies ρ g t }) ->
    ({ ρ : Valuation2 &
      (
        (satisfies ρ g ((toe_to_cpat avoid t).1))
        *
        (satisfies ρ tt ((toe_to_cpat avoid t).2))
      )%type
    })
  .
  Proof.
    revert g avoid.
    ltac1:(induction t using TermOver_rect; intros g avoid [ρ Hρ]).
    {
      inversion Hρ; clear Hρ.
      simpl.
      unfold satisfies; simpl.
      exists (<[(fresh avoid) := g]>ρ).
      split.
      {
        ltac1:(simp sat2B).
        unfold Satisfies_Valuation2_TermOverBuiltinValue_BuiltinOrVar.
        unfold Valuation2 in *.
        apply lookup_insert.
      }
      {
        intros x Hx.
        apply elem_of_list_singleton_inv in Hx.
        subst x.
        unfold satisfies; simpl.
        split.
        {
          Search Expression2_evaluate.
        }
        {
          unfold isSome.
          unfold Valuation2 in *.
          rewrite lookup_insert.
          reflexivity.
        }
        Search satisfies.
      }
      Print sat2B.
    }

  Qed.

  Definition keep_data (A : Type) (l : list (option A)) : list A
  :=
    fold_right (fun b a => match b with Some b' => b'::a | None => a end) [] l
  .

  Search (TermOver Expression2).

  Definition sym_step
    {Σ : StaticModel}
    {UA : UnificationAlgorithm}
    {Act : Set}
    (Γ : RewritingTheory2 Act)
    (s : TermOver BuiltinOrVar)
    :
    list (TermOver BuiltinOrVar)
  :=
    let l'' := (fun r => (ur ← ua_unify s (r.(r_from)); Some (ur, r))) <$> Γ in
    let l' := filter (fun x => x <> None) l'' in
    let l := keep_data l' in
    (fun ur => sub_app_e ur.1 (ur.2.(r_to))) <$> l
  .


End Implementation.

