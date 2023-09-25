From Coq Require Import ssreflect ssrfun ssrbool.
From Coq.Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable decidable finite list list_numbers gmap strings.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
Set Equations Transparent.

Require Import Wellfounded.
From Ltac2 Require Import Ltac2.

From Minuska Require Import minuska.

(*
#[export]
Instance rr_satisfies_dec
    {Σ : Signature}
    (left_right : LR)
    (ρ : Valuation)
    (r : RewritingRule)
    (e : Element)
    : Decision (rr_satisfies left_right ρ r e)
.
Proof. Admitted.
*)

Fixpoint evaluate_simple_pattern
    {Σ : Signature}
    (ρ : Valuation)
    (φ : SimplePattern)
    : option Element :=
match φ with
| spat_builtin v => Some (el_builtin v)
| spat_sym s => Some (el_sym s)
| spat_app φ1 φ2 =>
    let oe1 := (evaluate_simple_pattern ρ φ1) in
    let oe2 := (evaluate_simple_pattern ρ φ2) in
    match oe1,oe2 with
    | Some e1, Some e2 =>
        Some (el_app e1 e2)
    | _,_ => None
    end
| spat_var x => ρ !! x
end
.

Lemma evaluate_simple_pattern_correct
    {Σ : Signature}
    (φ : SimplePattern)
    (ρ : Valuation)
    (e : Element)
    : evaluate_simple_pattern ρ φ = Some e ->
    element_satisfies_simple_pattern_in_valuation e φ ρ
.
Proof.
    induction φ; cbn; intros H.
    {
        
    }

Qed.

Print LocalRewrite.

Fixpoint rhs_evaluate_rule
    {Σ : Signature}
    (ρ : Valuation)
    (r : RewritingRule)
    : option Element :=
match r with
| rr_local_rewrite lr =>
    evaluate_simple_pattern ρ (lr_to lr)
| rr_builtin b => Some (el_builtin b)
| rr_app r1 r2 =>
    let oe1 := rhs_evaluate_rule ρ r1 in
    let oe2 := rhs_evaluate_rule ρ r2 in
    match oe1,oe2 with
    | Some e1, Some e2 => Some (el_app e1 e2)
    | _,_ => None
    end
| rr_var x => ρ !! x
  (* We ignore requires clauses when evaluating RHS*)
| rr_requires r' _ => rhs_evaluate_rule ρ r'
| rr_requires_match r' _ _ => rhs_evaluate_rule ρ r'
end
.

Lemma rhs_evaluate_rule_correct
    {Σ : Signature}
    (r : RewritingRule)
    (ρ : Valuation)
    (e : Element)
    : rhs_evaluate_rule ρ r = Some e ->
    rr_satisfies LR_Right ρ r e
.
Proof.
    induction r; cbn; intros H.
    {

    }
Qed.

Definition lhs_match_one
    {Σ : Signature}
    (e : Element)
    (r : RewritingRule)
    : option Valuation
.
Admitted.

Lemma lhs_match_one_Some
    {Σ : Signature}
    (e : Element)
    (r : RewritingRule)
    (ρ : Valuation)
    :
    lhs_match_one e r = Some ρ <->
    rr_satisfies LR_Left ρ r e
.
Proof. Admitted.

Lemma lhs_match_one_None
    {Σ : Signature}
    (e : Element)
    (r : RewritingRule)
    :
    lhs_match_one e r = None <-> 
    ~ exists (ρ : Valuation),
        rr_satisfies LR_Left ρ r e
.
Proof.
Admitted.


Definition thy_lhs_match_one
    {Σ : Signature}
    (e : Element)
    (Γ : RewritingTheory)
    : option (RewritingRule * Valuation)%type
    := let vs : list (option Valuation) := lhs_match_one e <$> Γ in
       let found : option (nat * option Valuation) := list_find is_Some vs in
       match found with
       | None => None
       | Some (_, None) => None
       | Some (n, Some v) => (
        match Γ !! n with
        | Some r => Some (r, v)
        | None => None
        end)
       end
.

Lemma thy_lhs_match_one_None
    {Σ : Signature}
    (e : Element)
    (Γ : RewritingTheory)
    :
    thy_lhs_match_one e Γ = None ->
    ~ exists (r : RewritingRule) (ρ : Valuation),
        r ∈ Γ /\ rr_satisfies LR_Left ρ r e
.
Proof.
    unfold thy_lhs_match_one.
    intros H [r [ρ [Hin HContra]]].
    destruct (list_find is_Some (lhs_match_one e <$> Γ)) eqn:Heqfound.
    {
        destruct p as [n oρ].
        rewrite list_find_Some in Heqfound.
        ltac1:(destruct Heqfound as [Hfound [HSome HFirst]]).
        destruct oρ.
        {
            subst. clear HFirst.
            destruct (Γ !! n) eqn:Heq.
            { inversion H. }
            clear H. clear HSome.
            rewrite list_lookup_fmap in Hfound.
            ltac1:(rewrite Heq in Hfound).
            cbn in Hfound.
            inversion Hfound.
        }
        {
            inversion HSome. inversion H0.
        }
    }
    {
        clear H.
        rewrite list_find_None in Heqfound.
        rewrite Forall_forall in Heqfound.
        specialize (Heqfound (Some ρ)).
        ltac1:(rewrite elem_of_list_fmap in Heqfound).
        ltac1:(feed specialize Heqfound).
        {
            exists r.
            split.
            {
                symmetry.
                apply lhs_match_one_Some.
                exact HContra.
            }
            {
                exact Hin.
            }
        }
        {
            unfold is_Some.
            exists ρ. reflexivity.
        }
        exact Heqfound.
    }
Qed.

Definition naive_interpreter
    {Σ : Signature}
    (Γ : RewritingTheory)
    (e : Element)
    : option Element
:=
    let oρ : option (RewritingRule*Valuation) := thy_lhs_match_one e Γ in
    match oρ with
    | None => None
    | Some (r,ρ) => Some (rhs_evaluate_rule ρ r)
    end
.

