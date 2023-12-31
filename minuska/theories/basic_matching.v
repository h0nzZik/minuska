
From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    flattened
    flatten
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.

Section with_signature.
    Context
        {Σ : Signature}
    .

    Fixpoint ApppliedOperator'_matches_AppliedOperator'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Valuation -> Operand1 -> Operand2 -> bool)
        (matches_app_1 :
            Valuation ->
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            bool
        )
        (matches_app_2 :
            Valuation ->
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            bool
        )
        (ρ : Valuation)
        (x : AppliedOperator' Operator Operand1)
        (y : AppliedOperator' Operator Operand2)
        : bool :=
    match x, y with
    | ao_operator a1, ao_operator a2 =>
        bool_decide (a1 = a2)
    | ao_operator _, ao_app_operand _ _ => false
    | ao_operator _, ao_app_ao _ _ => false
    | ao_app_operand _ _ , ao_operator _ => false
    | ao_app_operand app1 o1, ao_app_operand app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            ρ
            app1
            app2
        && matches ρ o1 o2
    | ao_app_operand app1 o1, ao_app_ao app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            ρ
            app1
            app2
        && matches_app_1 ρ o1 o2
    | ao_app_ao app1 o1, ao_operator _ => false
    | ao_app_ao app1 o1, ao_app_operand app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            ρ
            app1
            app2
        && matches_app_2 ρ o1 o2
    | ao_app_ao app1 o1, ao_app_ao app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            ρ
            app1
            app2
        &&
        ApppliedOperator'_matches_AppliedOperator' 
            Operator
            Operand1
            Operand2
            matches
            matches_app_1
            matches_app_2
            ρ
            o1
            o2
    end.

    Set Typeclasses Debug.
    Lemma reflect__satisfies__ApppliedOperator'_matches_AppliedOperator'
        (Operand1 Operand2 : Type)
        {Sat1 : Satisfies (Valuation * Operand1) Operand2}
        {Sat2 : Satisfies (Valuation * Operand1) (AppliedOperator' symbol Operand2)}
        {Sat3 : Satisfies (Valuation * AppliedOperator' symbol Operand1) Operand2}
        (matches : Valuation -> Operand1 -> Operand2 -> bool)
        (matches_app_1 :
            Valuation ->
            Operand1 ->
            AppliedOperator' symbol Operand2 ->
            bool
        )
        (matches_app_2 :
            Valuation ->
            AppliedOperator' symbol Operand1 ->
            Operand2 ->
            bool
        )
        (reflect_matches : ∀ ρ o1 o2,
            reflect (satisfies (ρ,o1) o2) (matches ρ o1 o2))
        (reflect_matches_app_1 : ∀ ρ o1 o2,
            reflect (satisfies (ρ,o1) o2) (matches_app_1 ρ o1 o2))
        (reflect_matches_app_2 : ∀ ρ o1 o2,
            reflect (satisfies (ρ,o1) o2) (matches_app_2 ρ o1 o2))
        (ρ : Valuation)
        (x : AppliedOperator' symbol Operand1)
        (y : AppliedOperator' symbol Operand2)
        :
        reflect
            (satisfies (ρ,x) y)
            (ApppliedOperator'_matches_AppliedOperator'
                symbol Operand1 Operand2
                matches
                matches_app_1
                matches_app_2
                 ρ x y
            )
    .
    Proof.
        revert y.
        induction x; intros y; destruct y; simpl.
        {
            unfold bool_decide.
            ltac1:(case_match).
            {
                apply ReflectT.
                subst.
                apply Sat4_refl.
            }
            {
                apply ReflectF.
                apply Sat4_reflonly.
                assumption.
            }
        }
        {

            apply ReflectF.
            intros HContra.
            inversion HContra.
        }
    Qed.

    Definition ApppliedOperatorOr'_matches_AppliedOperatorOr'
        (Operator : Type)
        {Operator_eqdec : EqDecision Operator}
        (Operand1 Operand2 : Type)
        (matches : Valuation -> Operand1 -> Operand2 -> bool)
        (matches_app_1 :
            Valuation ->
            Operand1 ->
            AppliedOperator' Operator Operand2 ->
            bool
        )
        (matches_app_2 :
            Valuation ->
            AppliedOperator' Operator Operand1 ->
            Operand2 ->
            bool
        )
        (ρ : Valuation)
        (x : AppliedOperatorOr' Operator Operand1)
        (y : AppliedOperatorOr' Operator Operand2)
        : bool :=
    match x, y with
    | aoo_app _ _ app1, aoo_app _ _ app2 =>
        ApppliedOperator'_matches_AppliedOperator'
            Operator
            Operand1 Operand2
            matches matches_app_1 matches_app_2
            ρ
            app1 app2
    | aoo_app _ _ app1, aoo_operand _ _ o2 =>
        matches_app_2 ρ app1 o2
    | aoo_operand _ _ o1, aoo_app _ _ app2 =>
        matches_app_1 ρ o1 app2
    | aoo_operand _ _ o1, aoo_operand _ _ o2 =>
        matches ρ o1 o2
    end.

    Definition builtin_value_matches_BuiltinOrVar
        (ρ : Valuation)
        : builtin_value -> BuiltinOrVar -> bool :=
    fun b bv =>
    match bv with
    | bov_builtin b' => bool_decide (b = b')
    | bov_variable x =>
        match ρ !! x with
        | None => false
        | Some (aoo_app _ _ _) => false
        | Some (aoo_operand _ _ b') => bool_decide (b = b')
        end
    end.

    Definition builtin_value_try_match_BuiltinOrVar:
        builtin_value -> BuiltinOrVar -> option Valuation :=
    fun b bv =>
    match bv with
    | bov_builtin b' => if (decide (b = b')) then Some ∅ else None
    | bov_variable x => Some (<[x := (aoo_operand _ _ b)]>∅)
    end.

    Definition builtin_value_matches_pure_OpenTerm
        (ρ : Valuation)
        : builtin_value -> OpenTerm -> bool :=
    fun b t =>
    match t with
    | aoo_app _ _ _ => false
    | aoo_operand _ _ (bov_variable x) =>
        match ρ !! x with
        | None => false
        | Some (aoo_app _ _ _) => false
        | Some (aoo_operand _ _ b') => bool_decide (b = b')
        end
    | aoo_operand _ _ (bov_builtin b') =>
        bool_decide (b = b')
    end.

    Definition pure_GroundTerm_matches_BuiltinOrVar
        (ρ : Valuation)
        : AppliedOperator' symbol builtin_value -> BuiltinOrVar -> bool
    := fun t bov =>
    match bov with
    | bov_builtin b => false
    | bov_variable x =>
        bool_decide (ρ !! x = Some (aoo_app _ _ t))
    end.

    Definition pure_GroundTerm_try_match_BuiltinOrVar:
        AppliedOperator' symbol builtin_value -> BuiltinOrVar -> option Valuation
    := fun t bov =>
    match bov with
    | bov_builtin b => None
    | bov_variable x =>
        Some (<[x := (aoo_app _ _ t)]>∅)
    end.

    Definition GroundTerm_matches_OpenTerm
        (ρ : Valuation):
        GroundTerm -> OpenTerm -> bool :=
        ApppliedOperatorOr'_matches_AppliedOperatorOr'
            symbol
            builtin_value
            BuiltinOrVar
            (builtin_value_matches_BuiltinOrVar)
            (fun ρ' x y => false)
            (pure_GroundTerm_matches_BuiltinOrVar)
            ρ
    .

    Lemma reflect__satisfies__GroundTerm_matches_OpenTerm
        (ρ : Valuation) (g : GroundTerm) (φ : OpenTerm):
        reflect (satisfies (ρ,g) φ) (GroundTerm_matches_OpenTerm ρ g φ)
    .
    Proof.
        destruct g,φ; simpl.
        {
            revert ao0.
            induction ao; intros ao0; destruct ao0; simpl.
            {
                unfold bool_decide,decide_rel.
                ltac1:(case_match).
                {
                    subst.
                    apply ReflectT.
                    constructor.
                    constructor.
                }
                {
                    apply ReflectF.
                    intros HContra.
                    inversion HContra; subst; clear HContra.
                    inversion pf; subst; clear pf.
                    ltac1:(contradiction n).
                    reflexivity.
                }
            }
            {
                apply ReflectF.
                intros HContra.
                inversion HContra; subst; clear HContra.
                inversion pf.
            }
            {
                apply ReflectF.
                intros HContra.
                inversion HContra; subst; clear HContra.
                inversion pf.
            }
            {
                apply ReflectF.
                intros HContra.
                inversion HContra; subst; clear HContra.
                inversion pf.
            }
            {
                simpl.
                destruct (builtin_value_matches_BuiltinOrVar ρ b b0).
                {
                    rewrite andb_true_r.
                    apply IHao.
                }
                apply andPP.
                Search ssrbool.reflect andb.
                rewrite IHao.
            }
        }     
    Qed.

End with_signature.