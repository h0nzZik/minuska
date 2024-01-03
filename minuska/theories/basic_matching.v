
From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties(*
    flattened
    flatten*)
.

Require Import Logic.PropExtensionality.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.

Class Matches (A B : Type) {_SAB : Satisfies A B} := {
    matchesb: A -> B -> bool ;
    matchesb_satisfies : ∀ a b, reflect (satisfies a b) (matchesb a b) ;
}.

Arguments satisfies : simpl never.
Arguments matchesb : simpl never.


Section with_signature.
    Context
        {Σ : Signature}
    .

    Fixpoint ApppliedOperator'_matches_AppliedOperator'
        `{Matches (Valuation * Operand1) Operand2}
        `{Matches (Valuation * Operand1) (AppliedOperator' symbol Operand2)}
        `{Matches (Valuation * AppliedOperator' symbol Operand1) Operand2}
        (ρx : Valuation*(AppliedOperator' symbol Operand1))
        (y : AppliedOperator' symbol Operand2)
        : bool :=
    let ρ := ρx.1 in
    let x := ρx.2 in
    match x, y with
    | ao_operator a1, ao_operator a2 =>
        bool_decide (a1 = a2)
    | ao_operator _, ao_app_operand _ _ => false
    | ao_operator _, ao_app_ao _ _ => false
    | ao_app_operand _ _ , ao_operator _ => false
    | ao_app_operand app1 o1, ao_app_operand app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            (ρ,app1)
            app2
        && matchesb (ρ, o1) o2
    | ao_app_operand app1 o1, ao_app_ao app2 o2 => false
    | ao_app_ao app1 o1, ao_operator _ => false
    | ao_app_ao app1 o1, ao_app_operand app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            (ρ,app1)
            app2
        && matchesb (ρ, o1) o2
    | ao_app_ao app1 o1, ao_app_ao app2 o2 =>
        ApppliedOperator'_matches_AppliedOperator' 
            (ρ,app1)
            app2
        &&
        ApppliedOperator'_matches_AppliedOperator' 
            (ρ,o1)
            o2
    end.

    #[export]
    Program Instance reflect__satisfies__ApppliedOperator'_matches_AppliedOperator'
        (Operand1 Operand2 : Type)
        `{Matches (Valuation * Operand1) Operand2}
        `{Matches (Valuation * Operand1) (AppliedOperator' symbol Operand2)}
        `{Matches (Valuation * AppliedOperator' symbol Operand1) Operand2}
        :
        Matches
            (Valuation * (AppliedOperator' symbol Operand1))
            (AppliedOperator' symbol Operand2)
        := {|
            matchesb :=
                ApppliedOperator'_matches_AppliedOperator' ;
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        simpl.
        ltac1:(rename v into ρ).
        ltac1:(rename a into x).
        ltac1:(rename b into y).
        revert y.
        induction x; intros y; destruct y.
        {
            simpl.
            unfold bool_decide.
            ltac1:(case_match).
            {
                apply ReflectT.
                subst.
                constructor.
            }
            {
                apply ReflectF.
                intros HContra.
                inversion HContra; subst; clear HContra.
                ltac1:(contradiction).
            }
        }
        {

            apply ReflectF.
            intros HContra.
            inversion HContra.
        }
        {
            apply ReflectF.
            intros HContra.
            inversion HContra.
        }
        {
            apply ReflectF.
            intros HContra.
            inversion HContra.
        }
        {
            simpl.
            specialize (IHx y).
            simpl in IHx.
            destruct ((ApppliedOperator'_matches_AppliedOperator' (ρ,x) y)) eqn:Heqm1.
            {
                simpl.
                apply reflect_iff in IHx.
                apply proj2 in IHx.
                specialize (IHx eq_refl).
                destruct (matchesb (ρ,b) b0) eqn:Heqm.
                {
                    apply ReflectT.
                    constructor.
                    apply IHx.
                    assert(reflect_matches := matchesb_satisfies (ρ,b) b0).
                    apply reflect_iff in reflect_matches.
                    apply reflect_matches.
                    exact Heqm.
                }
                {
                    apply ReflectF.
                    intros HContra.
                    inversion HContra; subst; clear HContra.
                    assert(reflect_matches := matchesb_satisfies (ρ,b) b0).
                    apply reflect_iff in reflect_matches.
                    apply reflect_matches in H8.
                    rewrite Heqm in H8.
                    inversion H8.
                }
            }
            {
                simpl.
                apply ReflectF.
                intros HContra.
                inversion HContra; subst; clear HContra.
                simpl in H8.
                apply reflect_iff in IHx.
                apply proj1 in IHx.
                specialize (IHx ltac:(assumption)).
                inversion IHx.
            }
        }
        {
            simpl.
            apply ReflectF.
            intros HContra.
            inversion HContra.
        }
        {
            simpl.
            apply ReflectF.
            intros HContra.
            inversion HContra.
        }
        {
            simpl.
            specialize (IHx1 y).
            apply reflect_iff in IHx1.
            simpl in IHx1.
            apply iff_reflect.
            rewrite andb_true_iff.
            rewrite <- IHx1.
            ltac1:(cut ((satisfies (ρ, x2) b) <-> (matchesb (ρ, x2) b = true))).
            {
                intros HH0. rewrite <- HH0.
                simpl.    
                split; intros HH.
                {
                    inversion HH; subst; clear HH.
                    split; assumption.
                }
                {
                    constructor;
                    destruct HH; assumption.
                }
            }
            assert(reflect_matches_app_2 := matchesb_satisfies (ρ,x2) b).
            apply reflect_iff in reflect_matches_app_2.
            apply reflect_matches_app_2.
        }
        {
            specialize (IHx1 y1).
            specialize (IHx2 y2).
            apply reflect_iff in IHx1.
            apply reflect_iff in IHx2.
            apply iff_reflect.
            simpl.
            rewrite andb_true_iff.
            rewrite <- IHx1.
            rewrite <- IHx2.
            simpl.
            split; intros HH; inversion HH; subst; clear HH; constructor; assumption.
        }
    Qed.

    Definition ApppliedOperatorOr'_matches_AppliedOperatorOr'
        {Operand1 Operand2 : Type}
        `{Matches (Valuation*Operand1) Operand2}
        `{Matches (Valuation*Operand1) (AppliedOperator' symbol Operand2)}
        `{Matches (Valuation*(AppliedOperator' symbol Operand1)) Operand2}
        (ρx : Valuation*(AppliedOperatorOr' symbol Operand1))
        (y : AppliedOperatorOr' symbol Operand2)
        : bool :=
    let ρ := ρx.1 in
    let x := ρx.2 in
    match x, y with
    | aoo_app _ _ app1, aoo_app _ _ app2 =>
        matchesb (ρ,app1) app2
    | aoo_app _ _ app1, aoo_operand _ _ o2 =>
        matchesb (ρ, app1) o2
    | aoo_operand _ _ o1, aoo_app _ _ app2 =>
        false (*matchesb (ρ, o1) app2*)
    | aoo_operand _ _ o1, aoo_operand _ _ o2 =>
        matchesb (ρ, o1) o2
    end.

    Program Instance
        reflect__satisfies__ApppliedOperatorOr'_matches_AppliedOperatorOr'
        {Operand1 Operand2 : Type}
        `{M1 : Matches (Valuation * Operand1) Operand2}
        `{M2 : Matches (Valuation * Operand1) (AppliedOperator' symbol Operand2)}
        `{M3 : Matches (Valuation * AppliedOperator' symbol Operand1) Operand2}
        :
        Matches
            (Valuation * (AppliedOperatorOr' symbol Operand1))
            (AppliedOperatorOr' symbol Operand2)
        := {|
            matchesb := 
                ApppliedOperatorOr'_matches_AppliedOperatorOr';
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        ltac1:(rewrite /fst).
        ltac1:(rewrite /snd).
        ltac1:(rename v into ρ).
        ltac1:(rename a into x).
        ltac1:(rename b into y).
        
        simpl.
        destruct x; simpl.
        {
            destruct y; simpl.
            {
                unfold ApppliedOperatorOr'_matches_AppliedOperatorOr'.
                simpl.
                apply iff_reflect.
                split; intros H.
                {
                    inversion H; subst; clear H.
                    eapply introT.
                    { apply matchesb_satisfies. }
                    { assumption. }
                }
                {
                    constructor.
                    eapply elimT.
                    { apply matchesb_satisfies. }
                    { assumption. }
                }
            }
            {
                unfold ApppliedOperatorOr'_matches_AppliedOperatorOr'.
                simpl.
                apply iff_reflect.
                split; intros H.
                {
                    inversion H; subst; clear H.
                    eapply introT.
                    { apply matchesb_satisfies. }
                    { assumption. }
                }
                {
                    constructor.
                    eapply elimT.
                    { apply matchesb_satisfies. }
                    { assumption. }
                }
            }
        }
        {
            unfold ApppliedOperatorOr'_matches_AppliedOperatorOr'.
            simpl.
            destruct y; simpl.
            {
                unfold satisfies.
                simpl.
                apply iff_reflect.
                split; intros H.
                {
                    inversion H; subst; clear H.
                }
                {
                    ltac1:(exfalso).
                    inversion H.
                }
            }
            {
                unfold satisfies.
                simpl.
                apply iff_reflect.
                split; intros H.
                {
                    inversion H; subst; clear H.
                    eapply introT.
                    { apply matchesb_satisfies. }
                    { assumption. }
                }
                {
                    constructor.
                    eapply elimT.
                    { apply matchesb_satisfies. }
                    { assumption. }
                }
            }
        }
    Qed.

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