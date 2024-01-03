
From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
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

    #[export]
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
        : Valuation*builtin_value -> BuiltinOrVar -> bool :=
    fun ρb bv =>
    match bv with
    | bov_builtin b' => bool_decide (ρb.2 = b')
    | bov_variable x =>
        match ρb.1 !! x with
        | None => false
        | Some (aoo_app _ _ _) => false
        | Some (aoo_operand _ _ b') => bool_decide (ρb.2 = b')
        end
    end.


    #[export]
    Program Instance
        reflect__matches__builtin_value__BuiltinOrVar
        :
        Matches
            (Valuation * builtin_value)
            BuiltinOrVar
        := {|
            matchesb := 
                builtin_value_matches_BuiltinOrVar;
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        unfold satisfies; simpl.
        destruct b; unfold builtin_satisfies_BuiltinOrVar'; simpl.
        {
            apply iff_reflect.
            split; intros HH.
            {
                inversion HH; subst; clear HH.
                unfold bool_decide.
                ltac1:(case_match; subst; naive_solver).
            }
            {
                unfold bool_decide in HH.
                ltac1:(case_match; subst; try contradiction; try constructor; naive_solver).
            }
        }
        {
            destruct (v !! x) eqn:Hvx; simpl.
            {
                destruct a; simpl.
                {
                    apply ReflectF.
                    intros HContra.
                    inversion HContra; subst; clear HContra.
                    ltac1:(simplify_eq/=).
                }
                {
                    unfold bool_decide.
                    ltac1:(case_match).
                    {
                        apply ReflectT.
                        constructor. subst. assumption.
                    }
                    {
                        apply ReflectF.
                        intros HContra.
                        inversion HContra; subst; clear HContra.
                        ltac1:(simplify_eq/=).
                    }
                }
            }
            {
                apply ReflectF.
                intros HContra.
                inversion HContra; subst; clear HContra.
                ltac1:(simplify_eq/=).
            }
        }
    Qed.
    Fail Next Obligation.

    Definition builtin_value_matches_OpenTerm
        : Valuation*builtin_value -> OpenTerm -> bool :=
    fun ρb t =>
    match t with
    | aoo_app _ _ _ => false
    | aoo_operand _ _ (bov_variable x) =>
        match ρb.1 !! x with
        | None => false
        | Some (aoo_app _ _ _) => false
        | Some (aoo_operand _ _ b') => bool_decide (ρb.2 = b')
        end
    | aoo_operand _ _ (bov_builtin b') =>
        bool_decide (ρb.2 = b')
    end.

    #[export]
    Program Instance
        reflect__matches__builtin_value__OpenTerm
        :
        Matches
            (Valuation * builtin_value)
            OpenTerm
        := {|
            matchesb := builtin_value_matches_OpenTerm;
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        destruct b; simpl.
        {
            apply ReflectF.
            intros HContra.
            inversion HContra.
        }
        {
            unfold bool_decide.
            ltac1:((repeat case_match); simplify_eq/=);
                try (apply ReflectF; intros HContra; inversion HContra; subst; clear HContra;
                    ltac1:(simplify_eq/=)).
            {
                apply ReflectT.
                constructor.
            }
            {
                apply ReflectT.
                constructor.
                simpl.
                assumption.
            }
        }
    Qed.
    Fail Next Obligation.

    Definition GroundTerm'_matches_BuiltinOrVar
        : Valuation*(AppliedOperator' symbol builtin_value) ->
            BuiltinOrVar ->
            bool
    := fun ρt bov =>
    match bov with
    | bov_builtin b => false
    | bov_variable x =>
        bool_decide (ρt.1 !! x = Some (aoo_app _ _ ρt.2))
    end.

    #[export]
    Program Instance
        matches__builtin_value__OpenTerm
        :
        Matches
            (Valuation * (AppliedOperator' symbol builtin_value))
            BuiltinOrVar
        := {|
            matchesb := GroundTerm'_matches_BuiltinOrVar;
            matchesb_satisfies := _;
        |}.
    Next Obligation.
        destruct b; simpl.
        {
            apply ReflectF.
            intros HContra.
            inversion HContra.
        }
        {
            unfold bool_decide.
            apply iff_reflect.
            ltac1:(case_match; split; intros HH; inversion HH; simplify_eq/=).
            { reflexivity. }
            { 
                unfold satisfies. simpl. assumption.
            }
        }
    Qed.
    Fail Next Obligation.

    #[export]
    Program Instance Matches_bv_ao'
        :
        Matches (Valuation * builtin_value) (AppliedOperator' symbol BuiltinOrVar)
    := {|
        matchesb := fun _ _ => false ;
    |}.
    Next Obligation.
        unfold satisfies. simpl.
        apply ReflectF.
        intros HContra.
        exact HContra.
    Qed.
    Fail Next Obligation.

    #[export]
    Instance
        matches__GroundTerm__OpenTerm
        :
        Matches
            (Valuation * (GroundTerm))
            OpenTerm
    .
    Proof.
        unfold GroundTerm.
        unfold GroundTerm'.
        unfold OpenTerm.
        apply reflect__satisfies__ApppliedOperatorOr'_matches_AppliedOperatorOr'.
    Qed.

End with_signature.

Class ComputableSignature {Σ : Signature} := {
    builtin_unary_predicate_interp_bool :
        builtin_unary_predicate -> GroundTerm -> bool ; 

    builtin_binary_predicate_interp_bool :
        builtin_binary_predicate -> GroundTerm -> GroundTerm -> bool ;         

    cs_up :
        forall p e,
            reflect
                (builtin_unary_predicate_interp p e)
                (builtin_unary_predicate_interp_bool p e) ;

    cs_bp :
        forall p e1 e2,
            reflect
                (builtin_binary_predicate_interp p e1 e2)
                (builtin_binary_predicate_interp_bool p e1 e2) ;
}.

Definition val_satisfies_ap_bool
    `{ComputableSignature}
    (ρ : Valuation)
    (ap : AtomicProposition)
    : bool :=
match ap with
| apeq e1 e2 => 
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    bool_decide (v1 = v2) && isSome v1
| ap1 p e =>
    let v := Expression_evaluate ρ e in
    match v with
    | Some vx => builtin_unary_predicate_interp_bool p vx
    | None => false
    end
| ap2 p e1 e2 =>
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    match v1,v2 with
    | Some vx, Some vy => builtin_binary_predicate_interp_bool p vx vy
    | _,_ => false
    end
end
.

#[export]
Program Instance Matches_val_ap
    `{ComputableSignature}
    : Matches Valuation AtomicProposition
:= {|
    matchesb := val_satisfies_ap_bool ;
|}.
Next Obligation.
    induction b; simpl.
    {
        unfold satisfies.
        simpl.
        unfold is_Some, bool_decide.
        ltac1:(case_match).
        {
            simpl.
            apply iff_reflect.
            split; intros HH.
            {
                destruct HH as [HH1 [x HHx]].
                rewrite HHx.
                reflexivity.
            }
            {
                split.
                {
                    assumption.
                }
                {
                    unfold isSome in *|-.
                    ltac1:(case_match).
                    {
                        exists g. reflexivity.
                    }
                    {
                        inversion HH.
                    }
                }
            }
        }
        {
            simpl.
            apply ReflectF.
            intros [HContra1 [x HContrax]].
            ltac1:(simplify_eq/=).
        }
    }
    {
        unfold satisfies.
        simpl.
        ltac1:(case_match).
        {
            apply cs_up.
        }
        {
            apply ReflectF. intros HContra. exact HContra.
        }
    }
    {
        unfold satisfies.
        simpl.
        ltac1:(repeat case_match).
        {
            apply cs_bp.
        }
        {
            apply ReflectF. intros HContra. exact HContra.
        }
        {
            apply ReflectF. intros HContra. exact HContra.
        }
    }
Qed.
Fail Next Obligation.

Fixpoint val_satisfies_c_bool
    `{ComputableSignature}
    (ρ : Valuation)
    (c : Constraint)
    : bool :=
match c with
| c_True => true
| c_atomic ap => matchesb ρ ap
| c_and c1 c2 => val_satisfies_c_bool ρ c1 && val_satisfies_c_bool ρ c2
| c_not c' => ~~ val_satisfies_c_bool ρ c'
end.

#[export]
Program Instance Matches_val_c
    `{CΣ : ComputableSignature}
    : Matches Valuation Constraint
:= {|
    matchesb := val_satisfies_c_bool ;
|}.
Next Obligation.
    induction b.
    {
        apply ReflectT. exact I.
    }
    {
        unfold satisfies; simpl.
        apply matchesb_satisfies.
    }
    {
        apply reflect_iff in IHb1.
        apply reflect_iff in IHb2.
        unfold satisfies; simpl.
        unfold val_satisfies_c_bool; simpl.
        fold (@val_satisfies_c_bool Σ CΣ).
        unfold satisfies in IHb1.
        unfold satisfies in IHb2.
        simpl in *|-.
        apply iff_reflect.
        rewrite -> IHb1.
        rewrite -> IHb2.
        symmetry.
        apply andb_true_iff.
    }
    {
        apply reflect_iff in IHb.
        unfold satisfies in *; simpl in *.
        apply iff_reflect.
        rewrite IHb.
        split; intros HH.
        {
            apply not_true_is_false in HH.
            rewrite HH.
            reflexivity.
        }
        {
            intros HContra.
            rewrite HContra in HH.
            inversion HH.
        }
    }
Qed.
Fail Next Obligation.

Definition valuation_satisfies_match_bool
    {Σ : Signature}
    (ρ : Valuation)
    (m : Match) : bool :=
match m with
| mkMatch _ x φ =>
    match ρ !! x with
    | Some g
        => matchesb (ρ, g) φ
    | _ => false
    end
end.

#[export]
Program Instance Matches_val_match
    {Σ : Signature}
    :
    Matches Valuation Match
:= {|
    matchesb := valuation_satisfies_match_bool ;
|}.
Next Obligation.
    destruct b; unfold satisfies; simpl.
    ltac1:(case_match).
    {
        apply matchesb_satisfies.
    }
    {
        apply ReflectF.
        ltac1:(tauto).
    }
Qed.
Fail Next Obligation.


Definition valuation_satisfies_sc_bool
    `{CΣ : ComputableSignature}
    (ρ : Valuation)
    (sc : SideCondition) : bool :=
match sc with
| sc_constraint c => matchesb ρ c
| sc_match m => matchesb ρ m
end.

#[export]
Program Instance Matches_valuation_sc
    `{CΣ : ComputableSignature}
    :
    Matches Valuation SideCondition
:= {|
    matchesb := valuation_satisfies_sc_bool;
|}.
Next Obligation.
    destruct b.
    {
        unfold satisfies; simpl.
        apply matchesb_satisfies.
    }
    {
        unfold satisfies; simpl.
        apply matchesb_satisfies.
    }
Qed.
Fail Next Obligation.

#[export]
Program Instance Matches_valuation_scs
   `{CΣ : ComputableSignature}
    :
    Matches Valuation (list SideCondition)
:= {|
    matchesb := fun ρ => forallb (@matchesb Valuation SideCondition Satisfies_val_sc Matches_valuation_sc ρ) ;
|}.
Next Obligation.
    unfold satisfies. simpl.
    unfold valuation_satisfies_scs.
    apply iff_reflect.
    rewrite Forall_forall.
    rewrite forallb_forall.
    split; intros H' x Hin; specialize (H' x Hin).
    {
        eapply introT.
        { apply matchesb_satisfies. }
        {
            apply H'.
        }
    }
    {
        eapply elimT.
        { apply matchesb_satisfies. }
        {
            apply H'.
        }
    }
Qed.
Fail Next Obligation.