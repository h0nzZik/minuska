From Minuska Require Import
    prelude
    spec_syntax
.

Definition Valuation {Σ : Signature}
        := gmap variable GroundTerm
    .

#[export]
Instance VarsOf_valuation
    {Σ : Signature}
    : VarsOf Valuation variable
:= {|
    vars_of := fun ρ => dom ρ ; 
|}.

#[export]
Instance VarsOf_symbol
    {Σ : Signature}
    : VarsOf symbol variable
:= {|
    vars_of := fun _ => ∅ ; 
|}.

#[export]
Instance VarsOf_builtin
    {Σ : Signature}
    : VarsOf builtin_value variable
:= {|
    vars_of := fun _ => ∅ ; 
|}.


(*Transparent Valuation.*)

Fixpoint Expression_evaluate
    {Σ : Signature}
    (ρ : gmap variable GroundTerm)
    (t : Expression)
    : option GroundTerm :=
match t with
| ft_element e => Some e
| ft_variable x => ρ !! x
| ft_unary f t =>
    e ← Expression_evaluate ρ t;
    Some (builtin_unary_function_interp f e)
| ft_binary f t1 t2 =>
    e1 ← Expression_evaluate ρ t1;
    e2 ← Expression_evaluate ρ t2;
    Some (builtin_binary_function_interp f e1 e2)
end.


Lemma Expression_evaluate_extensive_Some
    {Σ : Signature}
    (ρ1 ρ2 : gmap variable GroundTerm)
    (t : Expression)
    (gt : GroundTerm)
    :
    ρ1 ⊆ ρ2 ->
    Expression_evaluate ρ1 t = Some gt ->
    Expression_evaluate ρ2 t = Some gt.
Proof.
    intros Hρ1ρ2.
    revert gt.
    induction t; simpl; intros gt.
    { ltac1:(tauto). }
    {
        unfold vars_of in Hρ1ρ2.
        simpl in Hρ1ρ2.
        intros H.
        eapply (lookup_weaken ρ1 ρ2 x).
        { apply H. }
        { assumption. }
    }
    {
        do 2 (rewrite bind_Some).
        intros [x [Hx1 Hx2]].
        exists x.
        rewrite (IHt _ Hx1).
        split>[reflexivity|].
        assumption.
    }
    {
        do 2 (rewrite bind_Some).
        intros [x [Hx1 Hx2]].
        exists x.
        rewrite (IHt1 _ Hx1).
        split>[reflexivity|].

        rewrite bind_Some in Hx2.
        destruct Hx2 as [x' [Hx'1 Hx'2]].
        rewrite bind_Some.
        exists x'.
        rewrite (IHt2 _ Hx'1).
        split>[reflexivity|].
        assumption.
    }
Qed.

Lemma Expression_evaluate_extensive_None
    {Σ : Signature}
    (ρ1 ρ2 : gmap variable GroundTerm)
    (t : Expression)
    :
    ρ1 ⊆ ρ2 ->
    Expression_evaluate ρ2 t = None ->
    Expression_evaluate ρ1 t = None.
Proof.
    intros Hρ1ρ2.
    induction t; simpl.
    { ltac1:(tauto). }
    {
        unfold vars_of in Hρ1ρ2.
        simpl in Hρ1ρ2.
        intros H.
        eapply (lookup_weaken_None ρ1 ρ2 x).
        { apply H. }
        { assumption. }
    }
    {
        do 2 (rewrite bind_None).
        intros [HNone|Hrest].
        {
            specialize (IHt HNone).
            rewrite IHt.
            left. reflexivity.
        }
        destruct Hrest as [x [Hx1 Hx2]].
        inversion Hx2.
    }
    {
        do 2 (rewrite bind_None).
        intros [HNone|Hrest].
        {
            specialize (IHt1 HNone).
            rewrite IHt1.
            left. reflexivity.
        }
        destruct Hrest as [x [Hx1 Hx2]].
        rewrite bind_None in Hx2.
        destruct Hx2 as [HNone|Hx2].
        {
            specialize (IHt2 HNone).
            destruct (Expression_evaluate ρ1 t1).
            {
                right.
                exists g.
                split>[reflexivity|].
                rewrite bind_None.
                left. exact IHt2.
            }
            {
                left. reflexivity.
            }
        }
        {
            destruct Hx2 as [x2 [Hx21 Hx22]].
            inversion Hx22.
        }
    }
Qed.


Lemma Expression_evaluate_extensive'
    {Σ : Signature}
    (ρ1 ρ2 : gmap variable GroundTerm)
    (t : Expression)
    :
    ρ1 ⊆ ρ2 ->
    isSome (Expression_evaluate ρ1 t) ->
    Expression_evaluate ρ1 t = Expression_evaluate ρ2 t.
Proof.
    intros H1 H2.
    unfold isSome in H2.
    ltac1:(case_match).
    {
        symmetry.
        eapply Expression_evaluate_extensive_Some in H>[|apply H1].
        assumption.
    }
    {
        inversion H2.
    }
Qed.

Class Satisfies
    {Σ : Signature}
    (V A B : Type)
    `{SubsetEq V}
    {_VV: VarsOf V variable}
    :=
mkSatisfies {
    satisfies :
        V -> A -> B -> Prop ;

    satisfies_ext :
        forall (v1 v2 : V),
            v1 ⊆ v2 ->
            forall a b,
                satisfies v1 a b ->
                satisfies v2 a b ;
}.

Arguments satisfies : simpl never.

Definition val_satisfies_ap
    {Σ : Signature} (ρ : Valuation) (ap : AtomicProposition)
    : Prop :=
match ap with
| apeq e1 e2 => 
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    v1 = v2 /\ is_Some v1
| ap1 p e =>
    let v := Expression_evaluate ρ e in
    match v with
    | Some vx => builtin_unary_predicate_interp p vx
    | None => False
    end
| ap2 p e1 e2 =>
    let v1 := Expression_evaluate ρ e1 in
    let v2 := Expression_evaluate ρ e2 in
    match v1,v2 with
    | Some vx, Some vy => builtin_binary_predicate_interp p vx vy
    | _,_ => False
    end
end
.

#[export]
Program Instance Satisfies_val_ap
    {Σ : Signature} :
    Satisfies
        (gmap variable GroundTerm)
        unit
        AtomicProposition
:= {|
    satisfies := fun ρ u ap => val_satisfies_ap ρ ap ;
|}.
Next Obligation.
    destruct b; simpl in *.
    {
        destruct H0 as [H1 [x Hx]].
        rewrite (Expression_evaluate_extensive_Some v1 v2 _ x H Hx).
        split>[|eexists; reflexivity].
        rewrite H1 in Hx.
        rewrite (Expression_evaluate_extensive_Some v1 v2 e2 x H Hx).
        reflexivity.
    }
    {
        destruct (Expression_evaluate v1 e1) eqn:Heq1, (Expression_evaluate v2 e1) eqn:Heq2.
        {
            rewrite (Expression_evaluate_extensive_Some v1 v2 e1 g H Heq1) in Heq2.
            inversion Heq2; subst; clear Heq2.
            assumption.
        }
        {
            apply (Expression_evaluate_extensive_None) with (ρ1 := v1) in Heq2.
            {
                ltac1:(simplify_eq/=).
            }
            { assumption. }
        }
        {
            inversion H0.
        }
        {
            inversion H0.
        }
    }
    {
        destruct
            (Expression_evaluate v1 e1) eqn:Heq1,
            (Expression_evaluate v2 e1) eqn:Heq2,
            (Expression_evaluate v1 e2) eqn:Heq3,
            (Expression_evaluate v2 e2) eqn:Heq4;
            try ltac1:(contradiction).
        {
            rewrite (Expression_evaluate_extensive_Some v1 v2 e1 g H Heq1) in Heq2.
            inversion Heq2; subst; clear Heq2.
            rewrite (Expression_evaluate_extensive_Some v1 v2 e2 g1 H Heq3) in Heq4.
            inversion Heq4; subst; clear Heq4.
            assumption.
        }
        {
            apply (Expression_evaluate_extensive_None) with (ρ1 := v1) in Heq4.
            {
                ltac1:(simplify_eq/=).
            }
            { assumption. }
        }
        {
            apply (Expression_evaluate_extensive_None) with (ρ1 := v1) in Heq2.
            {
                ltac1:(simplify_eq/=).
            }
            { assumption. }
        }
        {
            apply (Expression_evaluate_extensive_None) with (ρ1 := v1) in Heq2.
            {
                ltac1:(simplify_eq/=).
            }
            { assumption. }
        }
    }
Qed.
Fail Next Obligation.

Fixpoint val_satisfies_c
    {Σ : Signature} (ρ : Valuation) (c : Constraint)
    : Prop :=
match c with
| c_True => True
| c_atomic ap => satisfies ρ () ap
| c_and c1 c2 => val_satisfies_c ρ c1 /\ val_satisfies_c ρ c2
(* | c_not c' => ~ val_satisfies_c ρ c' *)
end.

#[export]
Program Instance Satisfies_val_c
    {Σ : Signature} : Satisfies (gmap variable GroundTerm) unit Constraint
:= {|
    satisfies := fun a b c => val_satisfies_c a c;
|}.
Next Obligation.
    induction b; simpl in *.
    { exact I. }
    {
        eapply satisfies_ext.
        { exact H. }
        { assumption. }
    }
    {
        ltac1:(naive_solver).
    }
Qed.
Fail Next Obligation.


Inductive aoxy_satisfies_aoxz
    {Σ : Signature}
    {V X Y Z : Type}
    {_VV : VarsOf V variable}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z}
    {_S2 : Satisfies V (Y) (AppliedOperator' X Z)}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) Z }

    :
    V ->
    ((AppliedOperator' X Y)) ->
    AppliedOperator' X Z ->
    Prop :=

| asa_x:
    forall ρ x,
        aoxy_satisfies_aoxz
            ρ
            (@ao_operator X Y x)
            (@ao_operator X Z x)

| asa_operand:
    forall ρ aoxy aoxz y z,
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ y z ->
        aoxy_satisfies_aoxz
            ρ
            (ao_app_operand aoxy y)
            (ao_app_operand aoxz z)

| asa_operand_asa:
    forall ρ aoxy aoxz aoxy2 z,
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ aoxy2 z ->
        aoxy_satisfies_aoxz
        (* The right-side, the symbolic one, has more compact representation - so *)
            ρ
            (ao_app_ao aoxy aoxy2)
            (ao_app_operand aoxz z)

| asa_asa_operand:
    forall
        (ρ : V)
        (aoxy : AppliedOperator' X Y)
        (aoxz aoxz2 : AppliedOperator' X Z)
        (y : Y),
        aoxy_satisfies_aoxz ρ aoxy aoxz ->
        satisfies ρ y aoxz2 ->
        aoxy_satisfies_aoxz
            ρ
            (ao_app_operand aoxy y)
            ((ao_app_ao aoxz aoxz2))

| asa_asa:
    forall ρ aoxy1 aoxy2 aoxz1 aoxz2,
        aoxy_satisfies_aoxz ρ aoxy1 aoxz1 ->
        aoxy_satisfies_aoxz ρ aoxy2 aoxz2 ->
        aoxy_satisfies_aoxz
            ρ
            (ao_app_ao aoxy1 aoxy2)
            (ao_app_ao aoxz1 aoxz2)
.


#[export]
Program Instance Satisfies_aoxy_aoxz
    {Σ : Signature}
    {V X Y Z : Type}
    {_VV : VarsOf V variable}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z}
    {_S2 : Satisfies V (Y) (AppliedOperator' X Z)}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) Z }
    :
    Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z)
:= {|
    satisfies := aoxy_satisfies_aoxz ;
|}.
Next Obligation.
    revert v2 H.
    induction H0; intros v2 HH; constructor; try (ltac1:(naive_solver)).
    {
        eapply satisfies_ext.
        { apply HH. }
        { exact H. }
    }
    {
        eapply satisfies_ext.
        { apply HH. }
        { exact H. }
    }
    {
        eapply satisfies_ext.
        { apply HH. }
        { exact H. }
    }
Qed.
Fail Next Obligation.


Inductive aoxyo_satisfies_aoxzo
    {Σ : Signature}
    (V X Y Z : Type)
    {_VV : VarsOf V variable}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z}
    {_S2 : Satisfies V ((AppliedOperator' X Y)) Z}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z)}
    : V ->
        ((AppliedOperatorOr' X Y)) ->
        (AppliedOperatorOr' X Z) ->
        Prop
:=
| axysaxz_app:
    forall
        (ρ : V)
        (xy : AppliedOperator' X Y)
        (xz : AppliedOperator' X Z)
        (pf : satisfies ρ xy xz),
        aoxyo_satisfies_aoxzo V X Y Z ρ (@aoo_app _ _  xy) (aoo_app _ _ xz)

| axysaxz_operand:
    forall (ρ : V) (y : Y) (z : Z) (pf : satisfies ρ y z),
        aoxyo_satisfies_aoxzo V X Y Z ρ (@aoo_operand X Y y) (@aoo_operand X Z z)

| axysaxz_combined:
    forall (ρ : V) axy axz,
        satisfies ρ axy axz ->
        aoxyo_satisfies_aoxzo V X Y Z ρ (@aoo_app _ _  axy) (@aoo_operand X Z axz)
.

#[export]
Program Instance Satisfies_aoxyo_aoxzo
    {Σ : Signature}
    (V X Y Z : Type)
    {_VV : VarsOf V variable}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z}
    {_S2 : Satisfies V ((AppliedOperator' X Y)) Z}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z)}
    :
    Satisfies V ((AppliedOperatorOr' X Y)) (AppliedOperatorOr' X Z)
:= {|
    satisfies := aoxyo_satisfies_aoxzo V X Y Z;
|}.
Next Obligation.
    destruct H0; constructor.
    {
        eapply satisfies_ext.
        { exact H. }
        { exact pf. }
    }
    {
        eapply satisfies_ext.
        { exact H. }
        { exact pf. }
    }
    {
        eapply satisfies_ext.
        { exact H. }
        { assumption. }
    }
Qed.
Fail Next Obligation.

Inductive builtin_satisfies_BuiltinOrVar
    {Σ : Signature}
    (ρ : Valuation)
    :
    builtin_value ->
    BuiltinOrVar ->
    Prop :=

| bsbv_builtin:
    forall b,
        builtin_satisfies_BuiltinOrVar ρ b (bov_builtin b)

| bsbv_var:
    forall (b : builtin_value) (x : variable),
        ρ !! x = Some (@aoo_operand symbol builtin_value b) ->
        builtin_satisfies_BuiltinOrVar ρ b (bov_variable x)
.

Definition builtin_satisfies_BuiltinOrVar'
    {Σ : Signature}
    (ρ : Valuation)
    (b : builtin_value)
    (bov : BuiltinOrVar)
    : Prop
:= builtin_satisfies_BuiltinOrVar ρ b bov.

#[export]
Instance Subseteq_Valuation {Σ : Signature}
    : SubsetEq Valuation
.
Proof.
    unfold Valuation.
    apply _.
Defined.

#[export]
Program Instance Satisfies_builtin_BuiltinOrVar
    {Σ : Signature}
    :
    Satisfies Valuation (builtin_value) BuiltinOrVar
:= {|
    satisfies := builtin_satisfies_BuiltinOrVar' ;
|}.
Next Obligation.
    inversion H0; constructor.
    {
        subst.
        unfold Valuation in *.
        eapply lookup_weaken.
        { apply H1. }
        { assumption. }
    }
Qed.
Fail Next Obligation.

Definition AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar
    {Σ : Signature}
    (ρ : Valuation)
    (aop : AppliedOperator' symbol builtin_value)
    (bov : BuiltinOrVar)
    : Prop :=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app symbol builtin_value aop)
end.

#[export]
Program Instance Satisfies__AppliedOperator'_symbol_builtin__BuiltinOrVar
    {Σ : Signature}
    : Satisfies Valuation ((AppliedOperator' symbol builtin_value)) BuiltinOrVar
:= {| 
    satisfies := AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar
|}.
Next Obligation.
    destruct b; simpl in *.
    { ltac1:(contradiction). }
    {
        unfold Valuation in *.
        eapply lookup_weaken.
        { apply H0. }
        { assumption. }
    }
Qed.
Fail Next Obligation.

Definition AppliedOperator'_symbol_builtin_satisfies'_BuiltinOrVar
    {Σ : Signature}
    (ρ : Valuation)
    (aop : (AppliedOperator' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Prop
:= AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ aop bov.

#[export]
Program Instance Satisfies_AppliedOperator'_symbol_builtin_BuiltinOrVar
    {Σ : Signature}
    :
    Satisfies Valuation ((AppliedOperator' symbol builtin_value)) BuiltinOrVar
:= {|
    satisfies := AppliedOperator'_symbol_builtin_satisfies'_BuiltinOrVar ;
|}.
Next Obligation.
    destruct b; simpl in *.
    { ltac1:(contradiction). }
    {
        unfold Valuation in *.
        eapply lookup_weaken.
        { apply H0. }
        { assumption. }
    }
Qed.
Fail Next Obligation.

Definition aosb_satisfies_aosbf
    {Σ : Signature}
    {A B : Type}
    {_S1 : Satisfies Valuation (A) B}
    {_S2 : Satisfies Valuation (A) (AppliedOperator' symbol B)}
    {_S3 : Satisfies Valuation ((AppliedOperator' symbol A)) B}
    :
    Valuation ->
    ((AppliedOperator' symbol A)) ->
    AppliedOperator' symbol B ->
    Prop :=
    @aoxy_satisfies_aoxz
        Σ
        Valuation
        symbol
        A
        B
        _
        _
        _
        _
        _
.

#[export]
Program Instance Satisfies__builtin__ao'B
    {Σ : Signature}
    {B : Type}
    :
    Satisfies
        Valuation
        (builtin_value)
        (AppliedOperator' symbol B)
:= {| 
    satisfies := fun _ _ _ => false ;
|}.

#[export]
Instance Satisfies_aos__builtin_BuiltinOrVar
    {Σ : Signature}
    :
    Satisfies Valuation ((AppliedOperator' symbol builtin_value)) (AppliedOperator' symbol BuiltinOrVar)
.
Proof.
    apply _.
Defined.


#[export]
Instance Satisfies_aosb_aosbf
    {Σ : Signature}
    {A B : Type}
    {SatAB : Satisfies Valuation (A) B}
    {_S2 : Satisfies Valuation (A) (AppliedOperator' symbol B)}
    {SatA'B : Satisfies Valuation ((AppliedOperator' symbol A)) B}
    :
    Satisfies Valuation ((AppliedOperator' symbol A)) (AppliedOperator' symbol B)
.
Proof.
    apply _.
Defined.


Definition aoosb_satisfies_aoosbf
    {Σ : Signature}
    :
    Valuation ->
    (AppliedOperatorOr' symbol builtin_value) ->
    AppliedOperatorOr' symbol BuiltinOrVar ->
    Prop :=
    aoxyo_satisfies_aoxzo
        Valuation
        symbol
        builtin_value
        BuiltinOrVar
.

#[export]
Instance
Satisfies_aoosb_aoosbf
    {Σ : Signature}
    :
    Satisfies Valuation ((AppliedOperatorOr' symbol builtin_value)) (AppliedOperatorOr' symbol BuiltinOrVar)
.
Proof. apply _. Defined.

Definition in_val_GroundTerm_satisfies_OpenTerm
    {Σ : Signature}
    (ρ : Valuation)
    (g : GroundTerm)
    (φ : OpenTerm)
    : Prop := aoosb_satisfies_aoosbf ρ g φ
.

#[export]
Instance Satisfies_valGroundTerm_OpenTerm
    {Σ : Signature}
    :
    Satisfies Valuation (GroundTerm) OpenTerm
.
Proof. apply _. Defined.

Definition valuation_satisfies_match
    {Σ : Signature}
    (ρ : Valuation)
    (m : Match) : Prop :=
match m with
| mkMatch _ x φ =>
    match ρ !! x with
    | Some g
        => satisfies ρ g φ
    | _ => False
    end
end.

#[export]
Program Instance Satisfies_val_match
    {Σ : Signature}
    :
    Satisfies Valuation unit Match
:= {|
    satisfies := fun a b c => valuation_satisfies_match a c;
|}.
Next Obligation.
    destruct b. simpl in *.
    unfold Valuation in *.
    ltac1:(repeat case_match).
    {
        eapply lookup_weaken in H1>[|apply H].
        ltac1:(simplify_eq/=).
        eapply satisfies_ext.
        { apply H. }
        { assumption. }
    }
    {
        eapply lookup_weaken in H1>[|apply H].
        ltac1:(simplify_eq/=).
    }
    {
        ltac1:(contradiction).
    }
    {
        ltac1:(contradiction).
    }
Qed.
Fail Next Obligation.

Definition valuation_satisfies_sc
    {Σ : Signature}
    (ρ : Valuation)
    (sc : SideCondition) : Prop :=
match sc with
| sc_constraint c => satisfies ρ () c
| sc_match m => satisfies ρ () m
end.

#[export]
Program Instance Satisfies_val_sc
    {Σ : Signature}
    :
    Satisfies Valuation unit SideCondition
:= {|
    satisfies := fun a b c => valuation_satisfies_sc a c ;
|}.
Next Obligation.
    destruct b; simpl in *; eapply satisfies_ext>[apply H|]; assumption.
Qed.
Fail Next Obligation.

Inductive A_satisfies_B_WithASideCondition
    {Σ : Signature}
    (V A B : Type)
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {_S1 : Satisfies V unit SideCondition}
    {_S2 : Satisfies V (A) B}
    : V -> A -> WithASideCondition B -> Prop :=

| asbwsc_base:
    forall ρ a (b : B),
        satisfies ρ a b ->
        A_satisfies_B_WithASideCondition V A B ρ a (wsc_base b)

| asbwsc_sc :
    forall ρ a (bsc : WithASideCondition B) sc,
        A_satisfies_B_WithASideCondition V A B ρ a bsc ->
        satisfies ρ () sc ->
        A_satisfies_B_WithASideCondition V A B ρ a (wsc_sc bsc sc)
.

#[export]
Program Instance Satisfies_A_Bsc
    {Σ : Signature}
    {V A B : Type}
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {_S1 : Satisfies V unit SideCondition}
    {_S2 : Satisfies V A B}
    :
    Satisfies V A (WithASideCondition B)
:= {|
    satisfies :=
        A_satisfies_B_WithASideCondition
        V A B;
|}.
Next Obligation.
    induction H0; constructor; try (ltac1:(naive_solver));
        eapply satisfies_ext>[apply H|]; assumption.
Qed.
Fail Next Obligation.

Definition GroundTerm_satisfies_BuiltinOrVar
    {Σ : Signature}
    (ρ : Valuation)
    (g : GroundTerm)
    (bov : BuiltinOrVar)
    : Prop :=
match bov with
| bov_builtin b =>
    match g with
    | aoo_app _ _ _ => False
    | aoo_operand _ _ b' => b = b'
    end
| bov_variable x => ρ !! x = Some g
end.

#[export]
Program Instance Satisfies_GroundTerm_BuiltinOrVar
    {Σ : Signature}
    :
    Satisfies Valuation (GroundTerm) BuiltinOrVar
:= {|
    satisfies := GroundTerm_satisfies_BuiltinOrVar ;
|}.
Next Obligation.
    destruct a,b; simpl in *; try ltac1:(naive_solver);
        unfold Valuation in *; eapply lookup_weaken>[|apply H];
        assumption.
Qed.
Fail Next Obligation.

Definition in_val_GroundTerm_satisfies_OpenTermWSC
    {Σ : Signature}
    :
    Valuation ->
    GroundTerm ->
    OpenTermWSC ->
    Prop :=
    A_satisfies_B_WithASideCondition
        Valuation
        GroundTerm
        OpenTerm
.

#[export]
Instance Satisfies_GroundTerm_OpenTermWSC
    {Σ : Signature}
    :
    Satisfies Valuation (GroundTerm) OpenTermWSC
.
Proof. apply _. Defined.

Definition builtin_value_satisfies_OpenTerm
    {Σ : Signature}
    :
    Valuation ->
    builtin_value ->
    OpenTerm ->
    Prop := fun ρ b t =>
match t with
| aoo_app _ _ _ => False
| aoo_operand _ _ bov =>
    satisfies ρ b bov
end.

#[export]
Program Instance Satisfies_builtin_value_OpenTerm
    {Σ : Signature}
    :
    Satisfies Valuation (builtin_value) OpenTerm
:= {|
    satisfies :=  builtin_value_satisfies_OpenTerm ;
|}.
Next Obligation.
    destruct b; simpl in *.
    { assumption. }
    {
        eapply satisfies_ext>[apply H|].
        assumption.
    }
Qed.
Fail Next Obligation.

Definition builtin_value_satisfies_OpenTermWSC
    {Σ : Signature}
    :
    Valuation ->
    builtin_value ->
    OpenTermWSC ->
    Prop :=
    A_satisfies_B_WithASideCondition
        Valuation
        builtin_value
        OpenTerm
.

#[export]
Instance Satisfies_builtin_value_OpenTermWSC
    {Σ : Signature}
    :
    Satisfies Valuation builtin_value OpenTermWSC
.
Proof. apply _. Defined.

Definition AppliedOperator'_symbol_builtin_value_satisfies_BOV
    {Σ : Signature}
    (ρ : Valuation)
    (ao : (AppliedOperator' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Prop
:=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app _ _ ao) 
end
.

#[export]
Program Instance Satisfies__AppliedOperator'_symbol_builtin_value__BOV
    {Σ : Signature}
    {V : Type}
    :
    Satisfies Valuation ((AppliedOperator' symbol builtin_value)) BuiltinOrVar
:= {|
    satisfies := AppliedOperator'_symbol_builtin_value_satisfies_BOV;
|}.
Next Obligation.
    destruct b; simpl in *; try assumption.
    {
        unfold Valuation in *.
        eapply lookup_weaken.
        { apply H0. }
        { assumption. }
    }
Qed.
Fail Next Obligation.

Definition AppliedOperator'_symbol_A_satisfies_OpenTermB'
    {Σ : Signature}
    (V A B : Type)
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {_S1 : Satisfies V (A) B}
    {_S2 : Satisfies V ((AppliedOperator' symbol A)) B}
    {_S3 : Satisfies V (AppliedOperator' symbol A) (AppliedOperator' symbol B)}
    :
    V ->
    (AppliedOperator' symbol A) ->
    AppliedOperatorOr' symbol B ->
    Prop
:=  fun ρ a =>
    satisfies
    ρ (aoo_app _ _ a)
.

#[export]
Program Instance Satisfies__lift_builtin_to_aosb
    {Σ : Signature}
    {V A B : Type}
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {_S1 : Satisfies V (A) B}
    {_S2 : Satisfies V ((AppliedOperator' symbol A)) B}
    {_S3 : Satisfies V (AppliedOperator' symbol A) (AppliedOperator' symbol B)}
    :
    Satisfies
        V
        ((AppliedOperator' symbol A))
        (AppliedOperatorOr' symbol B)
:= {|
    satisfies :=
        AppliedOperator'_symbol_A_satisfies_OpenTermB' V A B ;
|}.
Next Obligation.
    unfold AppliedOperator'_symbol_A_satisfies_OpenTermB' in *.
    eapply satisfies_ext.
    { apply H. }
    { assumption. }
Qed.    
Fail Next Obligation.

#[export]
Instance Satisfies__lift_builtin_to_aosbo
    {Σ : Signature}
    {V A B : Type}
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {bsB : Satisfies V (A) B}
    {sat2 : Satisfies V ((AppliedOperator' symbol A)) B}
    {sat3 : Satisfies V ((AppliedOperator' symbol A)) (AppliedOperator' symbol B)}
    :
    Satisfies V
        ((AppliedOperatorOr' symbol A))
        (AppliedOperatorOr' symbol B)
.
Proof. apply _. Defined.

Definition AppliedOperator'_symbol_builtin_satisfies_OpenTerm
    {Σ : Signature}
    {V : Type}
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) BuiltinOrVar}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol BuiltinOrVar)}
    :
    V ->
    ((AppliedOperator' symbol builtin_value)) ->
    OpenTerm ->
    Prop
:=  fun ρ a =>
    satisfies ρ (aoo_app _ _ a)
.

#[export]
Program Instance Satisfies__AppliedOperator'_symbol_builtin__OpenTerm
    {Σ : Signature}
    {V : Type}
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) BuiltinOrVar}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol BuiltinOrVar)}
    :
    Satisfies V
        ((AppliedOperator' symbol builtin_value))
        OpenTerm
:= {|
    satisfies :=
        AppliedOperator'_symbol_builtin_satisfies_OpenTerm ;
|}.
Next Obligation.
    eapply satisfies_ext.
    { apply H. }
    { assumption. }
Qed.
Fail Next Obligation.

#[export]
Instance Satisfies__AppliedOperator'_symbol_builtin__OpenTermWSC
    {Σ : Signature}
    :
    Satisfies
        Valuation (AppliedOperator' symbol builtin_value)
        OpenTermWSC
.
Proof. apply _. Defined.


#[export]
Instance Satisfies__GroundTerm__LhsPattern
    {Σ : Signature}
    {V : Type}
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {_S1 : Satisfies V (builtin_value) OpenTermWSC}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) OpenTermWSC}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol OpenTermWSC)}
    :
    Satisfies
        V
        (GroundTerm)
        LhsPattern
.
Proof. apply _. Defined.

#[local]
Obligation Tactic := idtac.

#[export]
Program Instance Satisfies_builtin_expr
    {Σ : Signature}:
    Satisfies Valuation (builtin_value) Expression
:= {|
    satisfies := (fun ρ b e =>
        Expression_evaluate ρ e = Some (aoo_operand _ _ b)
    ) ;
|}.
Next Obligation.
    intros. simpl in *.
    erewrite Expression_evaluate_extensive_Some>[|apply H|].
    { reflexivity. }
    { assumption. }
Qed.
Fail Next Obligation.

#[export]
Program Instance Satisfies_asb_expr
    {Σ : Signature}:
    Satisfies
        Valuation
        ((AppliedOperator' symbol builtin_value))
        Expression
:= {|
    satisfies := (fun ρ x e =>
        Expression_evaluate ρ e = Some (aoo_app _ _ x)
    ) ;
|}.
Next Obligation.
    intros. simpl in *.
    erewrite Expression_evaluate_extensive_Some>[|apply H|].
    { reflexivity. }
    { assumption. }
Qed.
Fail Next Obligation.

(*
Definition GroundTerm_satisfies_RhsPattern
    {Σ : Signature}
    {V : Type}
    `{Satisfies (V * builtin_value) Expression}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) Expression}
    `{Satisfies (V * AppliedOperator' symbol builtin_value) (AppliedOperator' symbol Expression)}
    :
    (V*GroundTerm) -> RhsPattern -> Prop
:= aoxyo_satisfies_aoxzo
    V
    symbol
    builtin_value
    Expression
.
*)

#[export]
Instance Satisfies__GroundTerm__RhsPattern
    {Σ : Signature}
    {V : Type}
    {_SV : SubsetEq V}
    {_VV : VarsOf V variable}
    {_S1 : Satisfies V (builtin_value) Expression}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) Expression}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol Expression)}
    :
    Satisfies
        V (GroundTerm)
        RhsPattern
.
Proof. apply _. Defined.

#[export]
Program Instance Satisfies_gt_var
    {Σ : Signature}:
    Satisfies Valuation (GroundTerm) variable
:= {|
    satisfies := (fun ρ g x => ρ !! x = Some g)
|}.
Next Obligation.
    intros. simpl in *.
    unfold Valuation in *.
    eapply lookup_weaken.
    { apply H0. }
    { assumption. }
Qed.
Fail Next Obligation.

#[export]
Instance Satisfies__GroundTerm__VarWithSc
    {Σ : Signature}
    :
    Satisfies
        Valuation
        (GroundTerm)
        (WithASideCondition variable)
.
Proof. apply _. Defined.


Definition GroundTerm_satisfies_LocalRewrite
    {Σ : Signature}
    (ρd : (Valuation*LeftRight))
    (g : GroundTerm)
    (r : LocalRewrite)
    : Prop :=
match ρd.2 with
| LR_Left => satisfies ρd.1 g (lr_from r)
| LR_Right => satisfies ρd.1 g (lr_to r)
end.

#[export]
Instance Subseteq_ValuationLR
    {Σ : Signature}
    : SubsetEq (Valuation * LeftRight)
:= {
    subseteq a b := subseteq a.1 b.1 /\ a.2 = b.2
}.


(* TODO *)
#[export]
Instance VarsOf_ValuationLR
    {Σ : Signature}
    : VarsOf (Valuation * LeftRight) variable
:= {
    vars_of a := vars_of a.1
}.

#[export]
Program Instance Satisfies__GroundTerm__LocalRewrite
    {Σ : Signature}
    :
    Satisfies
        (Valuation*LeftRight)
        (GroundTerm)
        (LocalRewrite)
:= {|
    satisfies := 
        GroundTerm_satisfies_LocalRewrite
        ;
|}.
Next Obligation.
    intros.
    unfold Valuation, GroundTerm_satisfies_LocalRewrite in *.
    destruct v1,v2; simpl in *.
    destruct l,l0; simpl in *; eapply satisfies_ext>[apply H|];
        simpl; try assumption.
    {
        inversion H; subst; clear H. simpl in *. inversion H2.
    }
    {
        inversion H; subst; clear H. simpl in *. inversion H2.
    }
Qed.
Fail Next Obligation.

Definition GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    (ρd : (Valuation*LeftRight))
    (g : GroundTerm)
    (rb : LocalRewriteOrOpenTermOrBOV)
    : Prop :=
let ρ := ρd.1 in
match rb with
| lp_rewrite r
    => satisfies ρd g r
| lp_basicpat φ
    => satisfies ρ g φ
| lp_bov bx
    => satisfies ρ g bx
end.

#[export]
Program Instance Satisfies__GroundTerm__LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    :
    Satisfies
        (Valuation*LeftRight)
        (GroundTerm)
        (LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies :=
        GroundTerm_satisfies_LocalRewriteOrOpenTermOrBOV
        ;
|}.
Next Obligation.
    intros. destruct b; simpl in *;
        eapply satisfies_ext>[apply H|]; simpl; assumption.
Qed.
Fail Next Obligation.

Definition builtin_satisfies_LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    (ρd : (Valuation*LeftRight))
    (b : builtin_value)
    (r : LocalRewriteOrOpenTermOrBOV)
    : Prop :=
let ρ := ρd.1 in
match r with
| lp_rewrite r'
    => satisfies (ρd) (aoo_operand _ _ b) r'

| lp_basicpat (aoo_app _ _ _)
    => False

| lp_basicpat (aoo_operand _ _ bov)
    => satisfies ρ b bov

| lp_bov bx
    => satisfies ρ b bx
end.

#[export]
Program Instance Satisfies__builtin_value__LocalRewriteOrOpenTermOrBOV
    {Σ : Signature}
    :
    Satisfies
        (Valuation*LeftRight)
        (builtin_value)
        (LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies :=
        builtin_satisfies_LocalRewriteOrOpenTermOrBOV
        ;
|}.
Next Obligation.
    intros. destruct v1,v2,b; simpl in *;
        inversion H; subst; simpl in *;
        subst.
    {
        eapply satisfies_ext.
        { apply H. }
        { assumption. }
    }
    {
        destruct φ.
        { ltac1:(contradiction). }
        eapply satisfies_ext>[apply H1|].
        { assumption. }
    }
    {
        eapply satisfies_ext>[apply H1|].
        { assumption. }
    }
Qed.
Fail Next Obligation.

(*
#[export]
Instance satLift1
    {Σ : Signature}
    {L R : Type}
    `{Satisfies (Valuation * L) R}
    :
    Satisfies
        ((Valuation * LeftRight) * L) R
:= {|
    satisfies := fun ρdg r => satisfies (ρdg.1.1,ρdg.2) r
|}.*)
(*
#[export] Instance _tmp
    {Σ : Signature}
    :
    Satisfies
        (Valuation * LeftRight * AppliedOperator' symbol builtin_value)
        LocalRewriteOrOpenTermOrBOV
:= {|
    satisfies := fun ρdg => satisfies (ρdg.1.1,ρdg.1.2, aoo_app _ _ ρdg.2)
|}.
*)

#[export]
Program Instance Satisfies_vlrglrootob
    {Σ : Signature}:
    Satisfies
        (Valuation * LeftRight)
        (AppliedOperator' symbol builtin_value)
        LocalRewriteOrOpenTermOrBOV
:= {|
    satisfies := fun ρd g =>
        satisfies ρd (aoo_app _ _ g)
        
     ;
|}.
Next Obligation.
    intros. simpl in *.
    eapply satisfies_ext>[apply H|]. assumption.
Qed.
Fail Next Obligation.


#[export]
Program Instance Satisfies_vlrblrootob
    {Σ : Signature}:
    Satisfies
        (Valuation * LeftRight)
        (builtin_value)
        (AppliedOperator' symbol LocalRewriteOrOpenTermOrBOV)
:= {|
    satisfies := fun _ _ _ => False ;
|}.
Next Obligation.
    intros. simpl in *. assumption.
Qed.
Fail Next Obligation.


#[export]
Program Instance Satisfies_sym_bov
    {Σ : Signature}
    :
    Satisfies Valuation (symbol) BuiltinOrVar
:= {|
    satisfies := fun _ _ _ => False ;
|}.
Next Obligation.
    simpl. auto with nocore.
Qed.
Fail Next Obligation.

#[export]
Instance Satisfies_aop_lrw {Σ : Signature}:
    Satisfies
        (Valuation * LeftRight)
        (AppliedOperator' symbol builtin_value)
        (AppliedOperator' symbol LocalRewriteOrOpenTermOrBOV)
.
Proof. apply _. Defined.

#[export]
Instance Satisfies__GroundTerm__UncondRewritingRule
    {Σ : Signature}
    :
    Satisfies
        (Valuation*LeftRight)
        (GroundTerm)
        (UncondRewritingRule)
.
Proof. apply _. Defined.

#[export]
Program Instance Satisfies_Valuation_LR_SideCondition
    {Σ : Signature}
    :
    Satisfies (Valuation * LeftRight) unit SideCondition
:= {|
    satisfies := fun ρd => let ρ := ρd.1 in
        satisfies ρ
        ;
|}.
Next Obligation.
    simpl. intros.
    inversion H; subst.
    eapply satisfies_ext.
    { apply H1. }
    { assumption. }
Qed.
Fail Next Obligation.

#[export]
Instance Satisfies__GroundTerm__RewritingRule
    {Σ : Signature}
    :
    Satisfies
        (Valuation*LeftRight)
        (GroundTerm)
        (RewritingRule)
.
Proof. apply _. Defined.

Definition GroundTerm_satisfies_OpenTerm
    {Σ : Signature}
    : GroundTerm -> OpenTerm -> Prop :=
    fun g φ => ∃ ρ, satisfies ρ g φ
.

#[export]
Instance VarsOf_unit {Σ : Signature}: VarsOf unit variable := {|
    vars_of _ := ∅ ;
|}.

#[export]
Instance Subseteq_unit {Σ : Signature}: SubsetEq unit := 
    fun _ _ => true
.

#[export]
Program Instance Satisfies__GroundTerm__OpenTerm_inall
    {Σ : Signature}
    :
    Satisfies
        unit
        GroundTerm
        OpenTerm
:= {|
    satisfies := fun _ => GroundTerm_satisfies_OpenTerm ;
|}.
Next Obligation.
    simpl. intros. assumption.
Qed.
Fail Next Obligation.


(*
#[export]
Instance Satisfies_bv_ao'
    {Σ : Signature}
    :
    Satisfies (Valuation * builtin_value) (AppliedOperator' symbol BuiltinOrVar)
:= {|
    satisfies := fun _ _ => False ;
|}.
*)

Definition rewrites_in_valuation_to
    {Σ : Signature}
    (ρ : Valuation)
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= satisfies (ρ,LR_Left) (from) r
/\ satisfies (ρ,LR_Right) (to) r
.

Definition rewrites_to
    {Σ : Signature}
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= exists ρ, rewrites_in_valuation_to ρ r from to
.

Definition RewritingTheory {Σ : Signature}
    := list RewritingRule
.

Definition rewriting_relation
    {Σ : Signature}
    (Γ : RewritingTheory)
    : relation GroundTerm
    := fun from to =>
        exists r, r ∈ Γ /\ rewrites_to r from to
.

Definition not_stuck
    {Σ : Signature}
    (Γ : RewritingTheory)
    (e : GroundTerm) : Prop
:= exists e', rewriting_relation Γ e e'.

Definition stuck
    {Σ : Signature}
    (Γ : RewritingTheory)
    (e : GroundTerm) : Prop
:= not (not_stuck Γ e).

Definition rule_weakly_well_defined
    {Σ : Signature}
    (r : RewritingRule)
    : Prop
    := ∀ ρ from,
        satisfies (ρ,LR_Left) (from) r ->
        ∃ to, satisfies (ρ,LR_Right) (to) r
.

Definition thy_weakly_well_defined
    {Σ : Signature}
    (Γ : RewritingTheory)
    : Prop
    := ∀ r, r ∈ Γ -> rule_weakly_well_defined r
.


#[export]
Program Instance Satisfies_valuation_scs
    {Σ : Signature}
    : Satisfies Valuation unit (list SideCondition)
:= {|
    satisfies := fun ρ _ => Forall (satisfies ρ ());
|}.
Next Obligation.
    intros. simpl in *.
    rewrite Forall_forall. rewrite Forall_forall in H0.
    intros x Hx. specialize (H0 x Hx).
    eapply satisfies_ext.
    { apply H. }
    { assumption. }
Qed.
Fail Next Obligation.

(*
#[export]
Instance Satisfies_bv_pureterm
    {Σ : Signature}:
    Satisfies (Valuation * builtin_value)
    (AppliedOperator' symbol Expression)
:= {|
    satisfies := fun _ _ => False;
|}.
*)
#[export]
Program Instance
    Satisfies_symbol_Expression
    {Σ : Signature}
    {B : Type}
    :
    Satisfies Valuation (symbol) B
:= {|
    satisfies := fun _ _ _ => False ;
|}.
Next Obligation.
    auto with nocore.
Qed.

