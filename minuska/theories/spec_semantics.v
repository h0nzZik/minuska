From Minuska Require Import
    prelude
    spec_syntax
.

Definition Valuation {Σ : StaticModel}
        := gmap variable GroundTerm
    .

#[export]
Instance VarsOf_valuation
    {Σ : StaticModel}
    {var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    : VarsOf (gmap var GroundTerm) var
:= {|
    vars_of := fun ρ => dom ρ ; 
|}.

#[export]
Instance VarsOf_symbol
    {Σ : StaticModel}
    : VarsOf symbol variable
:= {|
    vars_of := fun _ => ∅ ; 
|}.

#[export]
Instance VarsOf_builtin
    {Σ : StaticModel}
    : VarsOf builtin_value variable
:= {|
    vars_of := fun _ => ∅ ; 
|}.


(*Transparent Valuation.*)

Fixpoint Expression_evaluate
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    (V A B var : Type)
    {_SV : SubsetEq V}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV: VarsOf V var}
    :=
mkSatisfies {
    satisfies :
        V -> A -> B -> Prop ;

    satisfies_ext :
        forall (v1 v2 : V),
            v1 ⊆ v2 ->
            forall (a : A) (b : B),
                satisfies v1 a b ->
                satisfies v2 a b ;
}.

Arguments satisfies : simpl never.

Definition val_satisfies_ap
    {Σ : StaticModel} (ρ : Valuation) (ap : AtomicProposition)
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
    {Σ : StaticModel} :
    Satisfies
        (gmap variable GroundTerm)
        unit
        AtomicProposition
        variable
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
    {Σ : StaticModel} (ρ : Valuation) (c : Constraint)
    : Prop :=
match c with
| c_True => True
| c_atomic ap => satisfies ρ () ap
| c_and c1 c2 => val_satisfies_c ρ c1 /\ val_satisfies_c ρ c2
(* | c_not c' => ~ val_satisfies_c ρ c' *)
end.

#[export]
Program Instance Satisfies_val_c
    {Σ : StaticModel} :
    Satisfies
        (gmap variable GroundTerm)
        unit
        Constraint
        variable
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
    {Σ : StaticModel}
    {V X Y Z var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z var}
    {_S2 : Satisfies V (Y) (AppliedOperator' X Z) var}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) Z var}

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
    {Σ : StaticModel}
    {V X Y Z var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z var}
    {_S2 : Satisfies V (Y) (AppliedOperator' X Z) var}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) Z var}
    :
    Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z) var
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
    {Σ : StaticModel}
    (V X Y Z var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z var}
    {_S2 : Satisfies V ((AppliedOperator' X Y)) Z var}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z) var}
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
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@aoo_app _ _  xy) (aoo_app xz)

| axysaxz_operand:
    forall (ρ : V) (y : Y) (z : Z) (pf : satisfies ρ y z),
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@aoo_operand X Y y) (@aoo_operand X Z z)

| axysaxz_combined:
    forall (ρ : V) axy axz,
        satisfies ρ axy axz ->
        aoxyo_satisfies_aoxzo V X Y Z var ρ (@aoo_app _ _  axy) (@aoo_operand X Z axz)
.

#[export]
Program Instance Satisfies_aoxyo_aoxzo
    {Σ : StaticModel}
    (V X Y Z var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z var}
    {_S2 : Satisfies V ((AppliedOperator' X Y)) Z var}
    {_S3 : Satisfies V ((AppliedOperator' X Y)) (AppliedOperator' X Z) var}
    :
    Satisfies V ((AppliedOperatorOr' X Y)) (AppliedOperatorOr' X Z) var
:= {|
    satisfies := aoxyo_satisfies_aoxzo V X Y Z var;
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    (ρ : Valuation)
    (b : builtin_value)
    (bov : BuiltinOrVar)
    : Prop
:= builtin_satisfies_BuiltinOrVar ρ b bov.

#[export]
Instance Subseteq_Valuation {Σ : StaticModel}
    : SubsetEq Valuation
.
Proof.
    unfold Valuation.
    apply _.
Defined.

#[export]
Program Instance Satisfies_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation (builtin_value) BuiltinOrVar variable
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
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : AppliedOperator' symbol builtin_value)
    (bov : BuiltinOrVar)
    : Prop :=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app aop)
end.

#[export]
Program Instance Satisfies__AppliedOperator'_symbol_builtin__BuiltinOrVar
    {Σ : StaticModel}
    : Satisfies Valuation ((AppliedOperator' symbol builtin_value)) BuiltinOrVar variable
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
    {Σ : StaticModel}
    (ρ : Valuation)
    (aop : (AppliedOperator' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Prop
:= AppliedOperator'_symbol_builtin_satisfies_BuiltinOrVar ρ aop bov.

#[export]
Program Instance Satisfies_AppliedOperator'_symbol_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation ((AppliedOperator' symbol builtin_value)) BuiltinOrVar variable
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

(*
Definition aosb_satisfies_aosbf
    {Σ : StaticModel}
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
*)

#[export]
Program Instance Satisfies__builtin__ao'B
    {Σ : StaticModel}
    {V B var : Type}
    {_SV : SubsetEq V}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VV : VarsOf V var}
    :
    Satisfies
        V
        (builtin_value)
        (AppliedOperator' symbol B)
        var
:= {| 
    satisfies := fun _ _ _ => false ;
|}.

#[export]
Instance Satisfies_aos__builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        ((AppliedOperator' symbol builtin_value))
        (AppliedOperator' symbol BuiltinOrVar)
        variable
.
Proof.
    apply _.
Defined.


#[export]
Instance Satisfies_aosb_aosbf
    {Σ : StaticModel}
    {A B : Type}
    {SatAB : Satisfies Valuation (A) B variable}
    {_S2 : Satisfies Valuation (A) (AppliedOperator' symbol B) variable}
    {SatA'B : Satisfies Valuation ((AppliedOperator' symbol A)) B variable}
    :
    Satisfies Valuation ((AppliedOperator' symbol A)) (AppliedOperator' symbol B) variable
.
Proof.
    apply _.
Defined.

(*
Definition aoosb_satisfies_aoosbf
    {Σ : StaticModel}
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
*)

#[export]
Instance
Satisfies_aoosb_aoosbf
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        ((AppliedOperatorOr' symbol builtin_value))
        (AppliedOperatorOr' symbol BuiltinOrVar)
        variable
.
Proof. apply _. Defined.

(*
Definition in_val_GroundTerm_satisfies_OpenTerm
    {Σ : StaticModel}
    (ρ : Valuation)
    (g : GroundTerm)
    (φ : OpenTerm)
    : Prop := aoosb_satisfies_aoosbf ρ g φ
.
*)

#[export]
Instance Satisfies_valGroundTerm_OpenTerm
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        GroundTerm
        OpenTerm
        variable
.
Proof. apply _. Defined.

Definition valuation_satisfies_match
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        unit
        Match
        variable
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
    {Σ : StaticModel}
    (ρ : Valuation)
    (sc : SideCondition) : Prop :=
match sc with
| sc_constraint c => satisfies ρ () c
| sc_match m => satisfies ρ () m
end.

#[export]
Program Instance Satisfies_val_sc
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        unit
        SideCondition
        variable
:= {|
    satisfies := fun a b c => valuation_satisfies_sc a c ;
|}.
Next Obligation.
    destruct b; simpl in *; eapply satisfies_ext>[apply H|]; assumption.
Qed.
Fail Next Obligation.

Inductive A_satisfies_B_WithASideCondition
    {Σ : StaticModel}
    (V A B var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V unit SideCondition var}
    {_S2 : Satisfies V (A) B var}
    : V -> A -> WithASideCondition B -> Prop :=

| asbwsc_base:
    forall ρ a (b : B),
        satisfies ρ a b ->
        A_satisfies_B_WithASideCondition V A B var ρ a (wsc_base b)

| asbwsc_sc :
    forall ρ a (bsc : WithASideCondition B) sc,
        A_satisfies_B_WithASideCondition V A B var ρ a bsc ->
        satisfies ρ () sc ->
        A_satisfies_B_WithASideCondition V A B var ρ a (wsc_sc bsc sc)
.

#[export]
Program Instance Satisfies_A_Bsc
    {Σ : StaticModel}
    {V A B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V unit SideCondition var}
    {_S2 : Satisfies V A B var}
    :
    Satisfies V A (WithASideCondition B) var
:= {|
    satisfies :=
        A_satisfies_B_WithASideCondition
        V A B var;
|}.
Next Obligation.
    induction H0; constructor; try (ltac1:(naive_solver));
        eapply satisfies_ext>[apply H|]; assumption.
Qed.
Fail Next Obligation.

Definition GroundTerm_satisfies_BuiltinOrVar
    {Σ : StaticModel}
    (ρ : Valuation)
    (g : GroundTerm)
    (bov : BuiltinOrVar)
    : Prop :=
match bov with
| bov_builtin b =>
    match g with
    | aoo_app _ => False
    | aoo_operand b' => b = b'
    end
| bov_variable x => ρ !! x = Some g
end.

#[export]
Program Instance Satisfies_GroundTerm_BuiltinOrVar
    {Σ : StaticModel}
    :
    Satisfies Valuation (GroundTerm) BuiltinOrVar variable
:= {|
    satisfies := GroundTerm_satisfies_BuiltinOrVar ;
|}.
Next Obligation.
    destruct a,b; simpl in *; try ltac1:(naive_solver);
        unfold Valuation in *; eapply lookup_weaken>[|apply H];
        assumption.
Qed.
Fail Next Obligation.

(*
Definition in_val_GroundTerm_satisfies_OpenTermWSC
    {Σ : StaticModel}
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
*)

#[export]
Instance Satisfies_GroundTerm_OpenTermWSC
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        GroundTerm
        OpenTermWSC
        variable
.
Proof. apply _. Defined.

Definition builtin_value_satisfies_OpenTerm
    {Σ : StaticModel}
    :
    Valuation ->
    builtin_value ->
    OpenTerm ->
    Prop := fun ρ b t =>
match t with
| aoo_app _ => False
| aoo_operand bov =>
    satisfies ρ b bov
end.

#[export]
Program Instance Satisfies_builtin_value_OpenTerm
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        builtin_value
        OpenTerm
        variable
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

(*
Definition builtin_value_satisfies_OpenTermWSC
    {Σ : StaticModel}
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
*)

#[export]
Instance Satisfies_builtin_value_OpenTermWSC
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        builtin_value
        OpenTermWSC
        variable
.
Proof. apply _. Defined.

Definition AppliedOperator'_symbol_builtin_value_satisfies_BOV
    {Σ : StaticModel}
    (ρ : Valuation)
    (ao : (AppliedOperator' symbol builtin_value))
    (bov : BuiltinOrVar)
    : Prop
:=
match bov with
| bov_builtin _ => False
| bov_variable x => ρ !! x = Some (aoo_app ao) 
end
.

#[export]
Program Instance Satisfies__AppliedOperator'_symbol_builtin_value__BOV
    {Σ : StaticModel}
    {V : Type}
    :
    Satisfies
        Valuation
        ((AppliedOperator' symbol builtin_value))
        BuiltinOrVar
        variable
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
    {Σ : StaticModel}
    (V A B var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (A) B var}
    {_S2 : Satisfies V ((AppliedOperator' symbol A)) B var}
    {_S3 : Satisfies V (AppliedOperator' symbol A) (AppliedOperator' symbol B) var}
    :
    V ->
    (AppliedOperator' symbol A) ->
    AppliedOperatorOr' symbol B ->
    Prop
:=  fun ρ a =>
    satisfies
    ρ (aoo_app a)
.

#[export]
Program Instance Satisfies__lift_builtin_to_aosb
    {Σ : StaticModel}
    {V A B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (A) B var}
    {_S2 : Satisfies V ((AppliedOperator' symbol A)) B var}
    {_S3 : Satisfies V (AppliedOperator' symbol A) (AppliedOperator' symbol B) var}
    :
    Satisfies
        V
        ((AppliedOperator' symbol A))
        (AppliedOperatorOr' symbol B)
        var
:= {|
    satisfies :=
        AppliedOperator'_symbol_A_satisfies_OpenTermB' V A B var;
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
    {Σ : StaticModel}
    {V A B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {bsB : Satisfies V (A) B var}
    {sat2 : Satisfies V ((AppliedOperator' symbol A)) B var}
    {sat3 : Satisfies V ((AppliedOperator' symbol A)) (AppliedOperator' symbol B) var}
    :
    Satisfies V
        ((AppliedOperatorOr' symbol A))
        (AppliedOperatorOr' symbol B)
        var
.
Proof. apply _. Defined.

Definition AppliedOperator'_symbol_builtin_satisfies_OpenTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol BuiltinOrVar) var}
    :
    V ->
    ((AppliedOperator' symbol builtin_value)) ->
    OpenTerm ->
    Prop
:=  fun ρ a =>
    satisfies ρ (aoo_app a)
.

#[export]
Program Instance Satisfies__AppliedOperator'_symbol_builtin__OpenTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol BuiltinOrVar) var}
    :
    Satisfies V
        ((AppliedOperator' symbol builtin_value))
        OpenTerm
        var
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
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        (AppliedOperator' symbol builtin_value)
        OpenTermWSC
        variable
.
Proof. apply _. Defined.


#[export]
Instance Satisfies__GroundTerm__LhsPattern
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) OpenTermWSC var}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) OpenTermWSC var}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol OpenTermWSC) var}
    :
    Satisfies
        V
        GroundTerm
        LhsPattern
        var
.
Proof. apply _. Defined.

#[local]
Obligation Tactic := idtac.

#[export]
Program Instance Satisfies_builtin_expr
    {Σ : StaticModel}:
    Satisfies
        Valuation
        builtin_value
        Expression
        variable
:= {|
    satisfies := (fun ρ b e =>
        Expression_evaluate ρ e = Some (aoo_operand b)
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
    {Σ : StaticModel}:
    Satisfies
        Valuation
        ((AppliedOperator' symbol builtin_value))
        Expression
        variable
:= {|
    satisfies := (fun ρ x e =>
        Expression_evaluate ρ e = Some (aoo_app x)
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) Expression var}
    {_S2 : Satisfies V (AppliedOperator' symbol builtin_value) Expression var}
    {_S3 : Satisfies V (AppliedOperator' symbol builtin_value) (AppliedOperator' symbol Expression) var}
    :
    Satisfies
        V
        GroundTerm
        RhsPattern
        var
.
Proof. apply _. Defined.

#[export]
Program Instance Satisfies_gt_var
    {Σ : StaticModel}:
    Satisfies
        Valuation
        GroundTerm
        variable
        variable
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
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        GroundTerm
        (WithASideCondition variable)
        variable
.
Proof. apply _. Defined.


Definition GroundTerm_satisfies_LocalRewrite
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    : SubsetEq (Valuation * LeftRight)
:= {
    subseteq a b := subseteq a.1 b.1 /\ a.2 = b.2
}.


(* TODO *)
#[export]
Instance VarsOf_ValuationLR
    {Σ : StaticModel}
    : VarsOf (Valuation * LeftRight) variable
:= {
    vars_of a := vars_of a.1
}.

#[export]
Program Instance Satisfies__GroundTerm__LocalRewrite
    {Σ : StaticModel}
    :
    Satisfies
        (Valuation*LeftRight)
        GroundTerm
        LocalRewrite
        variable
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
    :
    Satisfies
        (Valuation*LeftRight)
        (GroundTerm)
        (LocalRewriteOrOpenTermOrBOV)
        variable
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
    {Σ : StaticModel}
    (ρd : (Valuation*LeftRight))
    (b : builtin_value)
    (r : LocalRewriteOrOpenTermOrBOV)
    : Prop :=
let ρ := ρd.1 in
match r with
| lp_rewrite r'
    => satisfies (ρd) (aoo_operand b) r'

| lp_basicpat (aoo_app _)
    => False

| lp_basicpat (aoo_operand bov)
    => satisfies ρ b bov

| lp_bov bx
    => satisfies ρ b bx
end.

#[export]
Program Instance Satisfies__builtin_value__LocalRewriteOrOpenTermOrBOV
    {Σ : StaticModel}
    :
    Satisfies
        (Valuation*LeftRight)
        (builtin_value)
        (LocalRewriteOrOpenTermOrBOV)
        variable
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}
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
    {Σ : StaticModel}:
    Satisfies
        (Valuation * LeftRight)
        (AppliedOperator' symbol builtin_value)
        LocalRewriteOrOpenTermOrBOV
        variable
:= {|
    satisfies := fun ρd g =>
        satisfies ρd (aoo_app g)
        
     ;
|}.
Next Obligation.
    intros. simpl in *.
    eapply satisfies_ext>[apply H|]. assumption.
Qed.
Fail Next Obligation.


#[export]
Program Instance Satisfies_vlrblrootob
    {Σ : StaticModel}:
    Satisfies
        (Valuation * LeftRight)
        (builtin_value)
        (AppliedOperator' symbol LocalRewriteOrOpenTermOrBOV)
        variable
:= {|
    satisfies := fun _ _ _ => False ;
|}.
Next Obligation.
    intros. simpl in *. assumption.
Qed.
Fail Next Obligation.


#[export]
Program Instance Satisfies_sym_bov
    {Σ : StaticModel}
    :
    Satisfies
        Valuation
        symbol
        BuiltinOrVar
        variable
:= {|
    satisfies := fun _ _ _ => False ;
|}.
Next Obligation.
    simpl. auto with nocore.
Qed.
Fail Next Obligation.

#[export]
Instance Satisfies_aop_lrw {Σ : StaticModel}:
    Satisfies
        (Valuation * LeftRight)
        (AppliedOperator' symbol builtin_value)
        (AppliedOperator' symbol LocalRewriteOrOpenTermOrBOV)
        variable
.
Proof. apply _. Defined.

#[export]
Instance Satisfies__GroundTerm__UncondRewritingRule
    {Σ : StaticModel}
    :
    Satisfies
        (Valuation*LeftRight)
        (GroundTerm)
        (UncondRewritingRule)
        variable
.
Proof. apply _. Defined.

#[export]
Program Instance Satisfies_Valuation_LR_SideCondition
    {Σ : StaticModel}
    :
    Satisfies
        (Valuation * LeftRight)
        unit
        SideCondition
        variable
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
    {Σ : StaticModel}
    :
    Satisfies
        (Valuation*LeftRight)
        (GroundTerm)
        (RewritingRule)
        variable
.
Proof. apply _. Defined.

Definition GroundTerm_satisfies_OpenTerm
    {Σ : StaticModel}
    : GroundTerm -> OpenTerm -> Prop :=
    fun g φ => ∃ (ρ : Valuation), satisfies ρ g φ
.

#[export]
Instance VarsOf_unit {Σ : StaticModel}: VarsOf unit variable := {|
    vars_of _ := ∅ ;
|}.

#[export]
Instance Subseteq_unit {Σ : StaticModel}: SubsetEq unit := 
    fun _ _ => true
.

#[export]
Program Instance Satisfies__GroundTerm__OpenTerm_inall
    {Σ : StaticModel}
    :
    Satisfies
        unit
        GroundTerm
        OpenTerm
        variable
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
    {Σ : StaticModel}
    :
    Satisfies (Valuation * builtin_value) (AppliedOperator' symbol BuiltinOrVar)
:= {|
    satisfies := fun _ _ => False ;
|}.
*)

Definition rewrites_in_valuation_to
    {Σ : StaticModel}
    (ρ : Valuation)
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= satisfies (ρ,LR_Left) (from) r
/\ satisfies (ρ,LR_Right) (to) r
.

Definition rewrites_to
    {Σ : StaticModel}
    (r : RewritingRule)
    (from to : GroundTerm)
    : Prop
:= exists ρ, rewrites_in_valuation_to ρ r from to
.

Definition RewritingTheory {Σ : StaticModel}
    := list RewritingRule
.

Definition rewriting_relation
    {Σ : StaticModel}
    (Γ : RewritingTheory)
    : relation GroundTerm
    := fun from to =>
        exists r, r ∈ Γ /\ rewrites_to r from to
.

Definition not_stuck
    {Σ : StaticModel}
    (Γ : RewritingTheory)
    (e : GroundTerm) : Prop
:= exists e', rewriting_relation Γ e e'.

Definition stuck
    {Σ : StaticModel}
    (Γ : RewritingTheory)
    (e : GroundTerm) : Prop
:= not (not_stuck Γ e).

Definition rule_weakly_well_defined
    {Σ : StaticModel}
    (r : RewritingRule)
    : Prop
    := ∀ ρ from,
        satisfies (ρ,LR_Left) (from) r ->
        ∃ to, satisfies (ρ,LR_Right) (to) r
.

Definition thy_weakly_well_defined
    {Σ : StaticModel}
    (Γ : RewritingTheory)
    : Prop
    := ∀ r, r ∈ Γ -> rule_weakly_well_defined r
.


#[export]
Program Instance Satisfies_valuation_scs
    {Σ : StaticModel}
    : Satisfies
        Valuation
        unit
        (list SideCondition)
        variable
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
    {Σ : StaticModel}:
    Satisfies (Valuation * builtin_value)
    (AppliedOperator' symbol Expression)
:= {|
    satisfies := fun _ _ => False;
|}.
*)
#[export]
Program Instance
    Satisfies_symbol_B
    {Σ : StaticModel}
    {V B var : Type}
    {_SV : SubsetEq V}
    {_EDvar : EqDecision var}
    {_Covar : Countable var}
    {_VV : VarsOf V var}
    :
    Satisfies
        V
        symbol
        B
        var
:= {|
    satisfies := fun _ _ _ => False ;
|}.
Next Obligation.
    auto with nocore.
Qed.

