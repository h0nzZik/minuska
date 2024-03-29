From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    varsof
    syntax_properties
.

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
        auto with nocore.
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
    {
        do 2 (rewrite bind_Some).
        intros [x [Hx1 Hx2]].
        exists x.
        rewrite (IHt1 _ Hx1).
        split>[reflexivity|].

        rewrite bind_Some in Hx2.
        destruct Hx2 as [x' [Hx'1 Hx'2]].
        rewrite bind_Some.

        rewrite bind_Some in Hx'2.
        destruct Hx'2 as [x'' [Hx''1 Hx''2]].
        exists x'.
        rewrite (IHt2 _ Hx'1).
        split>[reflexivity|].

        rewrite bind_Some.
        exists x''.
        rewrite (IHt3 _ Hx''1).
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
        auto with nocore.
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
        destruct Hx2 as [x' [Hx'1 Hx'2]].
        rewrite bind_None in Hx'2.
        destruct Hx'2 as [HNone|Hx'2].
        {
            specialize (IHt3 HNone).
            destruct (Expression_evaluate ρ1 t1).
            {
                right.
                exists g.
                split>[reflexivity|].
                rewrite bind_None.

                destruct (Expression_evaluate ρ1 t2).
                {
                    right.
                    exists g0.
                    split>[reflexivity|].
                    rewrite bind_None.
                    left. exact IHt3.
                }
                {
                    left. reflexivity.
                }
            }
            {
                left. reflexivity.
            }
        }
        {
            destruct Hx'2 as [x2 [Hx'21 Hx'22]].
            inversion Hx'22.
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

Lemma Expression_evalute_total_iff
    {Σ : StaticModel}
    (t : Expression)
    (ρ : Valuation)
    :
    (∃ e:GroundTerm, Expression_evaluate ρ t = Some e)
    <->
    ( vars_of t ⊆ vars_of ρ )
.
Proof.
    induction t; cbn.
    {
        split; intros H.
        {
            apply empty_subseteq.
        }
        {
            exists e.
            reflexivity.
        }
    }
    {
        split; intros H.
        {
            rewrite elem_of_subseteq.
            intros x0 Hx0.
            unfold vars_of in Hx0; simpl in Hx0.
            rewrite elem_of_singleton in Hx0.
            subst x0.
            destruct H as [e H].
            ltac1:(rewrite elem_of_dom).
            exists e. exact H.
        }
        {
            rewrite elem_of_subseteq in H.
            specialize (H x).
            unfold vars_of in H; simpl in H.
            rewrite elem_of_singleton in H.
            specialize (H erefl).
            ltac1:(rewrite elem_of_dom in H).
            unfold is_Some in H.
            destruct H as [e H].
            exists e.
            exact H.
        }
    }
    {
        split; intros H.
        {
            ltac1:(set_solver).
        }
        {
            eexists. reflexivity.
        }
    }
    {
        ltac1:(rewrite <- IHt).
        split; intros [e H].
        {
            unfold mbind,option_bind in H; cbn.
            ltac1:(case_match).
            {
                ltac1:(rewrite <- H0).
                eexists.
                exact H0.
            }
            {
                inversion H.
            }
        }
        {
            eexists. rewrite H. reflexivity.
        }
    }
    {
        unfold vars_of; simpl.
        rewrite union_subseteq.
        ltac1:(rewrite <- IHt1).
        ltac1:(rewrite <- IHt2).
        split; intros H.
        {
            destruct H as [e H].
            unfold mbind,option_bind in H.
            (repeat ltac1:(case_match)); ltac1:(simplify_eq /=);
                split; eexists; reflexivity.
        }
        {
            destruct H as [[e1 H1] [e2 H2]].
            unfold mbind,option_bind.
            rewrite H1.
            rewrite H2.
            eexists. reflexivity.
        }
    }
    {
        unfold vars_of; simpl.
        rewrite union_subseteq.
        rewrite union_subseteq.
        ltac1:(rewrite <- IHt1).
        ltac1:(rewrite <- IHt2).
        ltac1:(rewrite <- IHt3).
        split; intros H.
        {
            destruct H as [e H].
            unfold mbind,option_bind in H.
            (repeat ltac1:(case_match)); ltac1:(simplify_eq /=);
                (repeat split); eexists; reflexivity.
        }
        {
            destruct H as [[[e1 H1] [e2 H2]] [e3 H3]].
            unfold mbind,option_bind.
            rewrite H1.
            rewrite H2.
            rewrite H3.
            eexists. reflexivity.
        }
    }
Qed.

Lemma Expression_evalute_total_T_2
    {Σ : StaticModel}
    (t : Expression)
    (ρ : Valuation)
    :
    ( vars_of t ⊆ vars_of ρ ) ->
    { e:GroundTerm & Expression_evaluate ρ t = Some e }
.
Proof.
    induction t; cbn; intros H.
    {
        exists e.
        reflexivity.
    }
    {

        rewrite elem_of_subseteq in H.
        specialize (H x).
        unfold vars_of in H; simpl in H.
        rewrite elem_of_singleton in H.
        specialize (H erefl).
        destruct (ρ !! x) eqn:Hρx.
        {
            exists g. apply Hρx.
        }
        {
            unfold Valuation in *.
            apply not_elem_of_dom_2 in Hρx.
            ltac1:(contradiction Hρx).
        }
    }
    {
        eexists. reflexivity.
    }
    {
        unfold vars_of in H; simpl in H.
        specialize (IHt H).
        destruct IHt as [e He].
        eexists. rewrite He. reflexivity.
    }
    {
        unfold vars_of in H; simpl in H.
        rewrite union_subseteq in H.
        destruct H as [H1 H2].
        specialize (IHt1 H1).
        specialize (IHt2 H2).
        destruct IHt1 as [e1 He1].
        destruct IHt2 as [e2 Hee].
        unfold mbind,option_bind.
        rewrite He1.
        rewrite Hee.
        eexists. reflexivity.
    }
    {
        unfold vars_of in H; simpl in H.
        rewrite union_subseteq in H.
        rewrite union_subseteq in H.
        destruct H as [[H1 H2] H3].
        specialize (IHt1 H1).
        specialize (IHt2 H2).
        specialize (IHt3 H3).
        destruct IHt1 as [e1 He1].
        destruct IHt2 as [e2 He2].
        destruct IHt3 as [e3 He3].
        rewrite He1. rewrite He2. rewrite He3. simpl.
        eexists. reflexivity.
    }
Qed.

Class SatisfiesProperties
    {Σ : StaticModel}
    (V A B var : Type)
    {_SV : SubsetEq V}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV: VarsOf V var}
    {_SAT : Satisfies V A B var}
    :=
mkSatisfiesProperties {
    satisfies_ext :
        forall (v1 v2 : V),
            v1 ⊆ v2 ->
            forall (a : A) (b : B),
                satisfies v1 a b ->
                satisfies v2 a b ;
}.

#[export]
Instance SatisfiesProperties_val_ap
    {Σ : StaticModel} :
    SatisfiesProperties
        (gmap variable GroundTerm)
        unit
        AtomicProposition
        variable
.
Proof.
    constructor. intros.
    destruct b; simpl in *.
    {
        unfold satisfies in *; simpl in *.
        destruct X as [H1 H2].
        unfold isSome in *.
        destruct (Expression_evaluate v1 e1) eqn:Hev1e1>[|inversion H2].
        symmetry in H1.
        rewrite (Expression_evaluate_extensive_Some v1 v2 _ g H H1).
        rewrite (Expression_evaluate_extensive_Some v1 v2 e1 g H Hev1e1).
        repeat split.
    }
Qed.


#[export]
Instance SatisfiesProperties_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    SatisfiesProperties Valuation (builtin_value) BuiltinOrVar variable
.
Proof.
    constructor. intros.
    inversion X; constructor.
    {
        subst.
        unfold Valuation in *.
        eapply lookup_weaken.
        { apply H0. }
        { assumption. }
    }
Qed.


#[export]
Instance SatisfiesProperties__PreTerm'_symbol_builtin__BuiltinOrVar
    {Σ : StaticModel}
    : SatisfiesProperties Valuation ((PreTerm' symbol builtin_value)) BuiltinOrVar variable
.
Proof.
    constructor. intros.
    destruct b; simpl in *.
    { ltac1:(contradiction). }
    {
        unfold satisfies; simpl.
        unfold Valuation in *.
        eapply lookup_weaken.
        { apply X. }
        { assumption. }
    }
Qed.

#[export]
Instance SatisfiesProperties_PreTerm'_symbol_builtin_BuiltinOrVar
    {Σ : StaticModel}
    :
    SatisfiesProperties Valuation ((PreTerm' symbol builtin_value)) BuiltinOrVar variable
.
Proof.
    constructor. intros.
    destruct b; simpl in *.
    { ltac1:(contradiction). }
    {
        unfold satisfies; simpl.
        unfold Valuation in *.
        eapply lookup_weaken.
        { apply X. }
        { assumption. }
    }
Qed.


#[export]
Instance SatisfiesProperties__builtin__ao'B
    {Σ : StaticModel}
    {V B var : Type}
    {_SV : SubsetEq V}
    {_EDv : EqDecision var}
    {_Cv : Countable var}
    {_VV : VarsOf V var}
    :
    SatisfiesProperties
        V
        (builtin_value)
        (PreTerm' symbol B)
        var
.
Proof.
    constructor. intros. auto.
Qed.


#[export]
Instance SatisfiesProperties_aoxyo_aoxzo
    {Σ : StaticModel}
    (V X Y Z var : Type)
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V Y Z var}
    {_S2 : Satisfies V ((PreTerm' X Y)) Z var}
    {_S3 : Satisfies V ((PreTerm' X Y)) (PreTerm' X Z) var}
    {_S1P : SatisfiesProperties V Y Z var}
    {_S2P : SatisfiesProperties V ((PreTerm' X Y)) Z var}
    {_S3P : SatisfiesProperties V ((PreTerm' X Y)) (PreTerm' X Z) var}
    :
    SatisfiesProperties V ((Term' X Y)) (Term' X Z) var
.
Proof.
    constructor. intros.
    destruct X0; constructor.
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


#[export]
Instance SatisfiesProperties_aoxy_aoxz
    {Σ : StaticModel}
    {V X Y Z var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_VV : VarsOf V var}
    {_SV : SubsetEq V}
    {_S1 : Satisfies V (Y) Z var}
    {_S2 : Satisfies V (Y) (PreTerm' X Z) var}
    {_S3 : Satisfies V ((PreTerm' X Y)) Z var}
    {_S1P : SatisfiesProperties V (Y) Z var}
    {_S2P : SatisfiesProperties V (Y) (PreTerm' X Z) var}
    {_S3P : SatisfiesProperties V ((PreTerm' X Y)) Z var}
    :
    SatisfiesProperties V ((PreTerm' X Y)) (PreTerm' X Z) var
.
Proof.
    constructor. intros.
    revert v2 H.
    induction X0; intros v2 HH; constructor; try (ltac1:(naive_solver)).
    {
        eapply satisfies_ext.
        { apply HH. }
        { assumption. }
    }
    {
        eapply satisfies_ext.
        { apply HH. }
        { assumption. }
    }
    {
        eapply satisfies_ext.
        { apply HH. }
        { assumption. }
    }
Qed.

#[export]
Instance SatisfiesProperties_aoosb_aoosbf
    {Σ : StaticModel}
    :
    SatisfiesProperties
        Valuation
        ((Term' symbol builtin_value))
        (Term' symbol BuiltinOrVar)
        variable
.
Proof.
    apply SatisfiesProperties_aoxyo_aoxzo.
    {
        apply _.
    }
    {
        apply _.
    }
    {
        apply _.
    }
Defined.

#[export]
Instance SatisfiesProperties_valGroundTerm_SymbolicTerm
    {Σ : StaticModel}
    :
    SatisfiesProperties
        Valuation
        GroundTerm
        SymbolicTerm
        variable
.
Proof.
    apply _.
Defined.


#[export]
Instance SatisfiesProperties_val_sc
    {Σ : StaticModel}
    :
    SatisfiesProperties
        Valuation
        unit
        SideCondition
        variable
.
Proof.
    constructor. intros; unfold satisfies in *; simpl in *.
    destruct b; simpl in *; eapply satisfies_ext>[apply H|]; assumption.
Qed.

#[export]
Instance SatisfiesProperties_GroundTerm_BuiltinOrVar
    {Σ : StaticModel}
    :
    SatisfiesProperties Valuation (GroundTerm) BuiltinOrVar variable
.
Proof.
    constructor. unfold satisfies; simpl. intros.
    destruct a,b; simpl in *; try ltac1:(naive_solver);
        unfold Valuation in *; eapply lookup_weaken>[|apply H];
        assumption.
Qed.

#[export]
Instance SatisfiesProperties_builtin_value_SymbolicTerm
    {Σ : StaticModel}
    :
    SatisfiesProperties
        Valuation
        builtin_value
        SymbolicTerm
        variable
.
Proof.
    constructor. unfold satisfies; simpl. intros.
    destruct b; simpl in *.
    { assumption. }
    {
        eapply satisfies_ext>[apply H|].
        assumption.
    }
Qed.


#[export]
Instance SatisfiesProperties__PreTerm'_symbol_builtin_value__BOV
    {Σ : StaticModel}
    {V : Type}
    :
    SatisfiesProperties
        Valuation
        ((PreTerm' symbol builtin_value))
        BuiltinOrVar
        variable
.
Proof.
    constructor. unfold satisfies; simpl. intros.
    destruct b; simpl in *; try assumption.
    {
        unfold Valuation in *.
        eapply lookup_weaken.
        { apply X. }
        { assumption. }
    }
Qed.

#[export]
Instance SatisfiesProperties__lift_builtin_to_aosb
    {Σ : StaticModel}
    {V A B var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (A) B var}
    {_S2 : Satisfies V ((PreTerm' symbol A)) B var}
    {_S3 : Satisfies V (PreTerm' symbol A) (PreTerm' symbol B) var}
    {_S1P : SatisfiesProperties V (A) B var}
    {_S2P : SatisfiesProperties V ((PreTerm' symbol A)) B var}
    {_S3P : SatisfiesProperties V (PreTerm' symbol A) (PreTerm' symbol B) var}
    :
    SatisfiesProperties
        V
        ((PreTerm' symbol A))
        (Term' symbol B)
        var
.
Proof.
    constructor. unfold satisfies; simpl. intros.
    unfold PreTerm'_symbol_A_satisfies_SymbolicTermB' in *.
    eapply satisfies_ext.
    { apply H. }
    { assumption. }
Qed.    

#[export]
Instance SatisfiesProperties__PreTerm'_symbol_builtin__SymbolicTerm
    {Σ : StaticModel}
    {V var : Type}
    {_varED : EqDecision var}
    {_varCnt : Countable var}
    {_SV : SubsetEq V}
    {_VV : VarsOf V var}
    {_S1 : Satisfies V (builtin_value) BuiltinOrVar var}
    {_S2 : Satisfies V (PreTerm' symbol builtin_value) BuiltinOrVar var}
    {_S3 : Satisfies V (PreTerm' symbol builtin_value) (PreTerm' symbol BuiltinOrVar) var}
    {_S1P : SatisfiesProperties V (builtin_value) BuiltinOrVar var}
    {_S2P : SatisfiesProperties V (PreTerm' symbol builtin_value) BuiltinOrVar var}
    {_S3P : SatisfiesProperties V (PreTerm' symbol builtin_value) (PreTerm' symbol BuiltinOrVar) var}
    :
    SatisfiesProperties V
        ((PreTerm' symbol builtin_value))
        SymbolicTerm
        var
.
Proof.
    constructor. unfold satisfies. simpl. intros.
    eapply satisfies_ext.
    { apply H. }
    { assumption. }
Qed.

#[export]
Instance SatisfiesProperties_builtin_expr
    {Σ : StaticModel}:
    SatisfiesProperties
        Valuation
        builtin_value
        Expression
        variable
.
Proof.
    constructor. unfold satisfies. simpl.  intros. simpl in *.
    erewrite Expression_evaluate_extensive_Some>[|apply H|].
    { reflexivity. }
    { assumption. }
Qed.


#[export]
Instance SatisfiesProperties_asb_expr
    {Σ : StaticModel}:
    SatisfiesProperties
        Valuation
        ((PreTerm' symbol builtin_value))
        Expression
        variable
.
Proof.
    constructor. unfold satisfies. simpl. intros. simpl in *.
    erewrite Expression_evaluate_extensive_Some>[|apply H|].
    { reflexivity. }
    { assumption. }
Qed.

#[export]
Instance SatisfiesProperties_gt_var
    {Σ : StaticModel}:
    SatisfiesProperties
        Valuation
        GroundTerm
        variable
        variable
.
Proof.
    constructor. unfold satisfies. simpl. intros. simpl in *.
    unfold Valuation in *.
    eapply lookup_weaken.
    { apply H0. }
    { assumption. }
Qed.


#[export]
Instance SatisfiesProperties_sym_bov
    {Σ : StaticModel}
    :
    SatisfiesProperties
        Valuation
        symbol
        BuiltinOrVar
        variable
.
Proof.
    constructor. unfold satisfies. simpl. 
    simpl. auto with nocore.
Qed.

#[export]
Instance SatisfiesProperties_Valuation_LR_SideCondition
    {Σ : StaticModel}
    :
    SatisfiesProperties
        (Valuation * LeftRight)
        unit
        SideCondition
        variable
.
Proof.
    constructor. unfold satisfies. simpl. 
    simpl. intros.
    inversion H; subst.
    eapply satisfies_ext.
    { apply H0. }
    { assumption. }
Qed.


#[export]
Instance SatisfiesProperties__GroundTerm__SymbolicTerm_inall
    {Σ : StaticModel}
    :
    SatisfiesProperties
        unit
        GroundTerm
        SymbolicTerm
        variable
.
Proof.
    constructor. unfold satisfies. simpl. 
    simpl. intros. assumption.
Qed.


#[export]
Instance SatisfiesProperties_valuation_scs
    {Σ : StaticModel}
    : SatisfiesProperties
        Valuation
        unit
        (list SideCondition)
        variable
.
Proof.
    constructor. unfold satisfies. simpl. 
    intros. simpl in *.
    specialize (X x H0).
    eapply satisfies_ext.
    { apply H. }
    { assumption. }
Qed.


#[export]
Instance
    SatisfiesProperties_symbol_B
    {Σ : StaticModel}
    {V B var : Type}
    {_SV : SubsetEq V}
    {_EDvar : EqDecision var}
    {_Covar : Countable var}
    {_VV : VarsOf V var}
    :
    SatisfiesProperties
        V
        symbol
        B
        var
.
Proof.
    constructor. unfold satisfies. simpl.     
    auto with nocore.
Qed.

Lemma Expression_evalute_total_same
    {Σ : StaticModel}
    (t : Expression)
    (ρ1 ρ2 ρ : Valuation)
    :
    ρ1 ⊆ ρ ->
    ρ2 ⊆ ρ ->
    vars_of t ⊆ vars_of ρ1 ->
    vars_of t ⊆ vars_of ρ2 ->
    Expression_evaluate ρ1 t = Expression_evaluate ρ2 t
.
Proof.
    intros H1 H2 H3 H4.
    induction t; simpl.
    { reflexivity. }
    {
        unfold vars_of in *; simpl in *.
        rewrite elem_of_subseteq in H3.
        rewrite elem_of_subseteq in H4.
        specialize (H3 x).
        specialize (H4 x).
        ltac1:(specialize(H3 ltac:(set_solver))).
        ltac1:(specialize(H4 ltac:(set_solver))).
        ltac1:(rewrite elem_of_dom in H3).
        ltac1:(rewrite elem_of_dom in H4).
        destruct H3 as [x1 Hx1].
        destruct H4 as [x2 Hx2].
        rewrite Hx1. rewrite Hx2.
        eapply lookup_weaken in Hx1>[|apply H1].
        eapply lookup_weaken in Hx2>[|apply H2].
        rewrite Hx1 in Hx2.
        inversion Hx2. subst; clear Hx2.
        reflexivity.
    }
    {
        reflexivity.
    }
    {
        unfold vars_of in *; simpl in *.
        specialize (IHt ltac:(assumption)).
        specialize (IHt ltac:(assumption)).
        rewrite IHt.
        reflexivity.
    }
    {
        unfold vars_of in *; simpl in *.
        rewrite union_subseteq in H3.
        rewrite union_subseteq in H4.
        destruct H3. destruct H4.
        specialize (IHt1 ltac:(assumption)).
        specialize (IHt2 ltac:(assumption)).
        specialize (IHt1 ltac:(assumption)).
        specialize (IHt2 ltac:(assumption)).
        rewrite IHt1. rewrite IHt2.
        reflexivity.
    }
    {
        unfold vars_of in *; simpl in *.
        rewrite union_subseteq in H3.
        destruct H3 as [H31 H32].
        rewrite union_subseteq in H4.
        destruct H4 as [H41 H42].
        rewrite union_subseteq in H31.
        destruct H31 as [H311 H312].
        rewrite union_subseteq in H41.
        destruct H41 as [H411 H412].
        specialize (IHt1 ltac:(assumption)).
        specialize (IHt2 ltac:(assumption)).
        specialize (IHt3 ltac:(assumption)).
        specialize (IHt1 ltac:(assumption)).
        specialize (IHt2 ltac:(assumption)).
        specialize (IHt3 ltac:(assumption)).
        rewrite IHt1. rewrite IHt2. rewrite IHt3.
        reflexivity.
    }
Qed.

#[export]
Instance SatisfiesProperties_TermOverBuiltin_TermOverBoV
    {Σ : StaticModel}
    : SatisfiesProperties
        Valuation
        (TermOver builtin_value)
        (TermOver BuiltinOrVar)
        variable
.
Proof.
    constructor.
    intros v1 v2 Hv1v2 a b.
    unfold satisfies; simpl.
    intros H.
    eapply satisfies_ext>[|apply H].
    exact Hv1v2.
Defined.

#[export]
Instance SatisfiesProperties_TermOverBuiltin_TermOverExpression
    {Σ : StaticModel}
    : SatisfiesProperties
        Valuation
        (TermOver builtin_value)
        (TermOver Expression)
        variable
.
Proof.
    constructor.
    intros v1 v2 Hv1v2 a b.
    unfold satisfies; simpl.
    intros H.
    eapply satisfies_ext>[|apply H].
    exact Hv1v2.
Defined.
