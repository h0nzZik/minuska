From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    minusl_syntax
    unification_interface
    (* symex_spec *)
    valuation_merge
.

Locate imap.
Check imap.

Fixpoint decouple
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : listset variable)
    (eqs : listset (variable * Expression2))
    :
    ((TermOver BuiltinOrVar)*(listset (variable * Expression2 )))%type
:=
    match et with
    | t_over e =>
        let y : variable := fresh (avoid ∪ (( ((fst <$> eqs))))) in
        (t_over (bov_variable y), singleton (y,e) ∪ eqs)
    | t_term s l =>
        let '(l'', m) := (fix go (l' : list (TermOver Expression2)) (avoid' : listset variable) (eqs' : listset (variable * Expression2)) : (list (TermOver BuiltinOrVar))*(listset (variable * Expression2 )) := 
            match l' with
            | [] => ([], eqs')
            | x::xs =>
                let '(t', eqs'') := decouple x avoid' eqs' in
                let '(ts', eqs''') := go xs avoid' eqs'' in
                (t'::ts', eqs''')
            end
        ) l avoid eqs in
        (t_term s l'', m)
    end
.

Lemma decouple_extends_eqs
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : listset variable)
    (eqs : listset (variable * Expression2))
    :
    eqs ⊆ (decouple et avoid eqs).2
.
Proof.
    revert avoid eqs.
    induction et; intros avoid eqs; simpl in *.
    {
        ltac1:(set_solver).
    }
    {
        ltac1:(repeat case_match).
        simpl.
        clear s.
        revert avoid eqs l0 l1 H0 H.
        induction l; intros avoid eqs l0 l1 H0 H.
        {
            ltac1:(simplify_eq/=).
            ltac1:(set_solver).
        }
        {
            rewrite Forall_cons in H.
            destruct H as [HH1 HH2].
            ltac1:(repeat case_match; simplify_eq/=).
            specialize (IHl _ _ _ _ H1 HH2).
            eapply transitivity>[|apply IHl].
            clear IHl.
            clear HH2 H1.
            specialize (HH1 avoid eqs).
            rewrite H in HH1.
            simpl in HH1.
            exact HH1.
        }
    }
Qed.

Lemma decouple_avoids
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : listset variable)
    (eqs : listset (variable * Expression2))
    :
    (vars_of (decouple et avoid eqs).1) ## (list_to_set ∘ elements) (avoid ∪ ((fst <$> eqs)))
.
Proof.
    revert avoid eqs.
    induction et; intros avoid eqs; simpl in *.
    {
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        rewrite elem_of_disjoint.
        intros x.
        rewrite elem_of_singleton.
        intros Hx H.
        subst x.
        rewrite elem_of_list_to_set in H.
        rewrite elem_of_elements in H.

        rewrite elem_of_union in H.
        destruct H as [H|H].
        {
            
            (* rewrite elem_of_list_to_set in Hx. *)
            (* rewrite elem_of_elements in Hx. *)
            (* rewrite elem_of_singleton in Hx. *)
            (* subst x. *)
            eapply elem_of_weaken in H.
            eapply is_fresh.
            { apply H. }
            ltac1:(set_solver).
        }
        {
            (* rewrite elem_of_list_to_set in Hx. *)
            (* rewrite elem_of_elements in Hx. *)
            (* rewrite elem_of_singleton in Hx. *)
            (* subst x. *)
            eapply elem_of_weaken in H.
            eapply is_fresh.
            { apply H. }
            ltac1:(set_solver).
        }
    }
    {
        ltac1:(case_match).
        unfold vars_of; simpl.
        clear s.
        revert avoid eqs H l0 l1 H0.
        induction l; intros avoid eqs H l0 l1 H0; simpl in *.
        {
            ltac1:(simplify_eq/=).
            ltac1:(set_solver).
        }
        {
            rewrite Forall_cons in H.
            destruct H as [HH1 HH2].
            
            destruct l0; simpl in *.
            {
                ltac1:(set_solver).
            }
            {
                (* Search elements union. *)
                rewrite disjoint_union_l.
                split.
                {
                    repeat (ltac1:(case_match)).
                    ltac1:(simplify_eq/=).
                    specialize (HH1 avoid eqs).
                    rewrite H in HH1. simpl in HH1.
                    apply HH1.
                }
                {
                    repeat (ltac1:(case_match)).
                    ltac1:(simplify_eq/=).
                    specialize (IHl (avoid) l2 HH2).
                    specialize (IHl l0 l1 H1).
                    assert(Htmp := decouple_extends_eqs a avoid eqs).
                    rewrite H in Htmp.
                    clear - IHl Htmp.
                    ltac1:(set_solver).
                }
            }
        }
    }
    Unshelve.
    apply listset_fin_set.
    apply listset_fin_set.
Qed.

Lemma decoupled_uses_only_original_vars
    {Σ : StaticModel}
    et avoid eqs φ σ x e:
    (φ, σ) = (decouple et avoid eqs) ->
    (x,e) ∈ σ ->
    vars_of e ⊆ vars_of et \/ (x,e) ∈ eqs
.
Proof.
    revert avoid eqs φ σ x e.
    induction et;
        intros avoid eqs φ σ x e H1 H2.
    {
        simpl in *.
        ltac1:(simplify_eq/=).
        rewrite elem_of_union in H2.
        destruct H2 as [H2|H2].
        {
            rewrite elem_of_singleton in H2.
            ltac1:(simplify_eq/=).
            left.
            apply reflexivity.
        }
        {
            right.
            exact H2.
        }
    }
    {
        simpl in *.
        ltac1:(simplify_eq/=).
        rewrite vars_of_t_term_e.
        ltac1:(repeat case_match; simplify_eq/=).
        clear s.
        revert l0 l1 x e avoid eqs H0 H2 H.
        induction l;
            intros l0 l1 x e avoid eqs H0 H2 H.
        {
            simpl in *.
            ltac1:(simplify_eq/=).
            right.
            exact H2.
        }
        {
            rewrite Forall_cons in H.
            destruct H as [HH1 HH2].
            rewrite fmap_cons.
            rewrite union_list_cons.
            destruct (decide ((x, e) ∈ eqs)) as [Hin|Hnotin].
            {
                right. assumption.
            }
            {
                
                ltac1:(repeat case_match; simplify_eq/=).
                destruct (decide ((x, e) ∈ l2)) as [Hin'|Hnotin'].
                {
                    specialize (HH1 avoid eqs t l2 x e (eq_sym H) Hin').
                    destruct HH1 as [HH1|HH1].
                    {
                        ltac1:(clear -HH1; set_solver).
                    }
                    {
                        ltac1:(exfalso; apply Hnotin; apply HH1).
                    }
                }
                {
                    specialize (IHl l3 l1 x e avoid l2 H1 H2 HH2).
                    simpl in *.
                    destruct IHl as [IHl|IHl].
                    {
                        left. ltac1:(clear -IHl; set_solver).
                    }
                    {
                        right. ltac1:(set_solver).
                    }
                }
            }
        }
    }
Qed.

Lemma decouple_does_not_lose_variables
    {Σ : StaticModel}
    et avoid φ σ eqs:
    (φ, σ) = (decouple et avoid eqs) ->
    ∀ (x : variable),
        x ∈ vars_of φ ->
        ∃ (e : Expression2),
            (x,e) ∈ σ
.
Proof.
    revert avoid φ σ eqs.
    induction et; intros avoid φ σ eqs HH1 x HH3.
    {
        simpl in *.
        ltac1:(simplify_eq/=).
        unfold vars_of in HH3; simpl in *.
        unfold vars_of in HH3; simpl in *.
        rewrite elem_of_singleton in HH3.
        subst x. exists a.
        rewrite elem_of_union. left.
        rewrite elem_of_singleton.
        reflexivity.
    }
    {
        simpl in *.
        ltac1:(repeat case_match; simplify_eq/=).
        rewrite vars_of_t_term in HH3.
        clear s.
        revert avoid eqs x l0 l1 H H0 HH3.
        induction l;
            intros avoid eqs x l0 l1 H H0 HH3.
        {
            ltac1:(simplify_eq/=).
            clear -HH3. ltac1:(set_solver).
        }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            ltac1:(repeat case_match; simplify_eq/=).
            destruct (decide (x ∈ vars_of t)) as [Hin|Hnotin].
            {
                specialize (H1 _ _ _ _ (eq_sym H)).
                specialize (H1 x Hin).
                destruct H1 as [e Hxe].
                exists e.
                clear - H3 Hxe.
                revert l1 l2 l3 avoid Hxe H3.
                induction l; intros l1 l2 l3 avoid Hxe H3.
                {
                    ltac1:(simplify_eq/=).
                    exact Hxe.
                }
                {
                    ltac1:(repeat case_match; simplify_eq/=).
                    eapply IHl>[|eapply H0].
                    eapply elem_of_weaken.
                    apply Hxe.
                    eapply transitivity.
                    eapply decouple_extends_eqs.
                    rewrite H. reflexivity.
                }
            }
            {
                rewrite elem_of_union in HH3.
                destruct HH3 as [HH3|HH3].
                {
                    ltac1:(naive_solver).
                }
                {
                    specialize (IHl _ _ _ _ _ H2 H3 HH3).
                    apply IHl.
                }
            }
        }
    }
Qed.

Lemma zip_lookup_fst
    {A B : Type} (l : list A) (l0 : list B) (i : nat) (x : (A*B)):
    length l = length l0 ->
    zip l l0 !! i = Some x ->
    l !! i = Some x.1
.
Proof.
    intros.
    apply lookup_zip_with_Some in H0.
    destruct H0 as [x0 [y [H1 [H2 H3]]]].
    subst x.
    simpl.
    exact H2.
Qed.

Lemma zip_lookup_snd
    {A B : Type} (l : list A) (l0 : list B) (i : nat) (x : (A*B)):
    length l = length l0 ->
    zip l l0 !! i = Some x ->
    l0 !! i = Some x.2
.
Proof.
    intros.
    apply lookup_zip_with_Some in H0.
    destruct H0 as [x0 [y [H1 [H2 H3]]]].
    subst x.
    simpl.
    exact H3.
Qed.

Lemma vars_of_l_subseq_avoid_impl_vars_of_x_subseteq_avoid
    {Σ : StaticModel}
    (l : list (TermOver Expression2))
    (i : nat)
    (et : TermOver Expression2)
    (avoid : gset variable)
    :
    ⋃ (vars_of <$> l) ⊆ avoid ->
    l !! i = Some et ->
    vars_of et ⊆ avoid
.
Proof.
    intros H1 H2.
    apply take_drop_middle in H2.
    rewrite <- H2 in H1. clear H2.
    rewrite fmap_app in H1.
    rewrite fmap_cons in H1.
    rewrite union_list_app in H1.
    rewrite union_list_cons in H1.
    ltac1:(set_solver).
Qed.

Definition piecewise
    {B : Type}
    {_EB : Empty B}
    {_UB : Union B}
    (n : nat)
    (f : forall(i : nat)(iltn : i < n), B)
    :
    B
:=
    let s := pfseqn n in
    let lδ := @fmap list _ _ _ (fun x => (f (proj1_sig x) (proj2_sig x))) s in
    union_list lδ
.

Definition pfnat_S (n : nat) (x : {x' : nat | x' < n }) : {x'' : nat | x'' < (S n)}
:=
    exist _ (S (proj1_sig x)) (proj1 (Nat.succ_lt_mono (proj1_sig x) n) (proj2_sig x))
.

Lemma pfseqn_S (n : nat):
    pfseqn (S n) = (exist _ 0 (Nat.lt_0_succ n))::(pfnat_S n <$> (pfseqn n))
.
Proof.
    unfold pfseqn.
    simpl.
    f_equal.
    {
        erewrite PropExtensionality.proof_irrelevance at 1.
        reflexivity.
    }
    {
        erewrite PropExtensionality.proof_irrelevance at 1.
        erewrite PropExtensionality.proof_irrelevance at 1.
        assert(Hgeneral: forall n' i m pf1 pf2, pfseq0 (S n') (S i) m pf1 = pfnat_S n' <$> pfseq0 n' i m pf2).
        {
            clear n.
            intros n' i m.
            revert n' i.
            induction m; intros n' i pf1 pf2.
            {
                reflexivity.
            }
            {
                simpl.
                f_equal.
                {
                    erewrite PropExtensionality.proof_irrelevance at 1.
                    erewrite PropExtensionality.proof_irrelevance at 1.
                    unfold pfnat_S.
                    simpl.
                    reflexivity.
                }
                {
                    erewrite (IHm n').
                    erewrite PropExtensionality.proof_irrelevance at 1.
                    reflexivity.
                    Unshelve.
                    { ltac1:(lia). }
                    { ltac1:(lia). }
                    { ltac1:(lia). }
                    { ltac1:(lia). }
                }
            }
        }
        apply Hgeneral.
    }
Qed.

Lemma piecewise_S
    {B : Type}
    {_EB : Empty B}
    {_UB : Union B}
    (n : nat)
    (f : forall(i : nat)(iltn : i < S n), B)
:
    piecewise (S n) f = (f 0 (Nat.lt_0_succ n)) ∪ (piecewise n (fun i iltn => f (S i) (proj1 (Nat.succ_lt_mono i n) iltn) ))
.
Proof.
    unfold piecewise.
    rewrite pfseqn_S.
    rewrite fmap_cons.
    rewrite union_list_cons.
    simpl.
    f_equal.
    rewrite <- list_fmap_compose.
    unfold compose.
    reflexivity.
Qed.

Lemma dom_union_list_gmap
    {K V : Type}
    {_ : EqDecision K}
    {_ : Countable K}
    (l : list (gmap K V))
    :
    dom (union_list l) = union_list (fmap dom l)
.
Proof.
    induction l; simpl in *.
    {
        rewrite dom_empty_L.
        reflexivity.
    }
    {
        rewrite dom_union_L.
        rewrite IHl.
        reflexivity.
    }
Qed.

Lemma dom_piecewise
    {K V}
    {_ : EqDecision K}
    {_ : Countable K}
    (n : nat)
    (f : forall(i : nat)(iltn : i < n), gmap K V)
:
    dom (piecewise n f) = piecewise n (fun i iltn => dom (f i iltn))
.
Proof.
    unfold piecewise.
    rewrite dom_union_list_gmap.
    rewrite <- list_fmap_compose.
    unfold compose.
    reflexivity.
Qed.
 
Lemma map_piecewise_difference
    {K V : Type}
    {_ : EqDecision K}
    {_ : Countable K}
    (n : nat)
    (f : forall (i : nat) (iltn: i < n), gmap K V)
    (m : gmap K V)
:
    (piecewise n f ∖ m) = piecewise n (fun i => ((fun x => x ∖ m) ∘ (f i)))
.
Proof.
    unfold piecewise.
    rewrite map_union_list_difference.
    rewrite <- list_fmap_compose.
    reflexivity.
Qed.

Lemma set_piecewise_difference
    {K : Type}
    {_ : EqDecision K}
    {_ : Countable K}
    (n : nat)
    (f : forall (i : nat) (iltn: i < n), gset K)
    (m : gset K)
:
    (piecewise n f ∖ m) = piecewise n (fun i => ((fun x => x ∖ m) ∘ (f i)))
.
Proof.
    unfold piecewise.
    rewrite set_union_list_difference.
    rewrite <- list_fmap_compose.
    reflexivity.
Qed.


Lemma piecewise_extends
    {Σ : StaticModel}
    (n : nat)
    (base_δ : gmap variable (TermOver builtin_value))
    (vals : forall(i : nat)(iltn : i < n), (gmap variable (TermOver builtin_value)))
    :
    (
        forall (i j : nat) (iltn : i < n) (jltn : j < n),
            i <> j ->
            map_same_up_to (dom base_δ) (vals i iltn) (vals j jltn)
    ) ->
    forall (i : nat) (iltn : i < n),
    vals i iltn ⊆ piecewise n vals
.
Proof.
    intros.

    unfold piecewise.
    unfold Valuation2 in *.
    ltac1:(rewrite map_subseteq_spec).
    intros x t Hin.
    eapply union_list_map_same_up_to_lookup with (i := i)>[()|()|apply Hin].
    {
        unfold pairwise.
        intros i0 j0 ai0 aj0 Hi0j0 H1 H2.
        
        apply lookup_lt_Some in H1 as H1'.
        apply lookup_lt_Some in H2 as H2'.
        rewrite length_fmap in H1'.
        rewrite length_fmap in H2'.
        rewrite length_pfseqn in H1'.
        rewrite length_pfseqn in H2'.
        rewrite list_lookup_fmap in H1.
        rewrite list_lookup_fmap in H2.
        destruct (pfseqn n !! i0) eqn:Heq1>[|inversion H1].
        destruct (pfseqn n !! j0) eqn:Heq2>[|inversion H2].
        simpl in H1. simpl in H2.
        apply (inj Some) in H1.
        apply (inj Some) in H2.
        subst ai0.
        subst aj0.
        destruct s as [n1 Hn1].
        destruct s0 as [n2 Hn2].
        simpl.
        apply H.
        apply pfseqn_lookup in Heq1.
        apply pfseqn_lookup in Heq2.
        simpl in *.
        ltac1:(lia).
    }
    {
        rewrite list_lookup_fmap.
        destruct (pfseqn n !! i) eqn:Heq.
        {
            apply pfseqn_lookup in Heq.
            subst i.
            simpl in *.
            apply f_equal.
            apply f_equal.
            apply PropExtensionality.proof_irrelevance.
        }
        {
            apply lookup_ge_None in Heq.
            rewrite length_pfseqn in Heq.
            ltac1:(lia).
        }
    }
Qed.

Lemma piecewise_preserves_sat
    {Σ : StaticModel}
    (n : nat)
    (base_δ : gmap variable (TermOver builtin_value))
    (vals : forall(i : nat)(iltn : i < n), (gmap variable (TermOver builtin_value)))
    (terms : forall(i : nat)(iltn : i < n), TermOver builtin_value)
    (patterns : forall(i : nat)(iltn : i < n), TermOver BuiltinOrVar)
    :
    (
        forall (i j : nat) (iltn : i < n) (jltn : j < n),
            i <> j ->
            map_same_up_to (dom base_δ) (vals i iltn) (vals j jltn)
    ) ->
    (forall(i : nat)(iltn : i < n),
        sat2B (vals i iltn) (terms i iltn) (patterns i iltn)
    ) ->
    forall (i : nat) (iltn : i < n),
    sat2B (piecewise n vals) (terms i iltn) (patterns i iltn)
.
Proof.
    intros Hdisj Hholds i iltn.
    eapply TermOverBoV_satisfies_extensive>[|
        apply (Hholds i iltn)
    ].
    eapply (piecewise_extends n base_δ _ Hdisj).
Qed.




Lemma decouple_preserves_semantics_1
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : listset variable)
    eqs
    (p : ProgramT)    
    (o : NondetValue)
    (δ : Valuation2)
    :
        vars_of et ⊆ vars_of δ -> 
        vars_of δ ⊆ (list_to_set (elements avoid)) -> 
        { δ' : gmap variable (TermOver builtin_value) &
            ((dom δ' ∖ dom δ = list_to_set (fresh_n (count_expr et) (avoid ∪ (fst <$> eqs))))*( 
                vars_of et ⊆ (list_to_set (elements avoid)) ->
                forall (φ : TermOver BuiltinOrVar) σ,
                (φ,σ) = decouple et avoid eqs ->
                forall (t : TermOver builtin_value),
                satisfies δ (p,(o,t)) et ->
            ((satisfies δ' t φ)*(
            ∀ (x : variable) (e : Expression2), (x,e) ∈ σ ->
                (x,e) ∉ eqs ->
                { ot : _ & ((Expression2_evaluate p δ e = Some ot)*((δ' !! x) = Some (ot o)))%type }
        ))%type))%type }
.
Proof.
    revert avoid eqs p o δ.
    ltac1:(induction et using TermOver_rect);
        intros avoid eqs p o δ HH1 HH2.
    {
        simpl in *.
        destruct (Expression2_evaluate p δ a) as [ft'|] eqn:Heq.
        {
            unfold Valuation2 in *.
            remember (δ ∪ ({[(fresh (avoid ∪ (fst <$> eqs))) := (ft' o)]})) as δ'.
            exists δ'.
            split.
            {
                subst δ'.
                rewrite dom_union_L.
                rewrite difference_union_distr_l_L.
                rewrite difference_diag_L.
                rewrite union_empty_l_L.
                rewrite dom_singleton_L.
                apply set_eq.
                intros x.
                rewrite elem_of_difference.
                rewrite elem_of_singleton.
                rewrite elem_of_union.
                rewrite elem_of_singleton.
                rewrite elem_of_empty.
                split; intros HH.
                {
                    destruct HH as [HH1' HH2'].
                    subst x.
                    left.
                    ltac1:(set_solver).
                }
                {
                    destruct HH as [HH | HH].
                    {
                        split.
                        { ltac1:(set_solver). }
                        subst x.
                        intros HContra.
                        unfold vars_of in *; simpl in *.
                        unfold vars_of in *; simpl in *.
                        eapply elem_of_weaken in HContra>[|apply HH2].
                        assert ((fresh (avoid ∪ (fst <$> eqs))) ∉ avoid ∪ (fst <$> eqs)).
                        {
                            apply is_fresh.
                        }
                        ltac1:(set_solver).
                    }
                    { inversion HH. }
                }
            }
            {
                (* ltac1:(rename H0 into Hvo2). *)
                intros Hvo1 φ σ Hφσ t Hsate.
                ltac1:(simplify_eq/=).
                split.
                {
                    unfold satisfies in *; simpl in *.
                    destruct t; ltac1:(simp sat2B); simpl in *.
                    {
                        ltac1:(simp sat2E in Hsate).
                        rewrite Heq in Hsate.
                        rewrite Hsate.
                        unfold Valuation2 in *.
                        rewrite lookup_union_r.
                        {
                            rewrite lookup_singleton.
                            reflexivity.
                        }
                        {
                            rewrite <- not_elem_of_dom.
                            intros HContra.
                            eapply elem_of_weaken in HContra>[|apply HH2].
                            assert (H0: (fresh (avoid ∪ (fst <$> eqs))) ∉ avoid ∪ (fst <$> eqs)).
                            {
                                apply is_fresh.
                            }
                            apply H0. clear H0.
                            ltac1:(set_solver).
                        }
                    }
                    {
                        ltac1:(simp sat2E in Hsate).
                        rewrite Heq in Hsate.
                        rewrite Hsate.
                        unfold Valuation2 in *.
                        rewrite lookup_union_r.
                        {
                            rewrite lookup_singleton.
                            reflexivity.
                        }
                        {
                            rewrite <- not_elem_of_dom.
                            intros HContra.
                            eapply elem_of_weaken in HContra>[|apply HH2].
                            assert (H0: (fresh (avoid ∪ (fst <$> eqs))) ∉ avoid ∪ (fst <$> eqs)).
                            {
                                apply is_fresh.
                            }
                            apply H0. clear H0.
                            ltac1:(set_solver).
                        }
                    }
                }
                {
                    intros x e0 Hx.
                    rewrite elem_of_union in Hx.
                    rewrite elem_of_singleton in Hx.
                    intros HMaybeContra.
                    assert ((x, e0) = (fresh (avoid ∪ (fst <$> eqs)), a)).
                    {
                        ltac1:(set_solver).
                    }
                    (* (destruct Hx as [Hx|Hx])>[|ltac1:(set_solver)]. *)
                    ltac1:(simplify_eq/=).
                    exists ft'.
                    split>[exact Heq|].
                    rewrite lookup_union_r.
                    {
                        unfold Valuation2 in *.
                        rewrite lookup_singleton.
                        reflexivity.
                    }
                    {
                        rewrite <- not_elem_of_dom.
                        intros HContra.
                        eapply elem_of_weaken in HContra>[|apply HH2].
                        assert (H0: (fresh (avoid ∪ (fst <$> eqs))) ∉ avoid ∪ (fst <$> eqs)).
                        {
                            apply is_fresh.
                        }
                        apply H0. clear H0.
                        ltac1:(set_solver).
                    }
                }
            }
        }
        {
            apply Expression2_evaluate_None_inv in Heq.
            ltac1:(exfalso).
            repeat (unfold vars_of in *; simpl in *; ()).
            ltac1:(set_solver).
        }        
    }
    {
        (* TODO *)
    }
Qed.

Lemma decouple_preserves_semantics_1
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : gset variable)
    (p : ProgramT)    
    (o : NondetValue)
    (δ : Valuation2)
    :
        vars_of et ⊆ vars_of δ -> 
        vars_of δ ⊆ avoid -> 
        { δ' : gmap variable (TermOver builtin_value) &
            ((dom δ' ∖ dom δ = list_to_set (fresh_n (count_expr et) (avoid)))*( 
                vars_of et ⊆ avoid ->
                forall (φ : TermOver BuiltinOrVar) σ,
                (φ,σ) = decouple et avoid ->
                forall (t : TermOver builtin_value),
                satisfies δ (p,(o,t)) et ->
            ((satisfies δ' t φ)*(
            ∀ (x : variable) (e : Expression2), (x,e) ∈ σ ->
                { ot : _ & ((Expression2_evaluate p δ e = Some ot)*((δ' !! x) = Some (ot o)))%type }
        ))%type))%type }
.
Proof.
    ltac1:(funelim (decouple et avoid)).
    {
        ltac1:(simp decouple).
        simpl.
        unfold satisfies; simpl.
        destruct (Expression2_evaluate p δ e) as [ft'|] eqn:Heq.
        {
            remember (fresh avoid) as y.
            unfold Valuation2 in *.
            remember (δ ∪ ({[y := (ft' o)]})) as δ'.
            (* remember ((filter (fun ab => ab.1 <> y) δ) ∪ ({[y := (ft' o)]})) as δ'. *)
            exists δ'.
            split.
            {
                subst δ' y.
                rewrite dom_union_L.
                rewrite difference_union_distr_l_L.
                rewrite difference_diag_L.
                rewrite union_empty_l_L.
                rewrite dom_singleton_L.
                apply set_eq.
                intros x.
                rewrite elem_of_difference.
                rewrite elem_of_singleton.
                rewrite elem_of_union.
                rewrite elem_of_singleton.
                rewrite elem_of_empty.
                split; intros HH.
                {
                    destruct HH as [HH1 HH2].
                    subst x.
                    left.
                    ltac1:(set_solver).
                }
                {
                    destruct HH as [HH | HH].
                    {
                        split.
                        { ltac1:(set_solver). }
                        subst x.
                        intros HContra.
                        unfold vars_of in *; simpl in *.
                        unfold vars_of in *; simpl in *.
                        eapply elem_of_weaken in HContra>[|apply H0].
                        assert ((fresh avoid) ∉ avoid).
                        {
                            apply is_fresh.
                        }
                        ltac1:(set_solver).
                    }
                    { inversion HH. }
                }
            }
            {
                ltac1:(rename H0 into Hvo2).
                intros Hvo1 φ σ Hφσ t Hsate.
                ltac1:(simplify_eq/=).
                split.
                {
                    destruct t; ltac1:(simp sat2B); simpl in *.
                    {
                        ltac1:(simp sat2E in Hsate).
                        rewrite Heq in Hsate.
                        rewrite Hsate.
                        unfold Valuation2 in *.
                        rewrite lookup_union_r.
                        {
                            rewrite lookup_singleton.
                            reflexivity.
                        }
                        {
                            rewrite <- not_elem_of_dom.
                            intros HContra.
                            assert (H0: (fresh avoid) ∉ avoid).
                            {
                                apply is_fresh.
                            }
                            apply H0. clear H0.
                            eapply elem_of_weaken.
                            { apply HContra. }
                            exact Hvo2.
                        }
                    }
                    {
                        ltac1:(simp sat2E in Hsate).
                        rewrite Heq in Hsate.
                        rewrite Hsate.
                        unfold Valuation2 in *.
                        rewrite lookup_union_r.
                        {
                            rewrite lookup_singleton.
                            reflexivity.
                        }
                        {
                            rewrite <- not_elem_of_dom.
                            intros HContra.
                            assert (H0: (fresh avoid) ∉ avoid).
                            {
                                apply is_fresh.
                            }
                            apply H0. clear H0.
                            eapply elem_of_weaken.
                            { apply HContra. }
                            exact Hvo2.
                        }
                    }
                }
                {
                    intros x e0 Hx.
                    rewrite elem_of_singleton in Hx.
                    ltac1:(simplify_eq/=).
                    exists ft'.
                    split>[exact Heq|].
                    rewrite lookup_union_r.
                    {
                        unfold Valuation2 in *.
                        rewrite lookup_singleton.
                        reflexivity.
                    }
                    {
                        rewrite <- not_elem_of_dom.
                        intros HContra.
                        assert (H0: (fresh avoid) ∉ avoid).
                        {
                            apply is_fresh.
                        }
                        apply H0. clear H0.
                        eapply elem_of_weaken.
                        { apply HContra. }
                        exact Hvo2.
                    }
                }
            }
        }
        {
            intros Hvo.
            apply Expression2_evaluate_None_inv in Heq.
            ltac1:(exfalso).
            repeat (unfold vars_of in *; simpl in *; ()).
            ltac1:(set_solver).
        }
    }
    {
        intros Hvo1 Hvo2.
        rewrite vars_of_t_term_e in Hvo1.
        (* ltac1:(set(Helper : (forall i et, l !! i = Some et -> vars_of et ⊆ vars_of δ) := _)). *)
        ltac1:(unshelve(epose (_ : (forall (i : nat) (et : TermOver Expression2) (mypf: l !! i = Some et), vars_of et ⊆ vars_of δ)) as Helper)).
        {
            intros i et Hiet.
            abstract(
                apply take_drop_middle in Hiet;
                rewrite <- Hiet in Hvo1;
                rewrite fmap_app in Hvo1;
                rewrite fmap_cons in Hvo1;
                rewrite union_list_app in Hvo1;
                rewrite union_list_cons in Hvo1;
                clear - Hvo1;
                ltac1:(set_solver)
            ).
        }
        ltac1:(unshelve(epose(_ : forall i et, l !! i = Some et -> vars_of δ ⊆ (((avoid ∪ ⋃ (vars_of <$> take i l))))) as Helper2)).
        {
            intros i et Hiet.
            abstract(
                apply take_drop_middle in Hiet;
                assert (Hvo1' := Hvo1);
                rewrite <- Hiet in Hvo1';
                rewrite fmap_app in Hvo1';
                rewrite fmap_cons in Hvo1';
                rewrite union_list_app in Hvo1';
                rewrite union_list_cons in Hvo1';
                clear - Hvo2;
                ltac1:(set_solver)
            ).
        }
        assert(Helper3: forall (i : nat) (iltn : i < length l)(pfet: l !! i = None), False).
        {
            intros i iltn pfet.
            ltac1:(refine(
                let pf' := lookup_ge_None_1 l i pfet in
                match (proj1 (Nat.lt_nge i (length l)) iltn pf')
                with end)
            ).
        }
        assert(Helper4: forall i j a, take i l !! j = Some a -> j < length l).
        {
            intros.
            apply lookup_lt_Some in H.
            rewrite length_take in H.
            ltac1:(lia).
        }
        (* Search lt le. *)
        remember (fix ff (i : nat) (iltn : i < (length l)) : gmap variable (TermOver builtin_value) :=
                match inspect (l !! i) with
                | exist _ None pfet =>
                    match Helper3 i iltn pfet with end
                | exist _ (Some (et)) pfet =>
                    let avoid0 : gset variable := ((avoid ∪ ⋃ (ipmap (take i l) (fun j a pfa => dom (ff j ((Helper4 i j a pfa))))))) in
                    (* let dcpl := decouple et avoid0 in *)
                    let tmp0 := X i et pfet Σ et avoid0 p o δ eq_refl eq_refl (Helper i et pfet) (Helper2 i et pfet) in
                    (projT1 tmp0)
                end
            ) as f.
        remember (piecewise (length l) f) as myδ.
        exists myδ.
        split.
        {
            subst myδ.
            
            assert (Hdomf: forall (i : nat) (iltn : i < length l),
                (dom (f i iltn) ∖ dom δ) = (
                    let avoid0 := avoid ∪ union_list (vars_of <$> take i l) in
                    match (inspect (l !! i)) with
                    | exist _ (Some et) _ =>
                        list_to_set ((fresh_n (count_expr et) (avoid0)))
                    | exist _ None _ => ∅
                    end
                )
            ).
            {
                unfold TermOver in *.
                intros. subst Helper Helper2. simpl.
                destruct (l !! i) eqn:Hli.
                {
                    subst f. simpl.
                    ltac1:(move: (decouple_preserves_semantics_1_subproof Σ l δ Hvo1 i)).
                    ltac1:(move: (decouple_preserves_semantics_1_subproof0 Σ l avoid δ Hvo1 Hvo2 i)).
                    ltac1:(move: (X i)).
                    ltac1:(move: (Helper3 i)).
                    ltac1:(move: erefl).
                    ltac1:(rewrite Hli).
                    intros.
                    match! goal with
                    | [|- difference (dom (projT1 ?s)) _ = _] =>
                        remember $s as pfs
                    end.
                    destruct pfs as [δ' Hδ'].
                    simpl.
                    destruct Hδ' as [H1δ' H2δ'].
                    exact H1δ'.
                }
                {
                    apply lookup_ge_None in Hli.
                    ltac1:(exfalso; clear - Hli iltn).
                    ltac1:(lia).
                }
            }
            simpl in Hdomf.
            rewrite dom_piecewise.
            unfold Valuation2 in *.
            rewrite set_piecewise_difference.
            unfold compose.
            simpl.
            (* This should be possible to handle using single setoid_rewrite: *)
            (* setoid_rewrite Hdomf. *)
            (* but it didn't work for me *)
            match! goal with
            | [|- piecewise _ ?f = _] =>
                remember $f as g
            end.
            assert(Hg: g = fun i pf => match l !! i with None => empty | Some et => list_to_set (fresh_n (count_expr et) ((avoid ∪ ⋃ (vars_of <$> take i l))))end).
            {
                subst g.
                apply functional_extensionality_dep.
                intros x0.
                apply functional_extensionality_dep.
                intros x1.
                rewrite Hdomf.
                reflexivity.
            }
            rewrite Hg.
            simpl.
            assert (Havoid1: ⋃ (vars_of <$> l) ⊆ avoid).
            {
                ltac1:(set_solver).
            }
            match! goal with
            | [|- piecewise _ ?f = _] =>
                assert(Hf: $f = (fun (i : nat)(pfi: i < length l) => list_to_set(match l !! i with None => [] | Some et => (fresh_n (count_expr et) avoid)  end)))
            end.
            {
                apply functional_extensionality_dep.
                intros i.
                apply functional_extensionality_dep.
                intros pfi.
                destruct (l !! i) eqn:Hli.
                {
                    apply f_equal.
                    apply f_equal.
                    assert (Htmp1: vars_of (take i l) ⊆ vars_of l).
                    {
                        rewrite <- (take_drop i l) at 2.
                        unfold vars_of; simpl.
                        rewrite fmap_app.
                        rewrite union_list_app.
                        ltac1:(set_solver).
                    }
                    ltac1:(set_solver).
                }
                { reflexivity. }
            }
            rewrite Hf.
            clear Hf.
            (* 
            induction l; simpl.
            {
                reflexivity.
            }
            {
                rewrite fresh_n_plus.
                rewrite piecewise_S.
                simpl.
                rewrite list_to_set_app_L.
            }
            unfold piecewise.
            unfold union_list.
            rewrite foldr_fmap. *)
            (* About list_to_set. *)
            (* Search foldr fmap. *)
            clear X Heqf Heqcall Hvo2 Helper2.
            clear Hdomf f g Heqf Heqg Hg.
            assert(Htmp1: count_expr = length ∘ collect_expr).
            {
                apply functional_extensionality.
                apply count_expr_collect_expr.
            }
            rewrite Htmp1.
            clear Htmp1.
            (* unfold compose. *)
            
            revert Havoid1.
            revert avoid.
            clear.
            remember (sum_list_with (length ∘ collect_expr) l) as cnt.
            assert(Hcnt: sum_list_with (length ∘ collect_expr) l <= cnt).
            {
                ltac1:(lia).
            }
            clear Hcnt.
            (* clear Heqcnt. *)
            revert Heqcnt.
            revert l.
            induction cnt; intros l Heqcnt.
            {
                revert Heqcnt.
                induction l; intros Hcnt; simpl in *.
                {
                    intros _ _. reflexivity.
                }
                {
                    destruct a; simpl in *.
                    {
                        ltac1:(lia).
                    }
                    {
                        intros avoid Havoid.
                        rewrite piecewise_S.
                        simpl.
                        assert (Hlen: length (concat (collect_expr <$> l0)) = 0).
                        {
                            ltac1:(lia).
                        }
                        rewrite Hlen.
                        simpl.
                        rewrite concat_length in Hcnt.
                        specialize (IHl ltac:(lia)).
                        rewrite vars_of_t_term_e in Havoid.
                        specialize (IHl avoid ltac:(set_solver)).
                        rewrite <- IHl.
                        ltac1:(set_solver).
                    }
                }
            }
            {
                intros avoid Havoid.
                destruct l; simpl in *.
                {
                    ltac1:(lia).
                }
                {
                    rewrite piecewise_S.
                    simpl.
                    destruct t; simpl in *.
                    {
                        rewrite IHcnt.
                    }
                }
            }
            (* assert(Hind: forall (avoid' : gset variable) (et : TermOver' Expression2), vars_of et ⊆ avoid' -> fresh_n (count_expr et) avoid') *)
            induction l; intros avoid Havoid1.
            { 
                simpl.
                unfold piecewise.
                unfold pfseqn.
                simpl. reflexivity.
            }
            {
                simpl.
                rewrite fresh_n_plus.
                rewrite list_to_set_app_L.
                rewrite piecewise_S.
                simpl.

                rewrite IHl.


                f_equal.
                destruct a.
                {
                    simpl in *.
                    rewrite IHl.
                }
                rewrite IHl.
                apply f_equal.
                apply f_equal.

                destruct a.
                {
                    simpl in *.
                    destruct l.
                    {
                        simpl in *.
                        reflexivity.
                    }
                    {
                        simpl in *.
                    }
                    rewrite <- IHl.
                    clear IHl.
                    apply f_equal.
                    apply functional_extensionality_dep.
                    intros i.
                    apply functional_extensionality_dep.
                    intros pfi.
                    destruct (l !! i)>[|reflexivity].
                    apply f_equal.
                    apply f_equal.
                    destruct l.
                    {
                        simpl in *.
                        destruct i; simpl in *.
                        {
                            ltac1:(lia).
                        }
                        {
                            ltac1:(lia).
                        }
                    }
                    {
                        simpl in *.
                        destruct i; simpl in *.
                        {

                        }
                        {

                        }
                    }
                    assert (Htmp1: vars_of (take i l) ⊆ vars_of l).
                    {
                        rewrite <- (take_drop i l) at 2.
                        unfold vars_of; simpl.
                        rewrite fmap_app.
                        rewrite union_list_app.
                        ltac1:(set_solver).
                    }
                    match! goal with
                    | [|- ?l = ?r] =>
                        assert(Htmp: $l = avoid)
                    end.
                    {
                        ltac1:(set_solver).
                    }
                    rewrite Htmp.
                    clear Htmp Htmp1.
                    
                }
                {

                }


                rewrite <- IHl at 2.
                (* rewrite IHl. *)
                (* rewrite <- IHl. *)
                (* rewrite <- IHl. *)
                specialize (IHl (((*list_to_set (fresh_n (count_expr a) avoid)*) ∪ avoid ∪ (vars_of a)))).
                (* specialize (IHl (avoid ∪ vars_of a ∪ ⋃ (vars_of <$> l))). *)
                ltac1:(ospecialize (IHl _)).
                {
                    ltac1:(set_solver).
                }
                (* rewrite IHl. *)

                rewrite fmap_cons in Havoid1.
                rewrite union_list_cons in Havoid1.
                match! Constr.type (Control.hyp ident:(IHl)) with
                | (_ = (list_to_set (fresh_n _ ?l))) =>
                     match! goal with
                    |[|- _= (list_to_set (fresh_n _ ?r))] =>
                        assert(H'lr: $l = $r)
                    end
                end.
                {
                    ltac1:(set_solver).
                }
                rewrite H'lr in IHl.
                rewrite <- IHl.
                f_equal.
                apply functional_extensionality_dep.
                intros i.
                apply functional_extensionality_dep.
                intro Hiltlen.
                destruct (l !! i) eqn:Heq.
                {
                    apply f_equal.
                    apply f_equal.
                    clear IHl.
                    assert(Htmp: ⋃ (vars_of <$> take i l) ⊆ ⋃ (vars_of <$> l)).
                    {
                        clear.
                        rewrite <- (take_drop i l) at 2.
                        rewrite fmap_app.
                        rewrite union_list_app.
                        ltac1:(set_solver).
                    }
                    match! goal with
                    | [|- _ = ?r] => assert(Htmp2: $r = (list_to_set (fresh_n (count_expr a) avoid)) ∪ avoid)
                    end.
                    {
                        ltac1:(set_solver).
                    }
                    rewrite Htmp2. clear Htmp2.
                    ltac1:(set_solver).
                    apply set_eq.
                    repeat (setoid_rewrite elem_of_union).
                    (* ltac1:(set_solver). *)
                }
                {
                    reflexivity.
                }
                
                (* specialize (IHl _ Havoid1). *)
                (*                 
                simpl in f.
                simpl in g.
                remember (fun (i : nat)(iltn : i < length l) => f i (Nat.lt_lt_succ_r _ _ iltn)) as f'.
                remember (fun (i : nat)(iltn : i < length l) => g i (Nat.lt_lt_succ_r _ _ iltn)) as g'.
                specialize (IHl f').
                specialize (IHl g'). *)
                rewrite <- IHl.
                f_equal.
                apply functional_extensionality_dep.
                intros i.
                apply functional_extensionality_dep.
                intros pfi.
                destruct (l !! i) eqn:Hli.
                {
                    apply set_eq.
                    intros x.
                    rewrite elem_of_list_to_set.
                    rewrite elem_of_list_to_set.
                    match! goal with
                    | [|- (elem_of _ (fresh_n _ ?l)) <-> (elem_of _ (fresh_n _ ?r))] =>
                        assert(Hlr: $l = $r)
                    end.
                    {
                        apply set_eq.
                        intros x0.
                        rewrite elem_of_union.
                        rewrite elem_of_union.
                        rewrite elem_of_union.
                        rewrite elem_of_union.
                        rewrite elem_of_list_to_set.
                        split.
                        {
                            intros HH.
                            destruct HH as [HH|HH].
                            {
                                ltac1:(set_solver).
                            }
                            {
                                destruct HH as [HH|HH].
                                {
                                    clear IHl.
                                    rewrite fmap_cons in Havoid1.
                                    rewrite union_list_cons in Havoid1.
                                    left. right.
                                    clear - HH Havoid1.
                                    ltac1:(set_solver).
                                }
                                {
                                    ltac1:(set_solver).
                                }
                            }
                        }
                        {
                            intros HH.
                            destruct (decide (x0 ∈ ⋃ (vars_of <$> take i l))) as [Hin|Hnotin].
                            {
                                right. right. apply Hin.
                            }
                            {
                                destruct HH as [HH|HH].
                                {
                                    destruct (decide (x0 ∈ avoid)) as [Hin'|Hnotin'].
                                    {
                                        left. apply Hin'.
                                    }
                                    {
                                        right.
                                        left.
                                        destruct HH as [HH|HH].
                                        {
                                            rewrite fmap_cons in Havoid1.
                                            rewrite union_list_cons in Havoid1.
                                            ltac1:(exfalso).
                                        }
                                        {
                                            ltac1:(exfalso; clear -HH Hnotin'; set_solver).
                                        }
                                    }
                                }
                                {
                                    ltac1:(exfalso; clear - HH Hnotin; set_solver).
                                }
                            }
                            destruct HH as [HH|HH].
                            {
                                destruct HH as [HH|HH].
                                {
                                    rewrite fmap_cons in Havoid1.
                                    rewrite union_list_cons in Havoid1.
                                    left.
                                    eapply elem_of_weaken>[|apply Havoid1].
                                    rewrite elem_of_union.
                                    right.
                                    Search fresh_n.
                                }
                                {

                                }
                            }
                            {

                            }
                        }
                    }
                    (* ltac1:(set_solver). *)
                }
                {
                    reflexivity.
                }
            }
        }
        {
            intros φ σ Hφσ t Hsatt Hvo3.
            inversion Hφσ; subst φ σ; clear Hφσ.
            simpl in *.
            ltac1:(simp decouple).
            simpl.
            destruct t; simpl in *.
            {
                unfold satisfies in Hsatt; simpl in Hsatt.
                ltac1:(simp sat2E in Hsatt).
                inversion Hsatt.
            }
            unfold satisfies in Hsatt; simpl in Hsatt.
            ltac1:(simp sat2E in Hsatt).
            destruct Hsatt as [Hsatt1 [Hsatt2 Hsatt3]].
            subst s0.
            split.
            {
                unfold satisfies; simpl.
                ltac1:(simp sat2B).
                split>[reflexivity|].
                split.
                {
                    rewrite length_fmap.
                    rewrite ipmap_length.
                    exact Hsatt2.
                }
                {
                    intros i t' φ' HH1 HH2.
                    subst myδ.
                    eapply TermOverBoV_satisfies_extensive.
                    {
                        apply piecewise_extends with (base_δ := δ).
                        intros.
                        unfold map_same_up_to.
                    }
                    Search satisfies.
                    Check piecewise_extends.
                    eapply piecewise_preserves_sat.
                }
            }
            {

            }
        }
    }

(* 
    intros Hvet.
    ltac1:(funelim (decouple et avoid)).
    {
        intros Hφσ δ t p o H1e H2e.
        ltac1:(simp decouple in Hφσ).
        simpl in H1e.
        (* inversion H; subst; clear H. *)
        unfold satisfies in H1e; simpl in H1e.
        ltac1:(simp sat2E in H1e).
        destruct (Expression2_evaluate p δ e) as [ft'|] eqn:Heq.
        {
            remember (fresh avoid) as y.
            unfold Valuation2 in *.
            remember ((filter (fun ab => ab.1 <> y) δ) ∪ ({[y := t]}) ) as δ'.
            exists δ'.
            ltac1:(simp decouple in Hφσ).
            simpl in Hφσ.
            inversion Hφσ; subst; clear Hφσ.
            split.
            {
                unfold satisfies; simpl.
                ltac1:(simp sat2B).
                simpl.
                unfold Valuation2 in *.
                rewrite lookup_union_r.
                {
                    rewrite lookup_singleton.
                    reflexivity.
                }
                {
                    rewrite map_lookup_filter.
                    simpl.
                    rewrite bind_None.
                    unfold vars_of in Hvet; simpl in Hvet.
                    unfold vars_of in Hvet; simpl in Hvet.
                    destruct (decide (fresh avoid ∈ dom δ)) as [Hin|Hnotin].
                    {
                        right.
                        rewrite elem_of_dom in Hin.
                        destruct Hin as [x Hx].
                        exists x.
                        split>[exact Hx|].
                        ltac1:(simplify_option_eq).
                        reflexivity.
                    }
                    {
                        left.
                        apply not_elem_of_dom_1.
                        apply Hnotin.                        
                    }
                }
            }
            {
                intros x e0 Hxe0.
                subst.
                rewrite elem_of_singleton in Hxe0.
                inversion Hxe0; subst; clear Hxe0.
                exists ft'.
                split>[apply Heq|].
                rewrite lookup_union.
                rewrite lookup_singleton.
                rewrite union_Some_r.
                apply f_equal.
                rewrite map_lookup_filter.
                simpl.
                ltac1:(simplify_option_eq).
                rewrite not_elem_of_dom_1.
                { simpl. reflexivity. }
                {
                    unfold vars_of in H2e; simpl in H2e.
                    (* ltac1:(rewrite H2e). *)
                    unfold vars_of in Hvet; simpl in Hvet.
                    assert (H := is_fresh avoid).
                    intros HContra. apply H. clear H.
                    eapply elem_of_weaken>[apply HContra|].
                    exact H2e.
                }
            }
        }
        {
            inversion H1e.
        }
    }
    {
        (* Search sigT. *)
        intros Hd.
        ltac1:(simp decouple in Hd).
        simpl in Hd.
        inversion Hd; subst; clear Hd.
        intros δ t p o Hsat Hvars.
        rewrite vars_of_t_term_e in Hvet.
        (* assert (Hsat' := Hsat). *)
        unfold satisfies in Hsat; simpl in Hsat.
        destruct t;
            ltac1:(simp sat2E in Hsat);
            simpl in Hsat.
        {
            inversion Hsat.
        }
        {
            destruct Hsat as [Hsat1 [Hsat2 Hsat3]].
            subst s0.
            (* About eq_ind. *)
            remember (fun (i : nat) (iltn : i < (length l)) =>
                match inspect (l !! i) with
                | exist _ None pfet =>
                    let pf' := lookup_ge_None_1 l i pfet in
                    match (proj1 (Nat.lt_nge i (length l)) iltn pf')
                    with end
                | exist _ (Some (et)) pfet =>
                    match (inspect (l0 !! i)) with
                    | exist _ None pft =>
                        let pf' := lookup_ge_None_1 l0 i pft in
                        let pf'' := eq_ind _ (fun x => x <= i) pf' _ Hsat2 in
                        match (proj1 (Nat.lt_nge i (length l)) iltn pf'')
                        with end
                    | exist _ (Some t) pft =>
                        let avoid0 := ((avoid ∪ ⋃ (vars_of <$> take i l))) in
                        let dcpl := decouple et avoid0 in
                        let pfavoid0 := @vars_of_l_subseq_avoid_impl_vars_of_x_subseteq_avoid Σ l i et avoid Hvet pfet in
                        let tmp0 := X i et pfet Σ et avoid0 dcpl.1 dcpl.2 pfavoid0 in
                        (* let tmp := tmp0 eq_refl eq_refl (eq_sym (surjective_pairing (decouple et avoid0))) in *)
                        0
                    end
                end
            ) as f.
            About piecewise.
            Check piecewise_preserves_sat.
            (* Check Hvars. *)
            (* About surjective_pairing. *)
            (* About eq_sym.
            remember (
                (fun (i : nat) (arg : ((TermOver' Expression2 * TermOver' builtin_value))%type) (pf : (zip l l0) !! i = Some arg) =>
                let et := arg.1 in
                let t := arg.2 in
                let pf' := (proj1 (lookup_zip_with_Some pair l l0 i arg) pf) in
                let pfet : l !! i = Some et := (zip_lookup_fst l l0 i arg (eq_sym Hsat2) pf) in
                let pft : l0 !! i = Some t := (zip_lookup_snd l l0 i arg (eq_sym Hsat2) pf) in
                let avoidi : (gset variable) := avoid ∪ (union_list (vars_of <$> take i l)) in
                let pfvars1 : ((vars_of et) ⊆ avoidi) := vars_of_l_subseq_avoid_impl_vars_of_x_subseteq_avoid l i et avoid Hvet pfet in
                let pfsat (*satisfies δ (p, (o, t)) et*) := Hsat3 i t et pfet pft in
                let tmp := (X i et pfet Σ et avoidi) in
                let tmp2 := (tmp ((decouple et avoidi)).1 ((decouple et avoidi)).2 pfvars1) in
                let tmp3 := (tmp2 eq_refl eq_refl (@eq_sym _ _ _ (surjective_pairing (decouple et avoidi))) ) in 
                let tmp4 := (tmp3 δ t p o pfsat Hvars) in
                (* tmp4 *)
                (projT1 tmp4) 0
                )
            ) as myf. *)
            (* ltac1:(remember (ipmap (zip l l0) (fun i arg pf =>
                let et := arg.1 in
                let t := arg.2 in
                let pf' := (proj1 (lookup_zip_with_Some pair l l0 i arg) pf) in
                let pfet : l !! i = Some et := (zip_lookup_fst l l0 i arg (eq_sym Hsat2) pf) in
                let pft : l0 !! i = Some t := (zip_lookup_snd l l0 i arg (eq_sym Hsat2) pf) in
                let avoidi : (gset variable) := avoid ∪ (union_list (vars_of <$> take i l)) in
                let pfvars1 : ((vars_of et) ⊆ avoidi) := vars_of_l_subseq_avoid_impl_vars_of_x_subseteq_avoid l i et avoid Hvet pfet in
                let pfsat (*satisfies δ (p, (o, t)) et*) := Hsat3 i t et pfet pft in
                let tmp := (X i et pfet Σ et avoidi) in
                let tmp2 := (tmp ((decouple et avoidi)).1 ((decouple et avoidi)).2 pfvars1) in
                let tmp3 := (tmp2 eq_refl eq_refl (@eq_sym _ _ _ (surjective_pairing (decouple et avoidi))) ) in 
                let tmp4 := (tmp3 δ t p o pfsat Hvars) in
                tmp4
                (* (projT1 tmp4) *)
            )) as lδ). *)
            (* assert(mIH: forall (i : nat)(eti : TermOver Expression2)(ti : TermOver builtin_value),
                l !! i = Some eti -> l0 !! i = Some ti ->
                {δi : gmap variable (TermOver builtin_value) & ((satisfies δi ti eti)*(True))%type}
            ). *)
            unfold satisfies; simpl.
            ltac1:(simp sat2B).
        }
    } *)

Qed.
