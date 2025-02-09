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


Equations? decouple
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : gset variable)
    :
    ((TermOver BuiltinOrVar)*(listset (variable * Expression2 )))%type
    by wf (TermOver_size et) lt
:=
    decouple (t_over e) avoid :=
        let y : variable := fresh (avoid) in
        (t_over (bov_variable y), singleton (y,e))
    ;
    decouple (t_term s l) avoid :=
        let l'' := ipmap l (fun (i : nat) (x : TermOver Expression2) (pf : l !! i = Some x) =>
            let avoidi := avoid ∪ (union_list (vars_of <$> (take i l))) in
            let pi_sigmai := decouple x avoidi in
            pi_sigmai
        ) in
    (t_term s (fmap fst l''), union_list (fmap snd l''))
.
Proof.
    apply take_drop_middle in pf.
    rewrite <- pf.
    rewrite sum_list_with_compose.
    unfold compose.
    rewrite sum_list_with_S.
    rewrite sum_list_fmap.
    rewrite sum_list_with_app.
    rewrite length_fmap.
    rewrite length_app.
    simpl.
    ltac1:(lia).
Qed.


Lemma decouple_avoids
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : gset variable)
    :
    (vars_of (decouple et avoid).1) ## avoid
.
Proof.
    ltac1:(funelim (decouple et avoid)).
    {
        ltac1:(simp decouple).
        simpl.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        rewrite disjoint_singleton_l.
        rewrite <- elem_of_elements.
        apply infinite_is_fresh.
    }
    {
        ltac1:(simp decouple).
        simpl.
        unfold vars_of; simpl.
        rewrite elem_of_disjoint.
        intros x H1x H2x.
        rewrite elem_of_union_list in H1x.
        destruct H1x as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        rewrite elem_of_list_lookup in H2y.
        destruct H2y as [i Hi].
        subst.
        rewrite list_lookup_fmap in Hi.
        rewrite fmap_Some in Hi.
        destruct Hi as [[t ls][HH1 HH2]].
        simpl in *; subst.
        destruct (l !! i) eqn:Heq.
        {
            eapply ipmap_lookup in Heq as Heq'.
            ltac1:(setoid_rewrite HH1 in Heq').
            destruct Heq' as [b [H1b H2b]].
            specialize (H2b Heq).
            apply (inj Some) in H1b.
            subst b.
            specialize (H _ _ Heq Σ t0).
            simpl in H.
            match! (Constr.type (Control.hyp ident:(H2b))) with
            | ( _ = decouple _ ?a) =>
                specialize (H $a)
            end.
            specialize (H eq_refl).
            specialize (H eq_refl).
            rewrite <- H2b in H.
            simpl in H.
            ltac1:(set_solver).
        }
        {
            apply lookup_lt_Some in HH1 as HH1'.
            rewrite ipmap_length in HH1'.
            apply lookup_ge_None in Heq.
            ltac1:(lia).
        }
    }
Qed.

Lemma decoupled_uses_only_original_vars
    {Σ : StaticModel}
    et avoid φ σ x e:
    (φ, σ) = (decouple et avoid) ->
    (x,e) ∈ σ ->
    vars_of e ⊆ vars_of et
.
Proof.
    ltac1:(funelim (decouple et avoid)).
    {
        intros H1 H2.
        ltac1:(simp decouple in H1).
        simpl in H1.
        inversion H1; subst; clear H1.
        rewrite elem_of_singleton in H2.
        inversion H2; subst; clear H2.
        unfold vars_of; simpl.
        unfold vars_of; simpl.
        apply reflexivity.
    }
    {
        intros H1 H2.
        ltac1:(simp decouple in H1).
        simpl in H1.
        inversion H1; subst; clear H1.
        rewrite elem_of_union_list in H2.
        destruct H2 as [X [H1X H2X]].
        simpl in H1X.
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst X.
        rewrite elem_of_list_lookup in H2y.
        destruct H2y as [i Hi].
        destruct (l !! i) eqn:Hli.
        {
            eapply ipmap_lookup in Hli as Hli'.
            rewrite Hi in Hli'.
            destruct Hli' as [b [H1b H2b]].
            apply (inj Some) in H1b.
            subst y.
            specialize (H2b Hli).
            destruct b as [φ σ].
            specialize (H i t Hli Σ t (avoid ∪ ⋃ (vars_of <$> take i l)) φ σ x e eq_refl eq_refl H2b H2X).
            eapply transitivity>[apply H|].
            eapply take_drop_middle in Hli as Hli'.
            rewrite <- Hli'. clear Hli'.
            simpl.
            rewrite vars_of_t_term_e.
            rewrite fmap_app.
            rewrite fmap_cons.
            rewrite union_list_app.
            rewrite union_list_cons.
            clear.
            ltac1:(set_solver).
        }
        {
            ltac1:(exfalso).
            apply lookup_ge_None in Hli.
            apply lookup_lt_Some in Hi.
            rewrite ipmap_length in Hi.
            ltac1:(lia).
        }
    }
Qed.

Lemma decouple_does_not_lose_variables
    {Σ : StaticModel}
    et avoid φ σ:
    (φ, σ) = (decouple et avoid) ->
    ∀ (x : variable),
        x ∈ vars_of φ ->
        ∃ (e : Expression2),
            (x,e) ∈ σ
.
Proof.
    ltac1:(funelim (decouple et avoid)).
    {
        intros H1 x Hx.
        ltac1:(simp decouple in H1).
        simpl in H1.
        inversion H1; subst; clear H1.
        unfold vars_of in Hx; simpl in Hx.
        unfold vars_of in Hx; simpl in Hx.
        rewrite elem_of_singleton in Hx.
        subst x.
        exists e.
        rewrite elem_of_singleton.
        reflexivity.
    }
    {
        intros H1 x Hx.
        ltac1:(simp decouple in H1).
        simpl in H1.
        inversion H1; subst; clear H1.
        rewrite vars_of_t_term in Hx.
        rewrite elem_of_union_list in Hx.
        destruct Hx as [X [H1X H2X]].
        rewrite elem_of_list_fmap in H1X.
        destruct H1X as [y [H1y H2y]].
        subst X.
        rewrite elem_of_list_fmap in H2y.
        destruct H2y as [y' [H1y' H2y']].
        subst y.
        rewrite elem_of_list_lookup in H2y'.
        destruct H2y' as [i Hi].
        destruct (l !! i) eqn:Heq.
        {
            eapply ipmap_lookup in Heq as Heq'.
            rewrite Hi in Heq'.
            destruct Heq' as [[φ σ][H1 H2]].
            specialize (H2 Heq).
            apply (inj Some) in H1.
            subst y'.
            specialize (H i t Heq Σ t (avoid ∪ ⋃ (vars_of <$> take i l)) φ σ eq_refl eq_refl).
            specialize (H H2 x H2X).
            destruct H as [e He].
            exists e.
            ltac1:(setoid_rewrite elem_of_union_list).
            ltac1:(setoid_rewrite elem_of_list_fmap).
            ltac1:(setoid_rewrite elem_of_list_lookup at 1).
            exists σ.
            split.
            {
                exists (φ, σ).
                split.
                { reflexivity. }
                {
                    exists i.
                    apply Hi.
                }
            }
            {
                exact He.
            }
        }
        {
            ltac1:(exfalso).
            apply lookup_ge_None in Heq.
            apply lookup_lt_Some in Hi.
            rewrite ipmap_length in Hi.
            ltac1:(lia).
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

Lemma decouple_preserves_semantics_1
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : gset variable)
    (φ : TermOver BuiltinOrVar)
    σ
    :
    vars_of et ⊆ avoid ->
    (φ,σ) = decouple et avoid ->
    forall (δ : Valuation2) (t : TermOver builtin_value) (p : ProgramT) (o : NondetValue),
        satisfies δ (p,(o,t)) et ->
        vars_of δ ⊆ avoid ->
        { δ' : gmap variable (TermOver builtin_value) & ((satisfies δ' t φ)*(
            ∀ (x : variable) (e : Expression2), (x,e) ∈ σ ->
                ∃ ot, Expression2_evaluate p δ e = Some ot /\
                (δ' !! x) = Some (ot o)
        ))%type }
.
Proof.
    intros Hvet.
    ltac1:(funelim (decouple et avoid)).
    {
        intros Hφσ δ t p o H1e H2e.
        ltac1:(simp decouple in H).
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
        intros Hd.
        ltac1:(simp decouple in Hd).
        simpl in Hd.
        inversion Hd; subst; clear Hd.
        intros δ t p o Hsat Hvars.
        rewrite vars_of_t_term_e in Hvet.
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
            About lookup_zip_with_Some.
            remember (ipmap (zip l l0) (fun i x pf =>
                let et := x.1 in
                let t := x.2 in
                let pf' := (proj1 (lookup_zip_with_Some pair l l0 i x) pf) in
                let pfet : l !! i = Some et := _ in
                let tmp := (X i et) in
                0
            )) as lδ.
            (* assert(mIH: forall (i : nat)(eti : TermOver Expression2)(ti : TermOver builtin_value),
                l !! i = Some eti -> l0 !! i = Some ti ->
                {δi : gmap variable (TermOver builtin_value) & ((satisfies δi ti eti)*(True))%type}
            ). *)
            unfold satisfies; simpl.
            ltac1:(simp sat2B).
        }
    }

Qed.
