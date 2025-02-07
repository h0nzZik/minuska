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
        (* unfold vars_of; simpl. *)
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

