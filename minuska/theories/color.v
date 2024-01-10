From Minuska Require Import
    prelude
    spec_syntax
.

Require Import Coq.Logic.ProofIrrelevance.

From CoLoR Require Import
    Term.Varyadic.VSignature
    Term.Varyadic.VTerm
.

Inductive m2c_sig_symbols (Σ : spec_syntax.StaticModel) : Type :=
| c_sym_symbol (s : @spec_syntax.symbol Σ)
| c_sym_builtin_value
    (b : (@spec_syntax.builtin_value
        (@spec_syntax.symbol Σ)
        (@spec_syntax.symbols Σ)
        (@spec_syntax.builtin Σ))
    )
.

#[global]
Instance m2c_sig_symbols_eqdec
    (Σ : spec_syntax.StaticModel)
    : EqDecision (m2c_sig_symbols Σ)
.
Proof.
    ltac1:(solve_decision).
Qed.

Definition is_symbol
    {Σ : spec_syntax.StaticModel}
    (s : m2c_sig_symbols Σ)
    : Prop
:=
match s with
| c_sym_symbol _ _ => True
| c_sym_builtin_value _ _ => False
end
.

Definition beq_m2c_sig_symbols
    (Σ : spec_syntax.StaticModel)
    (a b : m2c_sig_symbols Σ)
    : bool
:= bool_decide (a = b).

Lemma beq_m2c_sig_symbols_ok
    (Σ : spec_syntax.StaticModel)
    :
    ∀ x y : (m2c_sig_symbols Σ),
        beq_m2c_sig_symbols Σ x y = true ↔ x = y
.
Proof.
    intros x y.
    unfold beq_m2c_sig_symbols.
    apply bool_decide_eq_true.
Qed.


Definition m2c_sig
    (Σ : spec_syntax.StaticModel)
    : VSignature.Signature
:=
    @VSignature.mkSignature
        (m2c_sig_symbols Σ)
        (beq_m2c_sig_symbols Σ)
        (beq_m2c_sig_symbols_ok Σ)
.

Coercion m2c_sig : spec_syntax.StaticModel >-> VSignature.Signature.

Print VTerm.term.

Definition vterm_is_closed
    {Σ : spec_syntax.StaticModel}
    (t : VTerm.term Σ)
    : Prop
:= @VTerm.term_rect
    Σ
    (fun _ => Prop)
    (fun _ => Prop)
    (fun (n:nat) => False)
    (fun sym l tf => tf)
    True
    (fun _ _ => and)
    t
.

Lemma vterm_is_closed_implies_vterm_is_not_var
    {Σ : spec_syntax.StaticModel}
    (t : VTerm.term Σ)
    : vterm_is_closed t -> forall v, t <> Var v
.
Proof.
    intros H1 v H2.
    subst t.
    simpl in H1.
    exact H1.
Qed.

Definition closed_vterm_proj_sym
    {Σ : spec_syntax.StaticModel}
    ( ct : { t : VTerm.term Σ | vterm_is_closed t })
    : VSignature.symbol (m2c_sig Σ)
:=
let t := `ct in
match inspect t with
| @exist _ _ (Var v) pfeq =>
    match vterm_is_closed_implies_vterm_is_not_var t (proj2_sig ct) v pfeq with
    end
| @exist _ _ (Fun s _) _ => s
end
.

Definition closed_vterm_proj_args0
    {Σ : spec_syntax.StaticModel}
    ( ct : { t : VTerm.term Σ | vterm_is_closed t })
    : list (VTerm.term Σ)
:=
let t := `ct in
match inspect t with
| @exist _ _ (Var v) pfeq =>
    match vterm_is_closed_implies_vterm_is_not_var t (proj2_sig ct) v pfeq with
    end
| @exist _ _ (Fun _ args) _ => args
end
.

Lemma closed_vterm_proj_args0_closed
    {Σ : spec_syntax.StaticModel}
    ( ct : { t : VTerm.term Σ | vterm_is_closed t })
    : Forall vterm_is_closed (closed_vterm_proj_args0 ct)
.
Proof.
    rewrite (sig_eta ct).
    remember (proj2_sig ct) as pf.
    clear Heqpf.
    remember (`ct) as t.
    clear Heqt ct.

    destruct t.
    {
        cbn in pf.
        inversion pf.
    }
    cbn.
    induction l.
    {
        apply Forall_nil.
    }
    {
        cbn in pf.
        destruct pf as [pf1 pf2].
        apply Forall_cons.
        {
            apply pf1.
        }
        {
            apply IHl.
            apply pf2.
        }
    }
Qed.

Lemma vterm_is_closed_Fun
    {Σ : spec_syntax.StaticModel}
    s
    (l: list (term Σ)) :
    Forall vterm_is_closed l <->
    @vterm_is_closed Σ (@VTerm.Fun Σ s l)
.
Proof.
    induction l; cbn.
    { split; intros H. exact I. apply Forall_nil. }
    {
        rewrite list.Forall_cons.
        ltac1:(naive_solver).
    }
Qed.

Program Fixpoint m2c_AppliedOperator'_symbol_builtin_rev
    {Σ : spec_syntax.StaticModel}
    (g : AppliedOperator' spec_syntax.symbol builtin_value)
    : { t : VTerm.term Σ | vterm_is_closed t }
:=
match g with
| ao_operator s => @exist _ _ (@VTerm.Fun Σ (c_sym_symbol Σ s) []) _
| ao_app_operand aps b =>
    let tpf : { t : VTerm.term Σ | vterm_is_closed t }
        := m2c_AppliedOperator'_symbol_builtin_rev aps in
    let sym : symbol Σ
        := closed_vterm_proj_sym tpf in
    let args : list (VTerm.term Σ)
        := closed_vterm_proj_args0 tpf in
    let pf
        := closed_vterm_proj_args0_closed tpf in
    let b'
        := (@VTerm.Fun Σ (c_sym_builtin_value Σ b) []) in
    let args'
        := (b'::args) in
    @exist _ _ 
        (@VTerm.Fun Σ sym args')
        (proj1 (@vterm_is_closed_Fun Σ sym args')
            (Forall_cons vterm_is_closed b' args _ pf)
        
        )
| ao_app_ao aps1 aps2 =>
    let tpf1 : { t : VTerm.term Σ | vterm_is_closed t }
        := m2c_AppliedOperator'_symbol_builtin_rev aps1 in
    let tpf2 : { t : VTerm.term Σ | vterm_is_closed t }
        := m2c_AppliedOperator'_symbol_builtin_rev aps2 in
    let sym : symbol Σ
        := closed_vterm_proj_sym tpf1 in
    let args : list (VTerm.term Σ)
        := closed_vterm_proj_args0 tpf1 in
    let pf
        := closed_vterm_proj_args0_closed tpf1 in
    @exist _ _
        (@VTerm.Fun Σ sym ((`tpf2)::args))
        (proj1 (@vterm_is_closed_Fun Σ sym ((`tpf2)::args))
            (Forall_cons vterm_is_closed (`tpf2) args _ (closed_vterm_proj_args0_closed _))
        )
end
.

Program Definition m2c_GroundTerm
    {Σ : spec_syntax.StaticModel}
    (g : GroundTerm)
    : { t : VTerm.term Σ | vterm_is_closed t }
:=
match g with
| aoo_app _ _ app => m2c_AppliedOperator'_symbol_builtin_rev app
| aoo_operand _ _ o =>
    @exist _ _ (@VTerm.Fun Σ (c_sym_builtin_value Σ o) []) _
end
.

Definition vterm_wellformed
    {Σ : spec_syntax.StaticModel}
    (t : VTerm.term Σ)
    : Prop
:= @VTerm.term_rect
    Σ
    (fun _ => Prop)
    (fun _ => Prop)
    (fun (n:nat) => True)
    (fun sym l pf => pf /\ (@is_symbol Σ sym \/ l = []))
    True
    (fun x xs => and)
    t
.


Lemma closed_vterm_proj_args0_wf
    {Σ : spec_syntax.StaticModel}
    ( ct : { t : VTerm.term Σ | vterm_is_closed t })
    :
    vterm_wellformed (`ct) ->
    Forall vterm_wellformed (closed_vterm_proj_args0 ct)
.
Proof.
    destruct ct as [t pf].
    destruct t.
    { inversion pf. }
    simpl.
    intros [H1 H2].
    unfold closed_vterm_proj_args0.
    simpl.
    clear H2.
    revert H1.
    induction l; simpl; intros H1.
    { apply Forall_nil. }
    {
        simpl in pf.
        apply Forall_cons; ltac1:(naive_solver).
    }
Qed.

Lemma vterm_wellformed_m2c_GroundTerm
    {Σ : spec_syntax.StaticModel}
    (g : AppliedOperator' spec_syntax.symbol builtin_value):
    vterm_wellformed (proj1_sig (m2c_AppliedOperator'_symbol_builtin_rev g))
.
Proof.
    induction g.
    {
        simpl.
        split>[exact I|].
        left. exact I.
    }
    {
        simpl.
        remember (m2c_AppliedOperator'_symbol_builtin_rev g) as tr.
        destruct tr as [t pf].
        repeat split.
        { right. reflexivity. }
        {
            simpl in IHg.
            destruct t; simpl in *.
            { inversion pf. }
            { apply IHg. }
        }
        {
            simpl.
            simpl in *.
            destruct t; simpl in *.
            { inversion pf. }
            {
                destruct IHg as [H1 H2].
                destruct H2 as [H2|H2].
                {
                    left. apply H2.
                }
                {
                    subst l.
                    simpl.
                    left.
                    unfold closed_vterm_proj_sym.
                    simpl.
                    unfold is_symbol.
                    destruct f,g; simpl in *; try (exact I);
                        inversion Heqtr.
                }
            }
        }
    }
    {
        simpl.
        repeat split.
        { exact IHg2. }
        {
            remember (m2c_AppliedOperator'_symbol_builtin_rev g1) as tr.
            assert (Htmp := closed_vterm_proj_args0_closed tr).
            remember (closed_vterm_proj_args0 tr) as l.
            destruct tr as [t pf].
            simpl in *.
            assert (Htmp2 := closed_vterm_proj_args0_wf (t ↾ pf)).
            simpl in Htmp2.
            specialize (Htmp2 IHg1).
            simpl in *.
            ltac1:(rewrite - Heql in Htmp2).
            clear -Htmp Htmp2.
            revert Htmp Htmp2.
            induction l; simpl; intros Htmp Htmp2.
            { exact I. }
            {
                inversion Htmp; subst; clear Htmp.
                inversion Htmp2; subst; clear Htmp2.
                split.
                { assumption. }
                { apply IHl; assumption. }
            }
        }
        {
            left.
            (* We want to prove that `closed_vterm_proj_sym` always returns a symbol*)
            destruct g1; simpl in *.
            { exact I. }
            {
                destruct IHg1 as [H1 H2].
                simpl in *.
                destruct H2 as [H2|H2].
                {
                    remember (closed_vterm_proj_sym (m2c_AppliedOperator'_symbol_builtin_rev g1)) as tr.
                    destruct tr; simpl in *.
                    {
                        exact I.
                    }
                    {
                        inversion H2.
                    }
                }
                {
                    inversion H2.
                }
            }
            {
                destruct IHg1 as [[H1 H2] H3].
                simpl in *.
                destruct H3 as [H3|H3].
                {
                    simpl in *.
                    remember (closed_vterm_proj_sym (m2c_AppliedOperator'_symbol_builtin_rev g1_1)) as tr.
                    destruct tr; simpl in *.
                    {
                        exact I.
                    }
                    {
                        inversion H3.
                    }
                }
                {
                    inversion H3.
                }
            }
        }
    }
Qed.

Lemma _helper_c2m_closed_vterm
    {Σ : spec_syntax.StaticModel}
    n l:
    vterm_is_closed (Fun n l) ->
    Forall (fun e => vterm_is_closed e) l
.
Proof.
    revert n.
    induction l; simpl; intros n H.
    { apply Forall_nil. }
    {
        apply Forall_cons.
        { ltac1:(naive_solver). }
        { ltac1:(naive_solver). }
    }
Qed.

Print fold_left.
Definition c2m_closed_vterm
    {Σ : spec_syntax.StaticModel}
    (ct : { t : VTerm.term Σ | vterm_is_closed t })
    : GroundTerm
:= @VTerm.term_rect
    Σ
    (fun t =>
        vterm_is_closed t ->
        GroundTerm
    )
    (fun (l : list (VTerm.term Σ)) =>
            Forall (fun e => vterm_is_closed e) l ->
            list (GroundTerm)
    )
    (fun n pf => match pf with end)
    (fun sym l rec pf => 
        let pf1 := _helper_c2m_closed_vterm sym l pf in
        let l1 := rec pf1 in
        match sym with
        | c_sym_symbol _ sym' =>
            aoo_app _ _ (fold_left
                (fun (y : AppliedOperator' spec_syntax.symbol builtin_value) (x : GroundTerm) =>
                    match x with
                    | aoo_app _ _ app => @ao_app_ao spec_syntax.symbol builtin_value y app
                    | aoo_operand _ _ b => @ao_app_operand spec_syntax.symbol builtin_value y b
                    end
                )
                l1
                (@ao_operator spec_syntax.symbol builtin_value sym')
                
            )
        | c_sym_builtin_value _ b => aoo_operand _ _ b
        end
    )
    (fun pf => [])

    (fun t v Pt Qv pf =>
        let x := Pt (Forall_inv pf) in
        let xs := Qv (Forall_inv_tail pf) in
        x::xs
    )
    (proj1_sig ct)
    (proj2_sig ct)
.

Definition zip_term_with_proof
    {Σ : spec_syntax.StaticModel}
    :
    forall (l : list (term Σ)),
    Forall vterm_is_closed l ->
    list ({t : term Σ | vterm_is_closed t})
.
Proof.
    intros l H.
    assert (H' := proj1 (Forall_forall vterm_is_closed l) H).
    clear H.
    revert H'.
    induction l; simpl.
    { intros H. exact []. }
    {
        intros H.
        ltac1:(ospecialize (IHl _)).
        {
            abstract(ltac1:(naive_solver)).
        }
        assert (Hclosed: vterm_is_closed a) by (abstract(ltac1:(naive_solver))).
        exact ((exist Hclosed)::IHl).
    }
Defined.

Example ex1_c2m_closed_vterm__m2c_GroundTerm
    {Σ : spec_syntax.StaticModel}
    (o : spec_syntax.symbol)
    : 
    let g := (aoo_app spec_syntax.symbol builtin_value (ao_operator o)) in
    c2m_closed_vterm (m2c_GroundTerm g) = g
.
Proof. reflexivity. Qed.

Example ex2_c2m_closed_vterm__m2c_GroundTerm
    {Σ : spec_syntax.StaticModel}
    (o : spec_syntax.symbol)
    (b : builtin_value)
    : 
    let g : GroundTerm 
        := (aoo_app _ _ (ao_app_operand (ao_operator o) b)) in
    c2m_closed_vterm (m2c_GroundTerm g) = g
.
Proof.
    reflexivity.
Qed.

(*
Lemma c2m_closed_vterm__m2c_GroundTerm
    {Σ : spec_syntax.StaticModel}
    (g : GroundTerm)
    : c2m_closed_vterm (m2c_GroundTerm g) = g
.
Proof.
    destruct g; simpl.
    {
        eapply term_ind
            with
            (Sig := m2c_sig Σ)
            (Q := (
                fun (l : list (term Σ)) =>
                    forall
                    (pf : Forall vterm_is_closed l),
                    ((@m2c_GroundTerm Σ <$> (@c2m_closed_vterm Σ <$> (zip_term_with_proof l pf))) = (zip_term_with_proof l pf))
            ))
        .
        {
            intros x. intros pf.
            simpl in pf.
            inversion pf.
        }

        remember (m2c_AppliedOperator'_symbol_builtin_rev ao) as tr.
        destruct tr as [t pf].
        apply (f_equal proj1_sig) in Heqtr.
        simpl in Heqtr.
        assert (Hwf := vterm_wellformed_m2c_GroundTerm ao).
        rewrite <- Heqtr in Hwf.
        revert pf Hwf Heqtr.
        pattern t.
        eapply term_ind
            with
            (Sig := m2c_sig Σ)
            (Q := (
                fun (l : list (term Σ)) =>
                    forall
                    (pf : Forall vterm_is_closed l),
                    ((@m2c_GroundTerm Σ <$> (@c2m_closed_vterm Σ <$> (zip_term_with_proof l pf))) = (zip_term_with_proof l pf))
            ))
        .
        {
            intros x. intros pf.
            simpl in pf.
            inversion pf.
        }
        {
            intros sym l. revert sym.
            revert ao t.

            intros ao t sym Hfmap Hclosed Hwf Hretfun.
            revert t Hfmap Hclosed Hwf.
            revert ao Hretfun.
            induction l; intros ao Hretfun t.
            {
                destruct sym,ao; cbn in *; inversion Hretfun; subst; clear Hretfun.
                reflexivity.
            }
            {
                intros IH pf Hwf.
                unfold c2m_closed_vterm.
                unfold proj1_sig.
                unfold proj2_sig.
                unfold term_rect.
                destruct sym.
                {
                    ltac1:(unshelve(ospecialize (IH _))).
                    {
                        apply vterm_is_closed_Fun in pf.
                        exact pf.
                    }
                    lazy_match! (Constr.type &IH) with
                    | (_ <$> (_ <$> (zip_term_with_proof _ ?a)) = _) => remember $a as ugly_proof
                    end.
                    erewrite (@proof_irrelevance _ ugly_proof ?[mypf0]) in IH.
                    clear Hequgly_proof.
                    unfold zip_term_with_proof in IH at 1.
                    unfold list_rect in IH at 1.
                    ltac1:(rewrite [_ <$> _]/= in IH).
                    ltac1:(rewrite [R in _ = R]/zip_term_with_proof in IH).
                    ltac1:(rewrite [list_rect _ _ _ _]/= in IH).
                    unfold zip_term_with_proof,list_rect in IH.
                    ltac1:(rewrite [R in _ = R]/= in IH).
                    inversion IH.
                    
                    (*
                    lazy_match! (Constr.type &H0) with
                    | ( (`(m2c_GroundTerm (c2n_closed_vterm (a ↾ ?pf)))) = _) => remember $pf as another_ugly_proof
                    end.
                    *)

                    specialize (IHl ao t (c_sym_symbol Σ s)).
                    ltac1:(unshelve(ospecialize (IHl _))).
                    {
                        intros pf0.
                        unfold fmap.
                        clear -H1.

                        remember ((zip_term_with_proof_subproof Σ a l
                            (proj1 (Forall_forall vterm_is_closed (a :: l)) ?mypf0))) as pf1.
                        rewrite <- Heqpf1 in H1.

                        lazy_match! (Constr.type &H1) with
                        | ( (list_fmap _ _ _ (list_fmap _ _ _ ?weird))  = _) => assert (Hweird: $weird = (zip_term_with_proof l pf0))
                        end.
                        {
                            clear.
                            induction l.
                            { reflexivity. }
                            {
                                cbn.
                                assert (Htmp: (proj1 (Forall_forall vterm_is_closed (a :: l)) pf0) = pf1).
                                {
                                    apply proof_irrelevance.
                                }
                                rewrite <- Htmp.
                                ltac1:(f_equal).
                            }
                        }
                        rewrite Hweird in H1.
                        apply H1.
                }
                ltac1:(unshelve(ospecialize (IHl _ _))).
                {
                    cbn in pf.
                    apply pf.
                }
                {
                    cbn in Hwf.
                    cbn.
                    split.
                    {
                        apply Hwf.
                    }
                    {
                        left. exact I.
                    }
                }
                specialize (IHl Heqtr).
                erewrite <- IHl.
                {
                    clear IHl.
                }
                
            }



            intros sym l IH pf Hwf Heqtr.
            apply vterm_is_closed_Fun in pf as pf'.
            specialize (IH pf').
            
            destruct sym; simpl.
            {
                destruct ao; simpl in Heqtr; inversion Heqtr.
                {
                    subst; clear Heqtr
                    cbn. reflexivity.
                }
                {
                    ltac1:(move: H0 => myH).
                    destruct l.
                    { inversion H1. }
                    revert t pf pf' Hwf IH H1 myH.
                    clear Heqtr.
                    revert ao b s.
                    induction l; intros ao b s t (*s*) pf pf' Hwf (*Heqtr*) IH H1 myH.
                    {
                        inversion H1; subst; clear H1.
                        unfold c2m_closed_vterm.
                        unfold term_rect.
                        unfold proj1_sig.
                        apply f_equal.
                        simpl.
                        destruct ao; simpl in H2; inversion H2; subst; clear H2.
                        simpl in *.
                        unfold closed_vterm_proj_sym in *.
                        cbn in myH.
                        inversion myH; subst; clear myH.


                        ltac1:(exfalso).
                    }
                    {
                        inversion H1; subst; clear H1.
                        ltac1:(unshelve(erewrite <- (IHl _ _ s t))).
                        {

                            ltac1:(naive_solver).
                        }
                        {
                            eapply Forall_inv_tail.
                            apply pf'.
                        }
                        {
                            simpl in IH.
                            inversion IH; subst; clear IH.
                            ltac1:(f_equal).
                        }
                        {
                            ltac1:(naive_solver).
                        }
                        {
                            ltac1:(naive_solver).
                        }
                        {
                            
                        }
                        {
                            
                        }
                        {

                        }

                        specialize (IHl t).





                        destruct pf as [pf1 pf2].
                        assert (pf'_backup := pf').
                        rewrite Forall_cons_iff in pf'_backup.
                        destruct Hwf as [[Hwf0 Hwf1] Hwf2].
                        clear Hwf2.
                        
                        
                        simpl in IH.
                        inversion IH; subst; clear IH.

                        unfold c2m_closed_vterm.
                        unfold term_rect.
                        unfold proj1_sig.
                        (*ltac1:(f_equal).*)
                        remember (Forall_inv_tail _) as some_proof.
                        clear Heqsome_proof.
                        remember (closed_vterm_proj_args0 (m2c_AppliedOperator'_symbol_builtin_rev ao)) as this_is_closed.
                        destruct pf'_backup as [somepf1 somepf2].
                        specialize (IHl ltac:(assumption) ltac:(assumption)).
                        ltac1:(ospecialize (IHl _)).
                        {
                            simpl.
                            split.
                            {
                                apply Hwf1.
                            }
                            {
                                left. exact I.
                            }
                        }
                        clear Hwf0.
                        rewrite <- myH in IHl.
                        rewrite <- IHl; clear IHl.
                        {
                            unfold c2m_closed_vterm.
                            unfold term_rect.
                            unfold proj1_sig.
                            ltac1:(f_equal).
                            subst.
                            remember (_helper_c2m_closed_vterm _ _ _) as another_proof_2.
                            ltac1:(cut (some_proof = another_proof_2)).
                            {
                                intros Hproofs_equal.
                                rewrite Hproofs_equal.
                                reflexivity.
                            }
                            {
                                apply proof_irrelevance.
                            }
                        }
                        {
                            unfold fmap.
                            remember (list_rect _ _ _ _) as lrect.
                            remember (lrect _) as lrect1.
                            remember ((zip_term_with_proof this_is_closed somepf2)) as something2.
                            ltac1:(cut (something2 = lrect1)).
                            {
                                intros Heq. rewrite Heq. apply H0.
                            }
                            subst something2 lrect1 lrect.
                            clear -some_proof.
                            revert pf' some_proof.
                            induction this_is_closed; simpl; intros pf' some_proof.
                            {
                                reflexivity.
                            }
                            {
                                cbn.
                                apply (f_equal2 cons).
                                {
                                    lazy_match! goal with
                                    | [ |- (@exist _ _ _ ?xa) = (@exist _ _ _ ?xb)] => (ltac1:(xa xb |- cut (xa = xb)) (Ltac1.of_constr xa) (Ltac1.of_constr xb))
                                    end.
                                    {
                                        intros Hmyeq. rewrite Hmyeq. reflexivity.
                                    }
                                    apply proof_irrelevance.
                                }
                                {
                                    
                                    inversion some_proof; subst; clear some_proof.
                                    inversion somepf2; subst.
                                    assert (HA : Forall vterm_is_closed (@Fun Σ (c_sym_builtin_value Σ b) [] :: this_is_closed)).
                                    {
                                        apply Forall_cons.
                                        {
                                            cbn. exact I.
                                        }
                                        {
                                            exact H4.
                                        }
                                    }
                                    
                                    specialize (IHthis_is_closed ltac:(assumption)).
                                    simpl in IHthis_is_closed.
                                    ltac1:(unshelve(ospecialize (IHthis_is_closed _))).
                                    {
                                        apply HA.
                                    }
                                    specialize (IHthis_is_closed H4).
                                    erewrite (@proof_irrelevance (Forall vterm_is_closed this_is_closed) H4 ?[mypf]) in IHthis_is_closed.
                                    ltac1:(f_equal).
                                    erewrite (@proof_irrelevance _ ((proj1 (Forall_forall vterm_is_closed (a :: this_is_closed))) ?[mypf2])).
                                    reflexivity.
                                    Unshelve.
                                    inversion somepf2; subst; assumption.
                                }
                            }
                        }
                        {

                        }
                    }
                    (* TODO move stuff here*)
                }
                {
                    
                }
                

                cbn.
                
            }
            {

                simpl in Hwf. simpl in pf.
                ltac1:(exfalso).
                assert (l = []) by (ltac1:(naive_solver)).
                subst l.
                clear Hwf.
                simpl in *.
                clear pf pf' IH.
                destruct ao; simpl in *; inversion Heqtr.
            }
        }




        induction ao; simpl.
        {
            reflexivity.
        }
        {
            remember (m2c_AppliedOperator'_symbol_builtin_rev ao) as tr1.
            destruct tr1 as [t1 pf1].
            unfold c2m_closed_vterm.
            simpl in *.
            simpl.
        }
    }
    {
        cbn. reflexivity.
    }
Qed.
*)
