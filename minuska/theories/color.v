From Minuska Require Import
    prelude
    spec_syntax
.

From CoLoR Require Import
    Term.Varyadic.VSignature
    Term.Varyadic.VTerm
.

Inductive m2c_sig_symbols (Σ : spec_syntax.Signature) : Type :=
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
    (Σ : spec_syntax.Signature)
    : EqDecision (m2c_sig_symbols Σ)
.
Proof.
    ltac1:(solve_decision).
Qed.

Definition is_symbol
    {Σ : spec_syntax.Signature}
    (s : m2c_sig_symbols Σ)
    : Prop
:=
match s with
| c_sym_symbol _ _ => True
| c_sym_builtin_value _ _ => False
end
.

Definition beq_m2c_sig_symbols
    (Σ : spec_syntax.Signature)
    (a b : m2c_sig_symbols Σ)
    : bool
:= bool_decide (a = b).

Lemma beq_m2c_sig_symbols_ok
    (Σ : spec_syntax.Signature)
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
    (Σ : spec_syntax.Signature)
    : VSignature.Signature
:=
    @VSignature.mkSignature
        (m2c_sig_symbols Σ)
        (beq_m2c_sig_symbols Σ)
        (beq_m2c_sig_symbols_ok Σ)
.

Coercion m2c_sig : spec_syntax.Signature >-> VSignature.Signature.

Print VTerm.term.

Definition vterm_is_closed
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
    s
    (l: list (term Σ)) :
    Forall vterm_is_closed l ->
    @vterm_is_closed Σ (@VTerm.Fun Σ s l)
.
Proof.
    intros H.
    induction l; cbn.
    { exact I. }
    {
        inversion H; subst; clear H.
        ltac1:(naive_solver).
    }
Qed.

Program Fixpoint m2c_AppliedOperator'_symbol_builtin_rev
    {Σ : spec_syntax.Signature}
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
        (@vterm_is_closed_Fun Σ sym args'
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
        (@vterm_is_closed_Fun Σ sym ((`tpf2)::args)
            (Forall_cons vterm_is_closed (`tpf2) args _ (closed_vterm_proj_args0_closed _))
        )
end
.

Program Definition m2c_GroundTerm
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
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
    {Σ : spec_syntax.Signature}
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

Definition c2m_closed_vterm
    {Σ : spec_syntax.Signature}
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
            aoo_app _ _ (fold_right
                (fun (x : GroundTerm) (y : AppliedOperator' spec_syntax.symbol builtin_value) =>
                    match x with
                    | aoo_app _ _ app => @ao_app_ao spec_syntax.symbol builtin_value y app
                    | aoo_operand _ _ b => @ao_app_operand spec_syntax.symbol builtin_value y b
                    end
                )
                (@ao_operator spec_syntax.symbol builtin_value sym')
                l1
            )
        | c_sym_builtin_value _ b => aoo_operand _ _ b
        end
    )
    (fun pf => [])
    (fun t v Pt Qv pf => Qv (Forall_inv_tail pf))
    (proj1_sig ct)
    (proj2_sig ct)
.
