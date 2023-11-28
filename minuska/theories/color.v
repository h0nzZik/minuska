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

Program Fixpoint m2c_AppliedOperator'_symbol_builtin
    {Σ : spec_syntax.Signature}
    (g : AppliedOperator' spec_syntax.symbol builtin_value)
    : { t : VTerm.term Σ | vterm_is_closed t }
:=
match g with
| ao_operator s => @exist _ _ (@VTerm.Fun Σ (c_sym_symbol Σ s) []) _
| ao_app_operand aps b =>
    let tpf : { t : VTerm.term Σ | vterm_is_closed t }
        := m2c_AppliedOperator'_symbol_builtin aps in
    let sym : symbol Σ
        := closed_vterm_proj_sym tpf in
    let args : list (VTerm.term Σ)
        := closed_vterm_proj_args0 tpf in
    let pf
        := closed_vterm_proj_args0_closed tpf in
    let b'
        := (@VTerm.Fun Σ (c_sym_builtin_value Σ b) []) in
    let args'
        := (args ++ [b']) in
    @exist _ _ 
        (@VTerm.Fun Σ sym args')
        (@vterm_is_closed_Fun Σ sym args'
            (Forall_app_2 vterm_is_closed args [b'] pf
                (Forall_cons vterm_is_closed b' [] _ (Forall_nil vterm_is_closed))
            )
        )
| ao_app_ao aps1 aps2 =>
    let tpf1 : { t : VTerm.term Σ | vterm_is_closed t }
        := m2c_AppliedOperator'_symbol_builtin aps1 in
    let tpf2 : { t : VTerm.term Σ | vterm_is_closed t }
        := m2c_AppliedOperator'_symbol_builtin aps2 in
    let sym : symbol Σ
        := closed_vterm_proj_sym tpf1 in
    let args : list (VTerm.term Σ)
        := closed_vterm_proj_args0 tpf1 in
    let pf
        := closed_vterm_proj_args0_closed tpf1 in
    @exist _ _
        (@VTerm.Fun Σ sym (args ++ [`tpf2]))
        (@vterm_is_closed_Fun Σ sym (args ++ [`tpf2])
            (Forall_app_2 vterm_is_closed args [`tpf2]
                (closed_vterm_proj_args0_closed _)
                _
            )
        )
end
.

Program Definition m2c_GroundTerm
    {Σ : spec_syntax.Signature}
    (g : GroundTerm)
    : { t : VTerm.term Σ | vterm_is_closed t }
:=
match g with
| aoo_app _ _ app => m2c_AppliedOperator'_symbol_builtin app
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
    (fun sym l pf => pf /\ @is_symbol Σ sym)
    True
    (fun x xs => and)
    t
.

Definition get_symbol
    {Σ : spec_syntax.Signature}
    s args
    (wf : vterm_wellformed (Fun s args))
    : spec_syntax.symbol
.
Proof.
    destruct s.
    {
        exact s.
    }
    {
        cbn in wf.
        destruct wf as [_ HFalse].
        destruct HFalse.
    }
Defined.

Lemma _helper_c2m_closed_vterm
    {Σ : spec_syntax.Signature}
    n l:
    vterm_is_closed (Fun n l) ∧ vterm_wellformed (Fun n l) ->
    Forall (fun e => vterm_is_closed e /\ vterm_wellformed e) l
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
    (ct : { t : VTerm.term Σ | vterm_is_closed t /\ vterm_wellformed t })
    : AppliedOperator' spec_syntax.symbol builtin_value
:= @VTerm.term_rect
    Σ
    (fun t =>
        vterm_is_closed t /\ vterm_wellformed t ->
        AppliedOperator' spec_syntax.symbol builtin_value
    )
    (fun (l : list (VTerm.term Σ)) =>
            Forall (fun e => vterm_is_closed e /\ vterm_wellformed e) l ->
            list (AppliedOperator' spec_syntax.symbol builtin_value)
    )
    (fun n pf => match (proj1 pf) with end)
    (fun sym l rec pf => 
        let pf1 := _helper_c2m_closed_vterm sym l pf in
        let l1 := rec pf1 in
        fold_right
            (fun x => @ao_app_ao spec_syntax.symbol builtin_value x)
            (@ao_operator spec_syntax.symbol builtin_value (get_symbol sym l (proj2 pf)))
            l1
    )
    (fun pf => [])
    (fun t v Pt Qv pf => Qv (Forall_inv_tail pf))
    (proj1_sig ct)
    (proj2_sig ct)
.
