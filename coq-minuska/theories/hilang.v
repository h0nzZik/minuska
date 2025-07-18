From Minuska Require Import
    prelude
    spec
.

Inductive ExtendedSymbols
    {sym : Type}
:=
| sym_original (s : sym)
| sym_cseq
| sym_emptyCseq
| sym_top
| sym_hole
| sym_heatedAt (s : sym) (pos : nat)
.

#[local]
Instance ExtendedSymbols_eqdec
    (sym : Type)
    {_E : EqDecision sym}
:
    EqDecision (@ExtendedSymbols sym)
.
Proof.
    ltac1:(solve_decision).
Defined.


#[local]
Instance ExtendedSymbols_countable
    (sym : Type)
    {_E : EqDecision sym}
    {_C : Countable sym}
:
    Countable (@ExtendedSymbols sym)
.
Proof.
    apply inj_countable with (
        f := fun es => match es return (sym+(()+(()+(()+(()+(sym*nat)))))) with
        | sym_original s => inl s
        | sym_cseq => inr (inl tt)
        | sym_emptyCseq => inr (inr (inl tt))
        | sym_top => inr (inr (inr (inl tt)))
        | sym_hole => inr (inr (inr (inr (inl tt))))
        | sym_heatedAt s pos => inr (inr (inr (inr (inr (s,pos)))))
        end
    )(
        g := fun (w : (sym+(()+(()+(()+(()+(sym*nat))))))) =>
        match w return option (@ExtendedSymbols sym) with
        | inl s => Some (sym_original s)
        | inr (inl tt) => Some (sym_cseq)
        | inr (inr (inl tt)) => Some (sym_emptyCseq)
        | inr (inr (inr (inl tt))) => Some (sym_top)
        | inr (inr (inr (inr (inl tt)))) => Some (sym_hole)
        | inr (inr (inr (inr (inr (s,pos))))) => Some (sym_heatedAt s pos)
        end
    ).
    abstract(intros x; cases (); ltac1:(simplify_eq/=); reflexivity).
Defined.

#[local]
Instance ExtendedSymbols_Symbols
    (symbol : Type)
    {_Sym : Symbols symbol}
:
    Symbols (@ExtendedSymbols symbol)
:= {|
    symbol_eqdec := _ ;
    symbol_countable := _ ;
|}.

Fixpoint extend_term
    (Σ : StaticModel)
    (t : @TermOver Σ builtin_value)
    :
    @TermOver' (@ExtendedSymbols symbol) builtin_value
:=
    match t with
    | t_over bv => t_over bv
    | t_term s args => @t_term (@ExtendedSymbols symbol) builtin_value (sym_original s) (extend_term Σ <$> args)
    end
.

Fixpoint contract_term
    (Σ : StaticModel)
    (t : @TermOver' (@ExtendedSymbols symbol) builtin_value)
:
    option (@TermOver Σ builtin_value)
:=
    match t with
    | t_over bv => Some (t_over bv)
    | t_term (sym_original s) args => 
        args' ← list_collect (contract_term Σ <$> args);
        Some (t_term s args')
    | t_term _ _ => None
    end
.

Lemma contract_extend_term
    (Σ : StaticModel)
    (t : @TermOver Σ builtin_value)
    :
    contract_term Σ (extend_term Σ t) = Some t
.
Proof.
    induction t.
    { reflexivity. }
    {
        simpl.
        rewrite bind_Some.
        exists l.
        split>[|reflexivity].
        revert H.
        induction l; intros H.
        {
            reflexivity.
        }
        {
            rewrite Forall_cons in H.
            destruct H as [H1 H2].
            specialize (IHl H2).
            clear H2.
            simpl.
            rewrite H1.
            simpl.
            rewrite bind_Some.
            exists l.
            split>[|reflexivity].
            apply IHl.
        }
    }
Qed.

Program Definition ExtendedModel (Σ : StaticModel)
: @Model (@ExtendedSymbols (Σ.(symbol))) _ (Σ.(signature)) (Σ.(NondetValue))
:= {|
    builtin_value := Σ.(builtin).(builtin_value) ;
    builtin_model_over := {|
        builtin_function_interp := fun f nd args =>
            let args' : (option (list (@TermOver Σ builtin_value))) := list_collect (contract_term Σ <$> args) in
            args'' ← args';
            r ← Σ.(builtin).(builtin_model_over).(builtin_function_interp) f nd args'';
            Some (extend_term Σ r)
        ;
        builtin_predicate_interp := fun p nd args =>
        args' ← list_collect (contract_term Σ <$> args);
            Σ.(builtin).(builtin_model_over).(builtin_predicate_interp) p nd args'
        ;
        (* Looking forward to get rid of this *)
        bps_neg_correct := _;
    |};
|}.
Next Obligation.
    rewrite bind_Some in H1.
    destruct H1 as [l' [H3 H4]].
    rewrite bind_Some in H2.
    destruct H2 as [l'' [H5 H6]].
    assert (Htmp := @bps_neg_correct (Σ.(symbol)) _ _ (Σ.(NondetValue)) (Σ.(builtin).(builtin_value))).
    specialize (Htmp (Σ.(builtin).(builtin_model_over)) p p' nv l' b b' H).
    ltac1:(ospecialize (Htmp _)).
    {
        apply length_list_collect_Some in H3.
        rewrite length_fmap in H3.
        ltac1:(lia).
    }
    specialize (Htmp H4).
    assert (l' = l'').
    {
        ltac1:(simplify_eq/=).
        reflexivity.
    }
    subst l''.
    specialize (Htmp H6).
    exact Htmp.
Qed.
Fail Next Obligation.

Definition ExtendedSM (Σ : StaticModel) : StaticModel := {|
    symbol := @ExtendedSymbols (Σ.(symbol)) ;
    symbols := ExtendedSymbols_Symbols (Σ.(symbol)) ;
    NondetValue := Σ.(NondetValue) ;
    signature := Σ.(signature) ;
    builtin := ExtendedModel Σ ;
    program_info := {|
        QuerySymbol := Σ.(program_info).(QuerySymbol) ;
        ProgramT := Σ.(program_info).(ProgramT) ;
        pi_symbol_interp := fun program q args =>
            args'' ← list_collect (contract_term Σ <$> args);
            r ← Σ.(program_info).(pi_symbol_interp) program q args'';
            (* None *)
            Some (extend_term Σ r)
            ;
    |} ;
    nondet_gen := Σ.(nondet_gen) ;
|}.

(* This should depend on a collection of contexts *)
Inductive collapses_to
    (Σ : StaticModel)
    :
    (@TermOver (ExtendedSM Σ) builtin_value) ->
    (@TermOver Σ builtin_value) ->
    Type
:=
| cto_base:
    forall x,
        collapses_to Σ
            (t_term (sym_cseq) [
                (extend_term _ x); 
                (t_term sym_emptyCseq [])])
            x
.





