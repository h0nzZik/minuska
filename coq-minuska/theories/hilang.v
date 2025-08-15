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

Fixpoint extend_term
    (Σ : BackgroundModel)
    (t : @TermOver' TermSymbol BasicValue)
    :
    @TermOver' (@ExtendedSymbols TermSymbol) BasicValue
:=
    match t with
    | t_over bv => t_over bv
    | t_term s args => @t_term (@ExtendedSymbols TermSymbol) BasicValue (sym_original s) (extend_term Σ <$> args)
    end
.

Fixpoint contract_term
    (Σ : BackgroundModel)
    (t : @TermOver' (@ExtendedSymbols TermSymbol) BasicValue)
:
    option (@TermOver' TermSymbol BasicValue)
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
    (Σ : BackgroundModel)
    (t : @TermOver' TermSymbol BasicValue)
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

Definition ExtendedBM (Σ : BackgroundModel) : BackgroundModel :=
let bt := {|
        TermSymbol := @ExtendedSymbols (Σ.(basic_types).(TermSymbol)) ;
        NondetValue := Σ.(basic_types).(NondetValue) ;
        Variabl := Σ.(basic_types).(Variabl) ;
        FunSymbol := Σ.(basic_types).(FunSymbol) ;
        PredSymbol := Σ.(basic_types).(PredSymbol) ;
        HiddenValue := Σ.(basic_types).(HiddenValue) ;
        QuerySymbol := Σ.(basic_types).(QuerySymbol) ;
        ProgramT := Σ.(basic_types).(ProgramT) ;
    |}
in
{|
    basic_types := bt;
    basic_types_properties := Build_BasicTypesProperties
        bt
        (Σ.(basic_types_properties).(Variabl_edc))
        ({|
            edc_eqdec := ExtendedSymbols_eqdec _ ;
            edc_count := ExtendedSymbols_countable _ ;
        |})
        (Σ.(basic_types_properties).(FunSymbol_edc))
        (Σ.(basic_types_properties).(PredSymbol_edc))
        (Σ.(basic_types_properties).(HPredSymbol_edc))
        (Σ.(basic_types_properties).(AttrSymbol_edc))
        (Σ.(basic_types_properties).(MethSymbol_edc))
        (Σ.(basic_types_properties).(QuerySymbol_edc))
        (Σ.(basic_types_properties).(BasicValue_edc))
        (Σ.(basic_types_properties).(HiddenValue_edc))
        (Σ.(basic_types_properties).(NondetValue_edc))
        (Σ.(basic_types_properties).(Variable_inf))
        ;
    background_model_over := {|
        program_info := {|
            pi_TermSymbol_interp := fun program q args =>
                args'' ← list_collect (contract_term Σ <$> args);
                r ← Σ.(background_model_over).(program_info).(pi_TermSymbol_interp) program q args'';
                (* None *)
                Some (extend_term Σ r)
                ;
        |} ;
        value_algebra := {|
            builtin_function_interp := fun f nd args =>
                let args' : (option (list (@TermOver' TermSymbol BasicValue))) := list_collect (contract_term Σ <$> args) in
                args'' ← args';
                r ← Σ.(background_model_over).(value_algebra).(builtin_function_interp) f nd args'';
                Some (extend_term Σ r)
            ;
            builtin_predicate_interp := fun p nd args =>
            args' ← list_collect (contract_term Σ <$> args);
                Σ.(background_model_over).(value_algebra).(builtin_predicate_interp) p nd args'
            ;
        |};
        hidden_algebra := {|
            
            attribute_interpretation := fun a h args =>
                args'' ← list_collect (contract_term Σ <$> args);
                r ← Σ.(background_model_over).(hidden_algebra).(attribute_interpretation) a h args'';
                Some (r)
            ;
            method_interpretation := fun m h args =>
                args'' ← list_collect (contract_term Σ <$> args);
                r ← Σ.(background_model_over).(hidden_algebra).(method_interpretation) m h args'';
                Some (r)
            ;
            hidden_predicate_interpretation := fun p h args =>
                args'' ← list_collect (contract_term Σ <$> args);
                r ← Σ.(background_model_over).(hidden_algebra).(hidden_predicate_interpretation) p h args'';
                Some (r)
            ;
            hidden_init := Σ.(background_model_over).(hidden_algebra).(hidden_init) ;
        |};
        nondet_gen := Σ.(background_model_over).(nondet_gen) ;
    |};
|}.


Inductive Context_ {Σ : BackgroundModel} :=
| ctx_hole
| ctx_term (s : TermSymbol)
           (l : list (@TermOver' TermSymbol BuiltinOrVar)) 
           (m : Context_)
           (r : list (@TermOver' TermSymbol BuiltinOrVar))
.

Fixpoint ctx_subst
    {Σ : BackgroundModel}
    (c : Context_)
    (p : @TermOver' TermSymbol BuiltinOrVar)
    :
    @TermOver' TermSymbol BuiltinOrVar
:=
    match c with
    | ctx_hole => p
    | ctx_term s l m r => t_term s (l++(ctx_subst m p)::r)
    end
.

Inductive collapses_to
    (Σ : BackgroundModel)
    :
    (@TermOver' (ExtendedBM Σ).(basic_types).(TermSymbol) BasicValue) ->
    (@TermOver' Σ.(basic_types).(TermSymbol) BasicValue) ->
    Type
:=
| cto_base:
    forall x,
        collapses_to Σ
            (t_term (sym_cseq) [
                (extend_term _ x); 
                (t_term sym_emptyCseq [])])
            x
| ctx_seq:
    forall x x' s n l,
    collapses_to Σ x' x ->
    collapses_to Σ
        (t_term (sym_cseq) [
            x';
            (t_term (sym_heatedAt s n) (extend_term _ <$>l))
        ])
        (t_term s (take n l ++ x::(drop n l)))        
.

(* 
    heating preserves [collapses_to]:
    ∀ x y d d'
    collapses_to Σ x y ->
    (t_term sym_top [x;d]) ~>_(heat) (t_term sym_top [x';d']) ->
    collapses_to Σ x' y.

    The same with cooling.
 *)



