From Minuska Require Import
    prelude
.

Class TermSignature := {
    ts_variable : Set ;
    ts_nulary_symbol : Set ;
    ts_unary_symbol : Set ;
    ts_binary_symbol : Set ;

    ts_variable_eqdec ::
        EqDecision ts_variable ;

    ts_nulary_symbol_eqdec ::
        EqDecision ts_nulary_symbol ;

    ts_unary_symbol_eqdec ::
        EqDecision ts_unary_symbol ;

    ts_binary_symbol_eqdec ::
        EqDecision ts_binary_symbol ;
    
    ts_variable_countable ::
        Countable ts_variable ;
    
    ts_nulary_symbol_countable ::
        Countable ts_nulary_symbol ;

    ts_binary_symbol_countable ::
        Countable ts_unary_symbol ;

    ts_unary_symbol_countable ::
        Countable ts_binary_symbol ;
}.

Inductive Term {Σ : TermSignature} :=
| t_var (x : ts_variable)
| t_app_nulary (s : ts_nulary_symbol)
| t_app_unary (s : ts_unary_symbol) (t' : Term)
| t_app_binary (s : ts_binary_symbol) (t1 t2 : Term)
.

Definition Substitution {Σ : TermSignature} :=
    gmap ts_variable Term
.

Inductive TermAbstraction {Σ : TermSignature} :=
| ta_var
| ta_app_nulary (s : ts_nulary_symbol)
| ta_app_unary (s : ts_unary_symbol) (t' : option ts_variable)
| ta_app_binary (s : ts_binary_symbol) (t1 t2 : option ts_variable)
.

#[global]
Instance TermAbstraction_eqdec {Σ : TermSignature}
    : EqDecision TermAbstraction
.
Proof.
    ltac1:(solve_decision).
Defined.

Definition TermAbstraction_encode {Σ : TermSignature}
    (ta : TermAbstraction)
    : (()+(ts_nulary_symbol)+(ts_unary_symbol*(option ts_variable))+(ts_binary_symbol*((option ts_variable)*(option ts_variable))))%type
.
Proof.
    destruct ta.
    { left. left. left. constructor. }
    { left. left. right. exact s. }
    { left. right. exact (s, t'). }
    { right. exact (s, (t1, t2)). }
Defined.

Definition TermAbstraction_decode {Σ : TermSignature}
    (v : (()+(ts_nulary_symbol)+(ts_unary_symbol*(option ts_variable))+(ts_binary_symbol*((option ts_variable)*(option ts_variable))))%type)
    : option TermAbstraction
.
Proof.
    left.
    destruct v.
    {
        destruct s; cbn.
        {
            destruct s; cbn.
            {
                apply ta_var.
            }
            {
                apply ta_app_nulary. exact t.
            }
        }
        {
            apply ta_app_unary.
            { exact p.1. }
            { exact p.2. }
        }
    }
    {
        apply ta_app_binary.
        { apply p.1. }
        { apply p.2.1. }
        { apply p.2.2. }
    }
Defined.

#[global]
Instance TermAbstraction_countable {Σ : TermSignature}
    : Countable TermAbstraction
.
Proof.
    apply inj_countable
        with
            (f := @TermAbstraction_encode Σ)
            (g := @TermAbstraction_decode Σ)
        .
    intros x.
    destruct x; cbn; reflexivity.
Defined.

Definition get_variable {Σ : TermSignature}
    (t : Term) : option ts_variable :=
match t with
| t_var x => Some x
| _ => None
end.

Definition abstract {Σ : TermSignature}
    (t : Term) : TermAbstraction :=
match t with
| t_var _ => ta_var
| t_app_nulary s => ta_app_nulary s
| t_app_unary s t' => ta_app_unary s (get_variable t')
| t_app_binary s t1 t2 => ta_app_binary s (get_variable t1) (get_variable t2)
end.

Record SubstAction {Σ : TermSignature} := {
    sa_nonempty : unit ;
}.

Inductive Maton {Σ : TermSignature} :=
| m_nil
| m_cont
    (xs: list
        (TermAbstraction*(SubstAction*Maton))%type)
.

Fixpoint traverse {Σ : TermSignature}
    (m : Maton)
    (t : Term)
    (ls : list Substitution)
    : list Substitution :=
match m with
| m_nil => ls
| m_cont f =>
    let ta := abstract t in
    
end.