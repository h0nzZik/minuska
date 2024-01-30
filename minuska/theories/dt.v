From Minuska Require Import
    prelude
.

Class Signature := {
    Constructor : Type ;
    Constructor_eqdec :: EqDecision Constructor ;
    arity : Constructor -> nat;
}.

Unset Elimination Schemes.
Inductive Pattern {Σ : Signature} : Type :=
| p_wildcard
| p_cpat (c : Constructor) (l : list Pattern)
.
Inductive Value {Σ : Signature} : Type :=
| v_cval (c : Constructor) (l : list Value)
.
Set Elimination Schemes.

Section custom_induction_principle.

    Context
        {Σ : Signature}
        (P : Pattern -> Prop)
        (true_for_wildcard : P p_wildcard)
        (preserved_by_cpat :
            forall
                (c : Constructor)
                (l : list Pattern),
                Forall P l ->
                P (p_cpat c l)
        )
    .

    Fixpoint Pattern_ind (p : Pattern) : P p :=
    match p with
    | p_wildcard => true_for_wildcard
    | p_cpat c l => preserved_by_cpat c l (Forall_true P l Pattern_ind)
    end.

End custom_induction_principle.

Section custom_induction_principle.

    Context
        {Σ : Signature}
        (P : Value -> Prop)
        (preserved_by_cval :
            forall
                (c : Constructor)
                (l : list Value),
                Forall P l ->
                P (v_cval c l)
        )
    .

    Fixpoint Value_ind (v : Value) : P v :=
    match v with
    | v_cval c l => preserved_by_cval c l (Forall_true P l Value_ind)
    end.

End custom_induction_principle.

Definition PatternVector {Σ : Signature} : Type :=
    list Pattern
.

Definition PatternMatrice {Σ : Signature} : Type :=
    list PatternVector
.

Definition ClauseMatrix {Σ : Signature} (A : Type) : Type :=
    list (PatternVector*A)
.

Definition ValueVector {Σ : Signature} : Type :=
    list Value
.

Inductive pvmatch {Σ : Signature} : Pattern -> Value -> Prop :=
| pvm_wildcard: forall v, pvmatch p_wildcard v
| pvm_ctor: forall c ps vs,
    (
        forall i p v, ps !! i = Some p -> vs !! i = Some v ->
        pvmatch p v
    ) ->
    pvmatch (p_cpat c ps) (v_cval c vs)
.

Definition pvvecmatch {Σ : Signature} : PatternVector -> ValueVector -> Prop :=
    fun ps vs => (
        forall i p v, ps !! i = Some p -> vs !! i = Some v ->
        pvmatch p v
    )
.

Inductive notinstance {Σ : Signature} : Pattern -> Value -> Prop :=
| ni_ctor_diferent: forall c c' ps vs, c <> c' -> notinstance (p_cpat c ps) (v_cval c' vs)
| ni_list_different : forall c c' ps vs,
    (exists i p v, ps !! i = Some p -> vs !! i = Some v -> notinstance p v) ->
    notinstance (p_cpat c ps) (v_cval c' vs)
.

Definition cmmatch {Σ : Signature} {A : Type}
    : ValueVector -> ClauseMatrix A -> A -> Prop
:=
    fun vs cm a =>
    ∃ (j : nat) (pv : PatternVector), cm !! j = Some (pv,a)
.
Search (∀ (A : Type), nat -> A -> list A).
About replicate.
Definition Simplify_step {Σ : Signature} {A : Type}
    (c : Constructor) (row : (PatternVector * A))
: list ((PatternVector * A))
:=
match head row.1 with
| None => []
| Some v1 =>
    match v1 with
    | p_wildcard => [((replicate (arity c) (p_wildcard)) ++ (tail row.1), row.2)]
    | p_cpat c' qs =>
        if (decide (c' = c)) then [((qs ++ tail row.1), row.2)] else []
    end
end.