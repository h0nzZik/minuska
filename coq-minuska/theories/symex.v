From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    unification_interface
    symex_spec
    valuation_merge
    fresher
    substitution_parallel
    substitution_parallel_properties
.


Require Import Wellfounded.
From stdpp Require Import lexico well_founded.

Require Import Program.
From Coq Require Import Logic.Eqdep_dec.

From Equations Require Export Equations.


Definition ScList {Σ : BackgroundModel} := (list (Variabl*(AttrSymbol+QuerySymbol+FunSymbol)*(list (Expression2)))).

(* To make sense, vars of F and vars of et should not overlap *)
Fixpoint replace_and_collect0
    {Σ : BackgroundModel}
    (* (F : FresherM ()) *)
    (et : (@TermOver' TermSymbol Expression2))
    :
    FresherM ((@TermOver' TermSymbol BuiltinOrVar)*ScList)
:=
    match et with
    | t_over (e_ground g) => returnFresher (((TermOverBuiltin_to_TermOverBoV g)),[])
    | t_over (e_Variabl x) => returnFresher ((t_over (bov_Variabl x)),[])
    | t_over (e_fun f l) => 
        freshFresher (fun x =>
            (t_over (bov_Variabl x),[(x,(inr f), l)])
        )
    | t_over (e_query q l) => 
        freshFresher (fun x =>
            (t_over (bov_Variabl x),[(x,(inl (inr q)), l)])
        )
    | t_over (e_attr a l) => 
        freshFresher (fun x =>
            (t_over (bov_Variabl x),[(x,(inl (inl a)), l)])
        )
    | t_term s l => 
        let a := (fix go (l : (list (@TermOver' TermSymbol Expression2))) : FresherM ((list (@TermOver' TermSymbol BuiltinOrVar))*ScList) :=
            match l with
            | nil => returnFresher (nil,nil)
            | x::xs => bindFresher (replace_and_collect0 x) (
                fun yr => bindFresher (go xs) (
                    fun ysr => 
                        let y := yr.1 in
                        let r1 := yr.2 in
                        let ys := ysr.1 in
                        let r2 := ysr.2 in
                        returnFresher ((y::ys), r1 ++ r2)
                )
            )
            end
        ) l in
        (bindFresher a (fun b => returnFresher (t_term s b.1, b.2)))
    end
.

Definition replace_and_collect1
    {Σ : BackgroundModel}
    (avoid : list Variabl)
    (et : (@TermOver' TermSymbol Expression2))
    :
    ((@TermOver' TermSymbol BuiltinOrVar)*ScList)
:=
    (replace_and_collect0 et {|fresher_avoid := (elements (vars_of et) ++ avoid)|}).1
.


Definition replace_and_collect
    {Σ : BackgroundModel}
    (et : (@TermOver' TermSymbol Expression2))
    :
    ((@TermOver' TermSymbol BuiltinOrVar)*ScList)
:=
    replace_and_collect1 [] et
.

Inductive SideConditionEq {Σ : BackgroundModel} :=
| sce_true
| sce_false
| sce_eq (l r : Expression2)
| sce_atom (pred : PredSymbol) (args : list Expression2)
| sce_natom (pred : PredSymbol) (args : list Expression2)
| sce_hatom (pred : HPredSymbol) (args : list Expression2)
| sce_and (left : SideConditionEq) (right : SideConditionEq)
| sce_or (left : SideConditionEq) (right : SideConditionEq)
.

Fixpoint asIfWithEq {Σ : BackgroundModel} (sc : SideCondition) : SideConditionEq :=
    match sc with
    | sc_true => sce_true
    | sc_false => sce_false
    | sc_pred p a => sce_atom p a
    | sc_npred p a => sce_natom p a
    | sc_hpred p a => sce_hatom p a
    | sc_and l r => sce_and (asIfWithEq l) (asIfWithEq r)
    | sc_or l r => sce_or (asIfWithEq l) (asIfWithEq r)
    end
.

Fixpoint vars_of_sce {Σ : BackgroundModel} (sc : SideConditionEq) : gset Variabl :=
match sc with
| sce_true => ∅
| sce_false => ∅
| sce_atom _ args => vars_of args
| sce_natom _ args => vars_of args
| sce_hatom _ args => vars_of args
| sce_eq l r => vars_of l ∪ vars_of r
| sce_and l r => vars_of_sce l ∪ vars_of_sce r
| sce_or l r => vars_of_sce l ∪ vars_of_sce r
end
.

#[export]
Instance  VarsOf_sce
    {Σ : BackgroundModel}
    : VarsOf SideConditionEq Variabl
:= {|
    vars_of := vars_of_sce ;
|}.

Definition SideConditionEq_evaluate
    {Σ : BackgroundModel}
    (program : ProgramT)
    (h : HiddenValue)
    (ρ : Valuation2)
    (nv : NondetValue)
    (sc : SideConditionEq)
    : option bool
:=
    (
        fix go (sc : SideConditionEq) : option bool :=
        match sc with
        | sce_true => Some true
        | sce_false => Some false
        | sce_atom pred args => (
            let ts' := (fun e => Expression2_evaluate program h ρ e nv) <$> args in
            ts ← list_collect ts';
            builtin_predicate_interp pred nv ts
        )
        | sce_natom pred args => (
            let ts' := (fun e => Expression2_evaluate program h ρ e nv) <$> args in
            ts ← list_collect ts';
            negb <$> builtin_predicate_interp pred nv ts
        )
        | sce_hatom pred args => (
            let ts' := (fun e => Expression2_evaluate program h ρ e nv) <$> args in
            ts ← list_collect ts';
            hidden_predicate_interpretation pred h ts
        )
        | sce_eq l r =>
            gl ← Expression2_evaluate program h ρ l nv;
            gr ← Expression2_evaluate program h ρ r nv;
            Some (bool_decide (gl = gr))
        | sce_and l r => 
            l' ← (go l);
            r' ← (go r);
            Some (andb l' r')
        | sce_or l r => 
            l' ← (go l);
            r' ← (go r);
            Some (orb l' r')
        end
    ) sc
.

Lemma SideConditionEq_evaluate_asIfWithEq
    {Σ : BackgroundModel}
    (sc : SideCondition)
    (program : ProgramT)
    (h : HiddenValue)
    (nv : NondetValue)
    (ρ : Valuation2)
    :
    SideConditionEq_evaluate program h ρ nv (asIfWithEq sc)
    = SideCondition_evaluate program h ρ nv sc
.
Proof.
    induction sc; simpl.
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    {
        rewrite IHsc1.
        rewrite IHsc2.
        reflexivity.
    }
    {
        rewrite IHsc1.
        rewrite IHsc2.
        reflexivity.
    }
Qed.

Record SimpleSymbolicState
    {Σ : BackgroundModel}
 := {
    sss_term : @TermOver' TermSymbol BuiltinOrVar ;
    sss_sc : SideConditionEq ;
    (* In general, we try to ensure that vars_of sss_sc ⊆ vars_of sss_term,
        but we do not want to encode as a proof object because of performance reasons
     *)
}.

Definition SymbolicState {Σ : BackgroundModel } := list SimpleSymbolicState.


Definition denot_sss
    {Σ : BackgroundModel}
    (sss : SimpleSymbolicState)
    (g : @TermOver' TermSymbol BasicValue)
    : Type
:=
    { ρ : Valuation2 & sat2B ρ g sss.(sss_term) }
.

(* Search sigT. *)

Definition denot_ss
    {Σ : BackgroundModel}
    (ss : SymbolicState)
    (g : @TermOver' TermSymbol BasicValue)
    : Type
:=
    { sss : SimpleSymbolicState & ((sss ∈ ss) * (((denot_sss sss g))))%type }

.

Definition FalseState {Σ : BackgroundModel} : SymbolicState := [].

Fixpoint sclist_to_sceq {Σ : BackgroundModel} (l : ScList) : SideConditionEq :=
    match l with
    | [] => sce_true
    | xfl::xs =>
        let part_1 := sce_eq (e_Variabl xfl.1.1) (
        match xfl.1.2 with
        | inl (inl a) => e_attr a xfl.2
        | inl (inr q) => e_query q xfl.2
        | inr f => e_fun f xfl.2
        end) in
        let part_2 := sclist_to_sceq xs in
        sce_and part_1 part_2
    end
.

Definition simpleStepByRule
    {Σ : BackgroundModel}
    (UA : UnificationAlgorithm)
    (sss : SimpleSymbolicState)
    (Label : Set)
    (r : RewritingRule2 Label)
    : SymbolicState
:=
    let osub := UA.(ua_unify) sss.(sss_term) r.(r_from) in
    match osub with
    | None => FalseState
    | Some sub =>
        let to'' := replace_and_collect1 (elements ((vars_of sub) ∪ vars_of (sss.(sss_sc)))) r.(r_to) in
        let sceq := sclist_to_sceq to''.2 in
        let to' := to''.1 in
        let to := subp_app sub to' in
        [{|sss_term := to; sss_sc := sceq|}]
    end
.


Module Implementation.

End Implementation.

