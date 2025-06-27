From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    minusl_syntax
    unification_interface
    symex_spec
    valuation_merge
    fresher
.


Require Import Wellfounded.
From stdpp Require Import lexico well_founded.

Require Import Program.
From Coq Require Import Logic.Eqdep_dec.

From Equations Require Export Equations.


Definition ScList {Σ : StaticModel} := (list (variable*(QuerySymbol+builtin_function_symbol)*(list (Expression2)))).

(* To make sense, vars of F and vars of et should not overlap *)
Fixpoint replace_and_collect0
    {Σ : StaticModel}
    (* (F : FresherM ()) *)
    (et : (TermOver Expression2))
    :
    FresherM ((TermOver BuiltinOrVar)*ScList)
:=
    match et with
    | t_over (e_ground g) => returnFresher (((TermOverBuiltin_to_TermOverBoV g)),[])
    | t_over (e_variable x) => returnFresher ((t_over (bov_variable x)),[])
    | t_over (e_fun f l) => 
        freshFresher (fun x =>
            (t_over (bov_variable x),[(x,(inr f), l)])
        )
    | t_over (e_query q l) => 
        freshFresher (fun x =>
            (t_over (bov_variable x),[(x,(inl q), l)])
        )
    | t_term s l => 
        let a := (fix go (l : (list (TermOver Expression2))) : FresherM ((list (TermOver BuiltinOrVar))*ScList) :=
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
    {Σ : StaticModel}
    (avoid : list variable)
    (et : (TermOver Expression2))
    :
    ((TermOver BuiltinOrVar)*ScList)
:=
    (replace_and_collect0 et {|fresher_avoid := (elements (vars_of et) ++ avoid)|}).1
.


Definition replace_and_collect
    {Σ : StaticModel}
    (et : (TermOver Expression2))
    :
    ((TermOver BuiltinOrVar)*ScList)
:=
    replace_and_collect1 [] et
.

Inductive SideConditionEq {Σ : StaticModel} :=
| sce_true
| sce_false
| sce_eq (l r : Expression2)
| sce_atom (pred : builtin_predicate_symbol) (args : list Expression2)
| sce_and (left : SideConditionEq) (right : SideConditionEq)
| sce_or (left : SideConditionEq) (right : SideConditionEq)
.

Fixpoint asIfWithEq {Σ : StaticModel} (sc : SideCondition) : SideConditionEq :=
    match sc with
    | sc_true => sce_true
    | sc_false => sce_false
    | sc_atom p a => sce_atom p a
    | sc_and l r => sce_and (asIfWithEq l) (asIfWithEq r)
    | sc_or l r => sce_or (asIfWithEq l) (asIfWithEq r)
    end
.

Fixpoint vars_of_sce {Σ : StaticModel} (sc : SideConditionEq) : gset variable :=
match sc with
| sce_true => ∅
| sce_false => ∅
| sce_atom _ args => vars_of args
| sce_eq l r => vars_of l ∪ vars_of r
| sce_and l r => vars_of_sce l ∪ vars_of_sce r
| sce_or l r => vars_of_sce l ∪ vars_of_sce r
end
.

#[export]
Instance  VarsOf_sce
    {Σ : StaticModel}
    : VarsOf SideConditionEq variable
:= {|
    vars_of := vars_of_sce ;
|}.

Definition SideConditionEq_evaluate
    {Σ : StaticModel}
    (program : ProgramT)
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
            let ts' := (fun e => Expression2_evaluate program ρ e nv) <$> args in
            ts ← list_collect ts';
            builtin_predicate_interp pred nv ts
        )
        | sce_eq l r =>
            gl ← Expression2_evaluate program ρ l nv;
            gr ← Expression2_evaluate program ρ r nv;
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
    {Σ : StaticModel}
    (sc : SideCondition)
    (program : ProgramT)
    (nv : NondetValue)
    (ρ : Valuation2)
    :
    SideConditionEq_evaluate program ρ nv (asIfWithEq sc)
    = SideCondition_evaluate program ρ nv sc
.
Proof.
    induction sc; simpl.
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
    {Σ : StaticModel}
 := {
    sss_term : TermOver BuiltinOrVar ;
    sss_sc : SideConditionEq ;
    (* In general, we try to ensure that vars_of sss_sc ⊆ vars_of sss_term,
        but we do not want to encode as a proof object because of performance reasons
     *)
}.

Definition SymbolicState {Σ : StaticModel } := list SimpleSymbolicState.


Definition denot_sss
    {Σ : StaticModel}
    (sss : SimpleSymbolicState)
    (g : TermOver builtin_value)
    : Type
:=
    { ρ : Valuation2 & sat2B ρ g sss.(sss_term) }
.

(* Search sigT. *)

Definition denot_ss
    {Σ : StaticModel}
    (ss : SymbolicState)
    (g : TermOver builtin_value)
    : Type
:=
    { sss : SimpleSymbolicState & ((sss ∈ ss) * (((denot_sss sss g))))%type }

.

Definition FalseState {Σ : StaticModel} : SymbolicState := [].

Fixpoint sclist_to_sceq {Σ : StaticModel} (l : ScList) : SideConditionEq :=
    match l with
    | [] => sce_true
    | xfl::xs =>
        let part_1 := sce_eq (e_variable xfl.1.1) (
        match xfl.1.2 with
        | inl q => e_query q xfl.2
        | inr f => e_fun f xfl.2
        end) in
        let part_2 := sclist_to_sceq xs in
        sce_and part_1 part_2
    end
.

Definition simpleStepByRule
    {Σ : StaticModel}
    (UA : UnificationAlgorithm)
    (sss : SimpleSymbolicState)
    (Act : Set)
    (r : RewritingRule2 Act)
    : SymbolicState
:=
    let osub := UA.(ua_unify) sss.(sss_term) r.(r_from) in
    match osub with
    | None => FalseState
    | Some sub =>
        let to'' := replace_and_collect1 (elements ((vars_of sub) ∪ vars_of (sss.(sss_sc)))) r.(r_to) in
        let sceq := sclist_to_sceq to''.2 in
        let to' := to''.1 in
        let to := subs_app sub to' in
        [{|sss_term := to; sss_sc := sceq|}]
    end
.


Module Implementation.

End Implementation.

