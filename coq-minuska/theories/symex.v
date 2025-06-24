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

Definition replace_and_collect
    {Σ : StaticModel}
    (et : (TermOver Expression2))
    :
    ((TermOver BuiltinOrVar)*ScList)
:=
    (replace_and_collect0 et {|fresher_avoid := (elements (vars_of et))|}).1
.





Module Implementation.

End Implementation.

