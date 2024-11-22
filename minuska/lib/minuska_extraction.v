
From Minuska Require Export
    prelude
    default_everything
    pval_ocaml_binding
.
From Minuska Require Import
    builtin.empty
    builtin.klike
.

Set Printing All.
Class BuiltinInterface (NondetValue : Type) := {
    bi_beta : Builtin (NondetValue : Type) ;
    bi_bindings : BuiltinsBinding ;
    bi_inject_bool : bool -> option (@builtin_value _ _ NondetValue bi_beta) ;
    bi_inject_Z : Z -> option (@builtin_value _ _ NondetValue bi_beta) ;
    bi_inject_string : string -> option (@builtin_value _ _ NondetValue bi_beta) ;
    bi_eject : (@builtin_value _ _ NondetValue bi_beta) -> option (bool+Z+string+unit)%type ;
}.

Definition builtins_empty : BuiltinInterface MyUnit := {|
    bi_beta := builtin.empty.β ;
    bi_bindings := builtin.empty.builtins_binding ;
    bi_inject_bool := @builtin.empty.inject_bool string;
    bi_inject_Z := @builtin.empty.inject_Z string;
    bi_inject_string := @builtin.empty.inject_string string;
|}.

Definition builtins_klike : BuiltinInterface MyUnit := {|
    bi_beta := builtin.klike.β ;
    bi_bindings := builtin.klike.builtins_binding ;
    bi_inject_bool := fun b => @builtin.klike.inject_bool string b;
    bi_inject_Z := fun z => @builtin.klike.inject_Z string z;
    bi_inject_string := fun s => @builtin.klike.inject_string string s;
|}.


Extraction
    "Dsm.ml"
    BuiltinInterface
    builtins_empty
    builtins_klike
    default_everything.DSM
    default_everything.GT
    default_everything.gt_term
    default_everything.gt_over
    default_everything.global_naive_interpreter
    (*
      Error:
The informative inductive type prod has a Prop instance
in naive_interpreter.naive_interpreter_sound (or in its mutual block).
This happens when a sort-polymorphic singleton inductive type
has logical parameters, such as (I,I) : (True * True) : Prop.
Extraction cannot handle this situation yet.
Instead, use a sort-monomorphic type such as (True /\ True)
or extract to Haskell.
    *)
    (* default_everything.global_naive_interpreter_sound *)
.