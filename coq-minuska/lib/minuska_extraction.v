
From Minuska Require Export
    prelude
    default_everything
    pval_ocaml_binding
    frontend
.
Extraction
    "Dsm.ml"
    mkRewritingRule2
    BuiltinInterface
    mkBuiltinInterface
    builtins_empty
    builtins_klike
    pi_trivial
    interpreter_results.RewritingTheory2_wf_dec
    frontend.srr_to_rr
    frontend.process_declarations
    frontend.to_theory
    frontend.realize_thy
    (* default_everything.Act *)
    default_everything.default_act
    default_everything.invisible_act
    default_everything.DSM
    default_everything.GT
    default_everything.gt_term
    default_everything.gt_over
    default_everything.global_naive_interpreter
    default_everything.global_naive_interpreter_ext
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