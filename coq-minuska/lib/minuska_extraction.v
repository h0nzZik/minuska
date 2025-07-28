
From Minuska Require Export
    prelude
    default_everything
    frontend
    builtin.empty
    builtin.klike
    pi.trivial
    ocaml_interface
.
Extraction
    "Dsm.ml"
    mkRewritingRule2
    ocaml_interface.combine_symbol_classifiers
    builtin.empty.β
    builtin.empty.bindings
    builtin.klike.β
    builtin.klike.bindings
    pi.trivial.MyProgramInfo
    pi.trivial.bindings
    interpreter_results.RewritingTheory2_wf_dec
    frontend.srr_to_rr
    frontend.process_declarations
    frontend.to_theory
    frontend.realize_thy
    default_everything.Label
    default_everything.default_label
    default_everything.invisible_label
    (* default_everything.DSM
    default_everything.GT
    default_everything.gt_term
    default_everything.gt_over *)
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