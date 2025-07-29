
From Minuska Require
    prelude
    default_everything
    default_static_model
    frontend
    builtin.empty
    builtin.klike
    pi.trivial
    hidden.hidden_unit
    ocaml_interface
.

Definition top_symbols_strings := @default_static_model.MySymbols.
Definition top_combine_symbol_classifiers := @ocaml_interface.combine_symbol_classifiers.
Definition top_builtin_empty_signature := @builtin.empty.mysignature.
Definition top_builtin_empty_model := @builtin.empty.β.
Definition top_builtin_empty_bindings := @builtin.empty.bindings.
Definition top_builtin_klike_signature := @builtin.klike.mysignature.
Definition top_builtin_klike_model := @builtin.klike.β.
Definition top_builtin_klike_bindings := @builtin.klike.bindings.
Definition top_pi_trivial_pi := @pi.trivial.MyProgramInfo.
Definition top_pi_trivial_bindings := @pi.trivial.bindings.
Definition top_hidden_unit_signature := @hidden.hidden_unit.unit_hidden_signature.
Definition top_hidden_unit_model := @hidden.hidden_unit.unit_hidden_model.
Definition top_hidden_unit_bindings := @hidden.hidden_unit.bindings.
Definition top_frontend_realize_thy := @frontend.realize_thy.
Definition top_frontend_to_thy := @frontend.to_theory.
Definition top_frontend_srr_to_rr := @frontend.srr_to_rr.
Definition top_frontend_process_declarations := @frontend.process_declarations.
Definition top_Label := @default_everything.Label.
Definition top_default_label := @default_everything.default_label.
Definition top_invisible_label := @default_everything.invisible_label.
Definition top_naive_interpreter := default_everything.global_naive_interpreter.
Definition top_naive_interpreter_ext := default_everything.global_naive_interpreter_ext.
Definition top_build_static_model := @default_everything.DSM.
Definition top_thy_wf := @interpreter_results.RewritingTheory2_wf_dec.
(* We extract only definitions from this module,
   and they all are prefixed with "top_"
   so that they do not collide with all the auxilliary definitions.
 *)
Extraction
    "Dsm.ml"
    (* mkRewritingRule2 *)
    top_symbols_strings
    top_combine_symbol_classifiers
    top_builtin_empty_signature
    top_builtin_empty_model
    top_builtin_empty_bindings
    top_builtin_klike_signature
    top_builtin_klike_model
    top_builtin_klike_bindings
    top_pi_trivial_pi
    top_pi_trivial_bindings
    top_hidden_unit_signature
    top_hidden_unit_model
    top_hidden_unit_bindings
    top_thy_wf
    (* interpreter_results.RewritingTheory2_wf_dec *)
    top_frontend_srr_to_rr
    top_frontend_process_declarations
    top_frontend_to_thy
    top_frontend_realize_thy
    top_Label
    top_default_label
    top_invisible_label
    top_build_static_model
    (* default_everything.DSM
    default_everything.GT
    default_everything.gt_term
    default_everything.gt_over *)
    top_naive_interpreter
    top_naive_interpreter_ext
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