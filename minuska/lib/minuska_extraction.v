
From Minuska Require Export
    prelude
    default_everything
    pval_ocaml_binding
.
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