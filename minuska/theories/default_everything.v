From Minuska Require Import
    prelude
    spec
    string_variables
    builtins
    default_static_model
.

Variant Act := default_act | invisible_act.

#[export]
Instance DSM : StaticModel :=
    default_model (default_builtin.β)
.

Definition GT := @TermOver' string builtin_value.

Definition StepT := GT -> option GT.

Definition gt_term (s : string) (l : list GT) : GT := @t_term string builtin_value s l.
(*
Definition gt_over b := term_over b.
*)