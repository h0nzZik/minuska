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

Definition GT := @TermOver' symbol builtin_value.

Definition StepT := GT -> option GT.