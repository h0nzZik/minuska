From Minuska Require Import
    prelude
    spec
    ocaml_interface
.

Definition void_value_algebra (NV Sy : Type)
    : ValueAlgebra void NV Sy void void
:= {|
    builtin_function_interp
        := fun _ _ _ => None ;
    builtin_predicate_interp
        := fun _ _ _ => None ;
|}    .

Definition bindings (Q : Type) : string -> SymbolInfo void void void void Q void
:=
    fun s => si_none _ _ _ _ _ _
.

Definition BV_EDC : EDC void.
Proof.
  econstructor.
  apply _.
Defined.
Definition FS_EDC : EDC void.
Proof.
  econstructor.
  apply _.
Defined.
Definition PS_EDC : EDC void.
Proof.
  econstructor.
  apply _.
Defined.
