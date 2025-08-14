From Minuska Require Import
    prelude
    spec
    ocaml_interface
.

Definition unit_hidden_model
    {BVal Ts : Type}
    (NdVal : Type)
:
    HiddenAlgebra unit BVal NdVal Ts void void void
:= {|
    hidden_init := tt;
    attribute_interpretation := fun a h args => None ;
    method_interpretation := fun m h args => None ;
    hidden_predicate_interpretation := fun p h args => None ;
|}.

Definition bindings (P HP F A Q M : Type)
    :
    string -> SymbolInfo P HP F A Q M
:=
fun s =>
match s with
| _ => si_none _ _ _ _ _ _
end.

Definition hv_edc : EDC unit.
Proof.
  econstructor.
  apply _.
Defined.
