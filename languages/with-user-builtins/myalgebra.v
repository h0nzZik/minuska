From Minuska Require Import -(coercions)
  prelude
  spec
  ocaml_interface
  model_algebra
  builtin.list_signature
  builtin.int_model
  builtin.list_model
  extensions
.


Definition list_int_model
  (TermSymbol : Type)
  (NondetValue : Type)
  :
  ValueAlgebra
    (bool+(simple_list_carrier Z))
    NondetValue
    TermSymbol
    ListFunSymbol
    ListPredSymbol
:=
  small_model_of_relaxed (
      list_wrapper _ _ _ _ _ _ (int_relaxed_va TermSymbol NondetValue)
    )
.

Existing Instance simple_list_carrier__countable.

Definition list_int_v_edc : EDC (bool+(simple_list_carrier Z)).
Proof.
  econstructor.
  apply _.
Defined.

Definition fs_edc : EDC ListFunSymbol.
Proof.
  econstructor.
  apply _.
Qed.

Definition ps_edc : EDC ListPredSymbol.
Proof.
  econstructor.
  apply _.
Qed.

Definition bindings (Q : Type) : string -> SymbolInfo ListPredSymbol void ListFunSymbol void Q void
:=
  fun si => si_none _ _ _ _ _ _
.



Extraction
  "myalgebra.ml"
    list_int_model
    list_int_v_edc
    fs_edc
    ps_edc
    bindings
.
