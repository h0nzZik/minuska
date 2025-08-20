From Coq Require Extraction.
Extraction Language OCaml.
From Coq.extraction Require Import
  Extraction
  ExtrOcamlBasic
  ExtrOcamlNativeString
  ExtrOcamlZBigInt
  ExtrOcamlNatBigInt
.

From Minuska Require Import -(coercions)
  prelude
  spec
  ocaml_interface
  model_algebra
  builtin.list_signature
  builtin.int_model
  builtin.list_model
.

(* TODO put these into some reusable module in Minuska *)

Extract Inductive Empty_set => "Libminuska.Extracted.empty_set" [].

Extract Inductive SymbolInfo => "Libminuska.Extracted.symbolInfo" [
  "Libminuska.Extracted.Si_none"
  "Libminuska.Extracted.Si_predicate"
  "Libminuska.Extracted.Si_hidden_predicate"
  "Libminuska.Extracted.Si_function"
  "Libminuska.Extracted.Si_attribute"
  "Libminuska.Extracted.Si_query"
  "Libminuska.Extracted.Si_method"
].

Extract Constant stdpp.countable.encode => "Libminuska.Extracted.encode".
Extract Constant stdpp.countable.decode => "Libminuska.Extracted.decode".
Extract Inductive stdpp.countable.Countable => "Libminuska.Extracted.countable" [
   "(fun (a,b) -> { Libminuska.Extracted.encode = a; Libminuska.Extracted.decode = b; })"
].

Extract Inductive EDC => "Libminuska.Extracted.eDC" [
  "(fun (a,b) -> { Libminuska.Extracted.edc_eqdec=a; Libminuska.Extracted.edc_count=b; })"
].

Extract Inductive TermOver' => "Libminuska.Extracted.termOver'" [
  "Libminuska.Extracted.T_over"
  "Libminuska.Extracted.T_term"
].

Extract Inductive ValueAlgebra => "Libminuska.Extracted.valueAlgebra" [
  "(fun (a,b) -> { Libminuska.Extracted.builtin_function_interp = a; Libminuska.Extracted.builtin_predicate_interp = b; })"
].

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
