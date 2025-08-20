(* Import this module in your 3rd-party, out-of-source extension *)
From Minuska Require Import -(coercions)
  prelude
  spec
  ocaml_interface
.

From Coq Require Extraction.
Extraction Language OCaml.
From Coq.extraction Require Import
  Extraction
  ExtrOcamlBasic
  ExtrOcamlNativeString
  ExtrOcamlZBigInt
  ExtrOcamlNatBigInt
.

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
