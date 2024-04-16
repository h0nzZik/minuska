Require Extraction.
Extraction Language OCaml.
Require Import
  Coq.extraction.Extraction
  Coq.extraction.ExtrOcamlBasic
  Coq.extraction.ExtrOcamlNativeString
.
From Coq Require Import String Bool Arith ZArith List.

From Minuska Require Import
    prelude
    default_everything
.


Extraction
    "Dsm.ml"
    default_everything.DSM
    default_everything.GT
    default_everything.gt_term
.