Require Extraction.
Extraction Language OCaml.
Require Export
  Coq.extraction.Extraction
  Coq.extraction.ExtrOcamlBasic
  Coq.extraction.ExtrOcamlZInt
  Coq.extraction.ExtrOcamlNatInt
.
From Coq Require Import String Bool Arith ZArith List.

From Minuska Require Import
    prelude
    default_everything
.


Extraction
    "Dsm.ml"
    default_everything.myBuiltinType
    default_everything.myBuiltin
    default_everything.DSM
    default_everything.GT
    default_everything.gt_term
    default_everything.gt_over
.