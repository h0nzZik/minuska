From Minuska Require Import
  prelude
  default_everything
.


Definition fancy_number := 5.

Extraction
  "Myalgebra.ml"
   fancy_number
.
