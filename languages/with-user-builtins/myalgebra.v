From Minuska Require Import
  prelude
  default_everything
.


Definition fancy_number := 5.

Extraction
  "myalgebra.ml"
   fancy_number
.
