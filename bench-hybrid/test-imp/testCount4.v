From Minuska Require
  interp_loop
.
From Test Require
  imp
  count4
.

Import String.
Import Ascii.

Time Compute (let steps := 10000 in
  @interp_loop.interp_loop
    _
    spec.nondet_gen
    0
    (imp.lang_interpreter count4.given_groundterm)
    steps
    count4.given_groundterm
).
