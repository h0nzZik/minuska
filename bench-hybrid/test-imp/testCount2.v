From Minuska Require
  interp_loop
.
From Test Require
  imp
  count2
.

Import String.
Import Ascii.

Time Compute (let steps := 10000 in
  @interp_loop.interp_loop
    _
    spec.nondet_gen
    0
    (imp.lang_interpreter count2.given_groundterm)
    steps
    count2.given_groundterm
).
