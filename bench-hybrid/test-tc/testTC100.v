From Minuska Require
  interp_loop
.
From Test Require
  twocounters
  tc100
.

Import String.
Import Ascii.

Time Compute (let steps := 10000 in
  @interp_loop.interp_loop
    _
    spec.nondet_gen
    0
    (twocounters.lang_interpreter tc100.given_groundterm)
    steps
    tc100.given_groundterm
).
