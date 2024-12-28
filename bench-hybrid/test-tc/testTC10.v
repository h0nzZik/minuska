From Minuska Require
  interp_loop
.
From Test Require
  twocounters
  tc10
.

Import String.
Import Ascii.

Time Compute (let steps := 10000 in
  @interp_loop.interp_loop
    _
    spec.nondet_gen
    0
    (twocounters.lang_interpreter tc10.given_groundterm)
    steps
    tc10.given_groundterm
).
