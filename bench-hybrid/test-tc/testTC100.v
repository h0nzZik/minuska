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
    default_everything.DSM
    spec.nondet_gen
    0
    twocounters.lang_interpreter
    steps
    tc100.given_groundterm
).
