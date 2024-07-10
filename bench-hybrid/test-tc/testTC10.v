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
    default_everything.DSM
    spec.nondet_gen
    0
    twocounters.lang_interpreter
    steps
    tc10.given_groundterm
).
