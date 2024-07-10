From Minuska Require
  interp_loop
.
From Test Require
  imp
  count3
.

Import String.
Import Ascii.

Time Compute (let steps := 10000 in
  @interp_loop.interp_loop
    default_everything.DSM
    spec.nondet_gen
    0
    imp.lang_interpreter
    steps
    count3.given_groundterm
).
