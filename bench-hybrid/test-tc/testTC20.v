From Minuska Require
  interp_loop
.
From Test Require
  twocounters
  tc20
.

Import String.
Import Ascii.

Time Compute (let steps := 10000 in
  @interp_loop.interp_loop
    default_everything.DSM
    twocounters.lang_interpreter
    steps
    tc20.given_groundterm
).
