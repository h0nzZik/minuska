From Minuska Require
  interp_loop
.
From Test Require
  twocounters
  tc50
.

Import String.
Import Ascii.

Time Compute (let steps := 10000 in
  @interp_loop.interp_loop
    default_everything.DSM
    twocounters.lang_interpreter
    steps
    tc50.given_groundterm
).
