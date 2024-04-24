From Minuska Require
  interp_loop
.
From Test Require
  imp
  count7
.

Import String.
Import Ascii.

Time Compute (let steps := 10000 in
  @interp_loop.interp_loop
    default_everything.DSM
    imp.lang_interpreter
    steps
    count7.given_groundterm
).
