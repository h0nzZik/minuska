
This is how to open Coqide running with Minuska-provided Coq and libraries (and Minuska itself):
```sh
bash$ minuska info coqflags | xargs coqide -coqtop $(minuska info coqbin)/coqidetop.opt myalgebra.v
```
The reason for the `xargs` is that `minuska info coqflags` prints a list of flags, and we need to split these flags into individual arguments for `coqide`.

