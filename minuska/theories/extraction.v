Require Extraction.
Extraction Language OCaml.

From Minuska Require Import examples.

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))"
.



Extraction
    "ExampleLang.ml"
    example_1.interp_loop_number
.


Extraction
    "TwoCounters.ml"
    two_counters.interp_loop_number
.