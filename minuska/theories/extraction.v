Require Extraction.
Extraction Language OCaml.
Require Import
  Coq.extraction.ExtrOcamlString
  Coq.extraction.ExtrOcamlZBigInt
.
From Coq Require Import Bool Arith ZArith List.

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

Extraction
    "FibNative.ml"
    fib_native.fib_interp_from_toint
.

Extraction
  "SumToN.ml"
  imp.interp_program_count_to
.