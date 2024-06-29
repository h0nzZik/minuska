## Language examples in Coq

This directory contains a few language definitions encoded directly in Coq, as well as derived interpreters for those languages. Specifically:
- `examples.two_counters.interp` in [theories/examples.v](theories/examples.v) is an interpreter for the "two counters" language over unary-encoded natural numbers;
- `examples.two_counters_Z.interp` is the same but over built-in integers (that is, the `Z` type from Coq's standard library);
- `examples.arith.interp` is an interpreter for a simple language of arithmetic expressions;
- `examples.fib_native.interp` calculates a Fibonacci sequence (over built-in integers), in an imperative style
- `examples.imp.interp` interpretes a simple imperative language with arithmetic expressions, assignment, conditions, and loops;
- `examples_unary_nat.unary_nat.interp_fib` implements Fibonacci sequence in the same style, but over unary-encoded natural numbers;
- `examples_unary_nat.unary_nat.interp_fact` implements factorial in the imperative style, over unary-encoded natural numbers.

No performance benchmarks for these are provided in this directory, but see [../bench-coq](../bench-coq) which uses this directory as a dependency.

