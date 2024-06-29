# Benchmarks for languages specified directly in Coq

To get some statistics about the languages defined in [../languages-in-coq](../languages-in-coq), run:
```sh
nix develop '.#bench-coq' --command ./build-and-profile.sh
```
The first column is the name of the benchmark, second column is the time of the `Compute` inside Coq (measured by Coq's `Time` command), and the third columns is the total time of `coqc` as measured by the GNU `time` utility.

The last two columns of Figure 3 of [this paper](h0nzzik.github.io/papers/minuska-extended.pdf) can be obtained by filtering the output of the above command.
For an illustrative example, a recent run on my "Intel(R) Core(TM) i7-10510U CPU @ 1.80GHz" laptop yield, among other, the following rows:
```
two-counters(10), 0.015, 0.73
two-counters(20), 0.01, 0.74
two-counters(50), 0.014, 0.73
two-counters(100), 0.008, 0.78
unary-fib(5), 0.133, 0.81
unary-fact(3), 0.285, 0.98
```

Similarly, the right table of Figure 2 of that paper corresponds to the following part of the output:
```
two-counters(10), 0.015, 0.73
two-counters(100), 0.008, 0.78
two-counters(1000), 0.011, 0.75
two-counters(10000), 0.026, 0.74
```

The middle two columns of Figure 4 of that paper are covered as well:
```
imp-count-to(1), 0.642, 1.43
imp-count-to(2), 1.078, 1.79
imp-count-to(3), 1.453, 2.15
imp-count-to(4), 1.911, 2.63
imp-count-to(5), 2.322, 3.00
imp-count-to(6), 2.569, 3.25
imp-count-to(7), 3.004, 3.70
```
(For the last column of that figure, see [../bench-standalone](../bench-standalone) and [../bench-hybrid](../bench-hybrid)).

Figure 5 of that paper is also contained in the output:
```
native-fib(1), 0.01, 0.75
native-fib(6), 0.015, 0.73
native-fib(11), 0.017, 0.73
native-fib(16), 0.021, 0.73
native-fib(21), 0.034, 0.74
native-fib(26), 0.038, 0.84
native-fib(31), 0.039, 0.89
native-fib(36), 0.038, 0.77
native-fib(41), 0.041, 0.74
native-fib(46), 0.044, 0.76
native-fib(51), 0.05, 0.76
native-fib(56), 0.047, 0.76
native-fib(61), 0.06, 0.79
native-fib(66), 0.059, 0.75
native-fib(71), 0.058, 0.74
native-fib(76), 0.072, 0.80
native-fib(81), 0.071, 0.79
native-fib(86), 0.102, 0.79
native-fib(91), 0.105, 0.80
native-fib(96), 0.095, 0.79
native-fib(101), 0.107, 0.79
native-fib(106), 0.115, 0.80

unary-fib(1), 0.074, 0.77
unary-fib(2), 0.079, 0.78
unary-fib(3), 0.093, 0.77
unary-fib(4), 0.103, 0.78
unary-fib(5), 0.137, 0.82
unary-fib(6), 0.2, 0.90
unary-fib(7), 0.311, 1.00
unary-fib(8), 0.459, 1.20
unary-fib(9), 0.882, 1.59
unary-fib(10), 1.42, 2.12
unary-fib(11), 2.471, 3.15

unary-fact(1), 0.108, 0.78
unary-fact(2), 0.167, 0.85
unary-fact(3), 0.285, 0.96
unary-fact(4), 0.575, 1.35
unary-fact(5), 2.102, 2.78
unary-fact(6), 10.318, 10.97
```
