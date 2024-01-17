From Minuska Require Import
    prelude
    examples
.

Require Import ZArith.

Module bench_fib_native.

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 1%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 6%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 11%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 16%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 21%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 26%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 31%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 36%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 41%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 46%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 51%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 56%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 61%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 66%Z).1.2).


    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 71%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 76%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 81%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 86%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 91%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 96%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 101%Z).1.2).

    Time Redirect "benchmark.out"
    Compute ((fib_native.fib_interp_from 1000 106%Z).1.2).


End bench_fib_native.