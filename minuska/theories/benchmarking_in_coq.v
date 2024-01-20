From Minuska Require Import
    prelude
    examples
.

Require Import ZArith.

Module bench_fib_native.

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(1)"), ((fib_native.fib_interp_from_toint 1000 1%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(6)"), ((fib_native.fib_interp_from_toint 1000 6%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(11)"), ((fib_native.fib_interp_from_toint 1000 11%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(16)"), ((fib_native.fib_interp_from_toint 1000 16%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(21)"), ((fib_native.fib_interp_from_toint 1000 21%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(26)"), ((fib_native.fib_interp_from_toint 1000 26%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(31)"), ((fib_native.fib_interp_from_toint 1000 31%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(36)"), ((fib_native.fib_interp_from_toint 1000 36%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(41)"), ((fib_native.fib_interp_from_toint 1000 41%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(46)"), ((fib_native.fib_interp_from_toint 1000 46%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(51)"), ((fib_native.fib_interp_from_toint 1000 51%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(56)"), ((fib_native.fib_interp_from_toint 1000 56%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(61)"), ((fib_native.fib_interp_from_toint 1000 61%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(66)"), ((fib_native.fib_interp_from_toint 1000 66%Z).1.2)).


    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(71)"), ((fib_native.fib_interp_from_toint 1000 71%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(76)"), ((fib_native.fib_interp_from_toint 1000 76%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(81)"), ((fib_native.fib_interp_from_toint 1000 81%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(86)"), ((fib_native.fib_interp_from_toint 1000 86%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(91)"), ((fib_native.fib_interp_from_toint 1000 91%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(96)"), ((fib_native.fib_interp_from_toint 1000 96%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(101)"), ((fib_native.fib_interp_from_toint 1000 101%Z).1.2)).

    Time (* Redirect "blackhole.out" *)
    Compute (("bench: native-fib(106)"), ((fib_native.fib_interp_from_toint 1000 106%Z).1.2)).


End bench_fib_native.