# Minusa - ideas and missing features

## Concrete syntax of programming languages

Minuska operates on an abstract representation of programming language syntax. There is currently no support for specifying, parsing of, and unparsing into concrete syntax of programming languages.

## Semantics of contexts

Currently, strictness declarations and contexts are implemented by desugaring them to rewriting rules by the [frontend](https://h0nzzik.github.io/minuska/Minuska.frontend.html).
While this approach works, it does not equip the user with any means of high-level reasoning about the high-level constructs (that is, contexts and strictness).
We are working on a precise [syntax](https://h0nzzik.github.io/minuska/Minuska.minusl_syntax.html) and [semantics](https://h0nzzik.github.io/minuska/Minuska.minusl_semantics.html) for contexts, with an explicit [translation](https://h0nzzik.github.io/minuska/Minuska.minusl_compile.html) to rewriting rules that should be formally [verified to preserve the semantics](https://h0nzzik.github.io/minuska/Minuska.minusl_compile_properties.html).

## Symbolic execution

In principle, it should be possible to generate symbolic execution engines for languages defined in Minuska, simply by using unification instead of pattern matching in the interpreter.
An option would be to use the [Coq Color library](https://github.com/fblanqui/color) which already contains a provably correct implementation of an unification algorithm.
However, this has not been implemented yet.
Even if this gets implemented, we would need to have a simplification engine to prune infeasible branches; this would be best done using some LTac scripting inside Coq, using tactics like `lia`,
[`itauto`](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.9), and possibly [`smt`](https://smtcoq.github.io/).

## Deductive verification

[K Framework](https://kframework.org/) a implements coinduction-based logic (reachability logic [1](https://ieeexplore.ieee.org/document/6571568) [2](https://link.springer.com/chapter/10.1007/978-3-319-44802-2_8))
that can be used to prove partial correctness properties of programs with loops, recursion, or other source of circular behavior. This would be nice to have, but it depends on the symbolic execution being implemented.


## Testing type soundness

We could use the QuickChick framework to automatically test whether a given language definition behaves reasonably on well-typed programs. This includes the absence of calls to builtin functions that would return an error value.
