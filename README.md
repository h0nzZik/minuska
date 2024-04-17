# Minuska - a formally verified semantic framework

Minuska is a framework for defining operational semantics ("language definitions") of programming languages and deriving tools from them.
Currently, the project is a research prototype, and the only tools derivable from language definitions are interpreters.
Users looking for a mature programming language framework are advised to check out [K framework](https://kframework.org/) or [PLT-Redex](https://redex.racket-lang.org/).

Minuska is built on top of the [Coq proof assistant](https://coq.inria.fr/). At its core is a simple language MinusLang for expressing programming language semantics
in an exact, unambiguous way: MinusLang has a simple formal semantics (mechanized in [spec.v](https://h0nzzik.github.io/minuska/Minuska.spec.html)),
and every MinusLang definition induces a transition relation between program configurations.
Similarly, in Minuska we can mathematically describe what a particular tool for a given language should do.
For example, a [step interpreter](https://h0nzzik.github.io/minuska/Minuska.spec_interpreter.html#Interpreter) takes a program configuration
and either returns a next configuration, or returns `None`.
We have defined what does it mean for an interpreter to be [correct with respect to a language definition](https://h0nzzik.github.io/minuska/Minuska.spec_interpreter.html#Interpreter_sound'),
defined some mild criteria for when a language definition is [amenable to interpretation](https://h0nzzik.github.io/minuska/Minuska.spec_interpreter.html#RewritingRule2_wf),
created a [very simple generic interpreter](https://h0nzzik.github.io/minuska/Minuska.naive_interpreter.html#naive_interpreter) that is parametric in a MinusLang language definition,
and [proved it correct](https://h0nzzik.github.io/minuska/Minuska.naive_interpreter.html#naive_interpreter_sound).

There are two ways of writing a language definition in Minuska: either as a Coq definition ([example](https://h0nzzik.github.io/minuska/Minuska.example.html)), or as a standalone `*.m` file ([example](https://github.com/h0nzZik/minuska/blob/main/minuska-examples/decrement.m)) that can be automatically converted to a Coq `*.v` file:
```sh
minuska def2coq language.m language.v
```
As for the generated interpreters: these can also be used either from inside the Coq, or compiled (using Coq's extraction mechanism) into a standalone executable file:
```sh
minuska compile language.m language-interpreter.exe
```
Note that the `minuska` command is still under an active development: it is not feature complete and may contain bugs.

# Geting Minuska up and running

The simplest way is to use the provided Nix Flake:
```sh
nix shell '.#minuska'
```

One can also build and install it using [Dune](https://dune.readthedocs.io/en/stable/):
```sh
dune build @all
```
but this requires one to install all the dependencies manually.
To typecheck the Coq development, one needs:
- [Coq](https://coq.inria.fr/) 8.19
- [stdpp](https://gitlab.mpi-sws.org/iris/stdpp) > 1.9.0
- [equations](https://mattam82.github.io/Coq-Equations/) 1.3

# Missing features

In principle, many features could be implemented in Minuska that would make the framework more useful.

## Concrete syntax of programming languages

Minuska operates on an abstract representation of programming language syntax. There is currently no support for specifying, parsing of, and unparsing into concrete syntax of programming languages.

## Symbolic execution

In principle, it should be possible to generate symbolic execution engines for languages defined in Minuska, simply by using unification instead of pattern matching in the interpreter.
An option would be to use the [Coq Color library](https://github.com/fblanqui/color) which already contains a provably correct implementation of an unification algorithm.
However, this has not been implemented yet.
Even if this gets implemented, we would need to have a simplification engine to prune infeasible branches; this would be best done using some LTac scripting inside Coq, using tactics like `lia`,
[`itauto`](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.9), and possibly [`smt`](https://smtcoq.github.io/).

## Deductive verification

[K Framework](https://kframework.org/) a implements coinduction-based logic (reachability logic [1](https://ieeexplore.ieee.org/document/6571568) [2](https://link.springer.com/chapter/10.1007/978-3-319-44802-2_8))
that can be used to prove partial correctness properties of programs with loops, recursion, or other source of circular behavior. This would be nice to have, but it depends on the symbolic execution being implemented.


# Developer documentation
[CoqDoc](https://h0nzzik.github.io/minuska/toc.html)

