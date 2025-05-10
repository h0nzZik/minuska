# Minuska - a formally verified semantic framework

Minuska is a framework for defining operational semantics ("language definitions") of programming languages and deriving tools from them.
Currently, the project is a research prototype, and the only tools derivable from language definitions are interpreters.
Users looking for a mature programming language framework are advised to check out [K framework](https://kframework.org/) or [PLT-Redex](https://redex.racket-lang.org/).
(For a more detailed comparison to K framework, look [here](./doc/comparison-to-k-framework.md).)

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

There are two ways of writing a language definition in Minuska: either as a Coq definition ([example](https://h0nzzik.github.io/minuska/Minuska.example.html)), or as a standalone `*.m` file ([example](https://github.com/h0nzZik/minuska/blob/main/languages/decrement/decrement.m)) that can be automatically converted to a Coq `*.v` file:
```sh
minuska def2coq language.m language.v
```
As for the generated interpreters: these can also be used either from inside the Coq, or compiled (using Coq's extraction mechanism) into a standalone executable file:
```sh
minuska compile language.m language-interpreter.exe
```
Note that the `minuska` command is still under an active development: it is not feature complete and may contain bugs.
More importantly, the command-line interface is NOT formally verified, as it is written in OCaml rather than Coq.

# Using Minuska

The simplest way is to use the provided Nix Flake
```sh
nix develop '.#with-minuska'
```
which provides the `minuska` command, as well as the required version of Coq and its libraries.
Consult the [user guide](./doc/user-guide.md) for more details.

# Working on Minuska

The easiest way to start is using the Nix Flake:
```sh
nix develop '.#minuska'
cd minuska/
```
See the [developer guide](./doc/developer-guide.md) for more details.
Also, see [CoqDoc](https://h0nzzik.github.io/minuska/toc.html)

# Missing features

In principle, many features could be implemented in Minuska that would make the framework more useful.
These include support for concrete syntax of programming languages, formalization of the strictness declarations, symbolic execution, and deductive verification.
See the [ideas document](./doc/ideas.md)


# Papers

There exists a SEFM'24 [paper](https://doi.org/10.1007/978-3-031-77382-2_12) titled 'Minuska: Towards a Formally Verified Programming Language Framework'. Also, an older version is available [on Arxiv](https://arxiv.org/abs/2409.11530).
