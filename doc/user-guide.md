# Minuska User Guide

This file describes Minuska from the user's point of view.

## Building

To build Minuska from source, you can either run
```sh
nix shell '.#minuska'
```
which builds the project and populates the PATH environment variable with a `minuska` command,
or you can first install [all the dependencies](./dependencies.md)
and run
```sh
cd <project-root>/minuska
dune build @all
dune install --prefix <install-directory>
```
which installs the `minuska` command into `<install-directory>/bin`.


## Using Minuska

Minuska can be used as a standalone command-line tool, as a Coq library, or combined.
We illustrate the usage on a trivial 'language definition' [decrement.m](./examples-standalone/m/decrement.m) that accepts unary-encoded numbers as programs
and decrements the given number until it gets to zero (or smaller).
The illustrative commands are supposed to be run from the root of this repository.

### From the command-line

To see all the options `minuska` offers, run run:
```sh
minuska --help
```

#### Generating interpreters and running programs

To generate an interpreter from a language definition, use the `minuska compile` command. For example,
```sh
minuska compile ./examples-standalone/m/decrement.m decrement.exe
```
generates the interpreter named `decrement.exe`.
The generated interpreter can be used to execute a program for a given number of steps.
For example, given the [unary-encoded number three](../examples-standalone/m/decrement.d/three), running
```sh
./decrement.exe ./examples-standalone/m/decrement.d/three --depth 3
```
outputs the unary-encoded number one
```
Taken 3 steps
succ[zero[]]
```
because the very first step is used to initialize the program.
Indeed, running
```sh
./decrement.exe ./examples-standalone/m/decrement.d/three --depth 0
```
shows us the initial configuration:
```
Taken 0 steps
builtin.init[succ[succ[succ[zero[]]]]]
```

To see all the options provided by the interpreter, run:
```sh
./decrement.exe --help
```

#### Generating a Coq definition

To generate a `*.v` file containing a Coq definition, run:
```
minuska def2coq ./examples-standalone/m/decrement.m decrement.v
```

