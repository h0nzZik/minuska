# Minuska User Guide

This file describes Minuska from the user's point of view.

## Building

To build Minuska from source, you can run
```sh
nix develop '.#with-minuska'
```
which builds the project and populates the PATH environment variable with the `minuska` command. You can also try the `bench-standalone` devshell. Alternatively, RPM and DEB packages are available.


## Using Minuska

The main use-case for Minuska is currently in generating interpreters from formal language definitions. Typically, a language definition has the form of an `*.m` file, such as [this one](../languages/arith/def.m). A language definition can also have the form of a direct, Coq-based definition; however, there is not much tooling support for that style of work.

Let's have a closer look at the above-referenced language definition file for evaluation of arithmetic expressions.

### Semantic rules

The main part of the language definition are "semantic rules" for addition and subtraction:
```
@rule/simple [plus]: plus[X,Y] => z.plus(X, Y) where @and(z.is(X), z.is(Y)) ;
@rule/simple [minus]: minus[X,Y] => z.minus(X, Y) where @and(z.is(X), z.is(Y)) ;
```
Each rule consists of
- the `@rule` keyword
- optionally followed by a "frame identifier" behind a slash (`/`) (such as `/simple`);
- a "rule label" in square brackets (such as `[plus]`);
- a "left-hand side pattern" such as `plus[X,Y]`;
- a "right-hand side term-with-expressions" such as `z.plus(X, Y)`; and
- a "side condition" such as `@and(z.is(X), z.is(Y))`.

The consequence of such a rule for an interpreter of the specified language is that a program state (formally known as "configuration") that _matches_ the left-hand side pattern can be _rewritten_ to a new configuration, which a result of evaluating the term-with-expressions with variables assigned to the same values as in the left-hand side. In the case of the `plus` rule, the term-with-expressions is one expression, calling the _built-in function_ named `z.plus` which simply adds two integers together.

### Subterm rewriting

However, the `plus` rule can be applied only to integers: the built-in function `z.plus` would get stuck on any other argument. To evaluate nested arithmetic expressions, the typical approach of these kind of frameworks (K and Minuska) is to implement a stack-based evaluator. Because doing so by hand is _boring_, Minuska (similarly to K) provides constructs that help with that. Specifically, one can declare the symbols `plus` and `minus` to be strict in both of their arguments
```
@strictness: [
  plus of_arity 2 in [0,1],
  minus of_arity 2 in [0,1]
];
```
which instructs Minuska to automatically generate rewrite rules for evaluation of subexpressions. However, for such approach to make sense, one needs to consider the concept of _value_.

A value is a term that we do not want to further rewrite. In the context of a language of arithmetic expressions, a value is simply an integer:
```
@value(X): z.is(X) ;
```
Here, `z.is` is a _built-in predicate_ that holds only on integers. (Specifically, it is a _negable predicate_ - a predicate that can safely be negated. In Minuska, not all predicates can be negated, because [negations are bad](https://h0nzzik.github.io/posts/008-framing-for-free/) and break separation-logic-style reasoning, which is a feature on the "TODO" list of Minuska.)

### Contexts and frames

However, the stack machine also needs to keep its stack somewhere. That is where "frames" and "contexts" come to place.
```
@context(HOLE): c[HOLE];
@frames: [
  simple(X): c[builtin.cseq [X,REST]]
];
```

The `@context` declaration says that the whole execution stack should be kept under the (unary) symbol `c`. The stack is like a list separated using the `builtin.cseq` binary symbol. For example, a stack `[1,2,3]` (with `1` at the top) is represented as the term
```
builtin.cseq[1, builtin.cseq[2, builtin.cseq[3, builtin.empty_cseq]
```
With this approach, a semantic rule for addition could look like the following:
```
@rule/simple [plus]: c[builtin.cseq[plus[X,Y], REST]] => c[builtin.cseq[z.plus(X, Y), REST]] where @and(z.is(X), z.is(Y)) ;
```
It is easily visible that there is so much uninteresting noise in such a rule! Therefore, the `simple` frame can be used to abstrac away all this noise. In general, one can declare multiple frames to be used in different contexts, which is a feature more useful for larger languages.

