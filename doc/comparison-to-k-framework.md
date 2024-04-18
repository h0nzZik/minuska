# Comparison to K framework

Minuska is inspired by [recent work on Xiaohong Chen and others](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_23) on extending K framework with proof certificate generation for certain tasks.

## Backend

### Terms
K framework, is based on rewriting of terms with builtins.
There, the configuration of the program being executed
is a closed term whose leaves can be either nullary terms (that is, constants)
or builtins (also known as domain values) -
such as integers, lists, or finite maps.
Our approach is very similar; the main difference is that in Minuska, terms
are unsorted and varyadic, while they are sorted and polyadic in K.
This comes with the usual costs and benefits: 
a semantic engineer using K can benefit from an early error detection
at the cost of lower flexibility,
and knowing sorts statically could in principle be exploited by optimizations,
although we do not know whether K actually uses the knowledge
for that purpose.
Another difference is that in K, proofs of domain reasoning
are omitted from the resulting proof certificate, while in Minuska,
the implementation of builtins is verified in Coq.
For example, we use a verified implementation of lists from Coq's
standard library, and of finite maps from the Std++ library.

### Rewriting
K framework, as well as Minuska, implements the topmost semantics
of rewriting rules. This means that matching a rule against a concrete term
always starts at the top of the term. This is in contrast with rewriting engines
such as Maude, where rules can be used to rewrite subterms in a context of an unbounded size.
In addition, K framework supports also so-called function rules,
which are rules about symbols declared as functions.
K's function rules can be used to match and rewrite anywhere in a term,
and they do so in between regular rewriting steps.
However, we believe that function rules do not present a significant advantage of K
against Minuska, and have three reasons for that belief.

First, since function rules are applied in-between computational steps,
they are hard to debug in practice: as far as we know, K does not have
any debugging facilities for showing what happens inside one computational step.
Second, function rules do not play nice with K's formal verification facilities.
The K framework implements a logic known as ``reachability logic'' (RL)
for reasoning about circular and repetetive behavior of programs.
In RL, one can pose the claim to be proven as a so-called circularity
and use it to discharge proof obligations after prograss has been made using a computational step;
however, one cannot effectively use RL for reasoning about circular behavior of function symbols,
because no computational steps happen between the simplifications.
We are not aware of any other mechanism for reasoning about circular behavior
of function symbols implemented in K; perhaps this missing but needed feature
is the reason why developments done in K sometimes resort to adding
unproven lemmas about function symbols (as done, e.g., in the development
of KEVM.
Third, in K framework, function rules are implemented as equalities
in the underlying logic (that is, matching logic); these equalities are then interpreted in an oriented way
by the K-based tools. Therefore, it is very easy for an user
to silently introduce
a logical inconsistency into the language: for example, by defining
a function symbol `f` and two rules, one of which rewrites `f`
to 0 and the other to $1$.
Any non-confluence in function rules gets translated to a logical inconsistency,
from which anything follows, rendering any generated proof certificates useless.
(In K framework, the generated proof objects are not checked for consistency of assumptions.
This cannot happen in Minuska: intuitively, because we do not allow function rules;
technically, because we do not axiomatize the underlying static model
but provide it directly.)


### Languages
In the referenced paper, the authors use a definition of a simple imperative language
(named ``IMP'') featuring
integer variables and basic arithmetic (addition, subtraction)
and control-flow (sequencing, conditionals, loops) constructs.
There, ``IMP'' is used only for illustrative purposes,
to explain the basic concepts of the K framework:
that language definition is not supported in their work.
However, in our work we define a similar language, and our verified interpreter
can actually run programs written in that language with reasonable performance.

## Frontend

K is equipped with a front-end language that features a nice syntax for writing language definitions.
The frontend language of K does not have a formal semantics - its only semantics is the frontend itself
which transforms the user-written specification into the format that K uses internally - Kore.
This is in principle similar to Minuska, where the user usually does not write the terms of semantic rules
by hand, but uses a layer of notations and translations that make semantic engineering tasks more effective.
Therefore, one should think about both the K frontend and Minuska's frontend as part of the trust base of
the respective tools.
K's frontend supports more features than that one of Minuska.


Next, we would like to highlight a few among the features of K's frontend.

### Parsing
Minuska does not do any parsing. The user of Minuska can write their own parsers for their languages,
or they can rely on Coq's Notation mechanism; both of these options do not come with any formal guarantees.
However, in principle, one could use a verified parser, such as Menhir or AllStar.
K framework can generate parsers for programs in the modeled languages automaticaly;
however, no proof certificates are currently generated for these.


### Configuration concretization
In K, patterns on sides of rewriting rules
are automatically completed to match the declared shape of configurations.
In practices, this means that the user does not have to mention parts of configurations that are not relevant
for the particular rule, as they are automatically preserved by transitions.
Minuska does not have this feature; however, as the development of language definitions in Minuska is done in Coq,
the user can use arbitrary Coq facilities (such as auxiliary definitions and notations)
to make her language definition more compact.

### Controling evaluation order
K supports strictness attributes for specifying order of evaluations of subterms of a term with a given symbol.
From these attributes, context declarations (as in evaluation contexts semantics)
are generated, from which it generates heating and cooling rules that are used for extraction of a redex out of a context
and insertion of the resulting value back.
Minuska has strictness declarations doing essentially the same thing.

### Local rewrites
K also supports local rewrites: the user can, instead of writing one rule that rewrites a big symbolic term into
another one, write a single symbolic term with multiple rewrite rules inside, and then the local rewrite rules happen
simoultaneously. This is technically implemented by a translation phase that generates the bigger rule that the user would have
to write not having this feature. Minuska does not support local rewrites; we belive it could be added in principle,
but so far we haven't seen the need for it.


