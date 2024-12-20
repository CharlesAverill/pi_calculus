# Pi Calculus in Coq

A formalization of the Polyadic Pi Calculus in the Coq Interactive Theorem Prover.

I pull from a number of sources (none are amazing on their own for my purposes):

- https://inria.hal.science/inria-00072970/document
- https://link.springer.com/chapter/10.1007/3-540-44929-9_30
- https://hal-lara.archives-ouvertes.fr/hal-02101985/file/RR2003-13.pdf
- https://en.wikipedia.org/wiki/%CE%A0-calculus
- https://www.sciencedirect.com/science/article/pii/0890540192900084

## Progress

I have an operational semantics defined that allows me to show the evolution of simple processes as presented in [Milner's "The Polyadic pi-Calculus: A Tutorial"](http://www.lfcs.inf.ed.ac.uk/reports/91/ECS-LFCS-91-180/).
I have written some automation tactics to alleviate some of the complexities with writing these transition proofs manually.

[See examples here](./Examples.v)

## Structure

Build with `make`

- [`Processes.v`](./Processes.v) - Definitions and notations for pi calculus ASTs and substitution
- [`Congruence.v`](./Congruence.v) - Definitions, lemmas, and `Equivalence` instances for structural congruence of pi calculus ASTs
- [`Step.v`](./Step.v) - Definitions, lemmas, and `Equivalence` instances for both `step` and `multistep` relations over pi calculus ASTs
- [`Tactics.v`](./Tactics.v) - Tactic definitions for manipulating and solving congruence, step, and multistep goals
- [`Interface.v`](./Interface.v) - `Import` site for dependent projects
