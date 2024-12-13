# Distributed termination detection -- an exercise in inductive reasoning

We formalize a simple distributed algorithm and we set up the Apalache
model-checker to facilitate searching for an inductive invariant that implies
the safety property of the algorithm. This is a great exercise in inductive
reasoning. The solution appears in the main branch, but you should try to
find it yourself. Note that you should have working knowledge of TLA+ to do the
exercise.

The algorithm detects the termination of a message-driven computation.  We
have a set of processes that exchange messages.  Initialy there is one message
in the network. A process can receive a messages and send 0, 1, or more
messages as a response, in a single atomic step.  A daemon visits arbitrary
processes one by one, each time noting how many messages the process has sent
to each other process, and how many it has received from each other process.
When the daemon sees that all numbers match, it declares that the system has
terminated.

What we want to prove is that the daemon is always right (i.e. if it declares
termination, then there are no more messges in flight).

This is the algorithm described in Section 4 of: Kumar, Devendra.  *A class of
termination detection algorithms for distributed computations.* International
Conference on Foundations of Software Technology and Theoretical Computer
Science.  Springer, Berlin, Heidelberg, 1985. This algorithm is also the
subject of: KM Chandy, J Misra. *Proofs of distributed algorithms: An
exercise.* Developments in concurrency and communication (1990), where the
author use UNITY to formally verify the algorithm.

The algorithm can also be found in : Mattern, Friedemann. *Algorithms for
distributed termination detection.* Distributed computing 2.3 (1987): 161-175.
In this paper, the algorithm is called the Channel Counting Algorithm and is
described in Section 7.

The algorithm is specified in [`Termination.tla`](Termination.tla).

## Exploring behaviors with the TLC model-checker

You can start by exploring a few behaviors to form some intuition.
To do that, think of a state predicate you want the behavior to end with, and create a "canary invariant" that asserts the negation of the predicate.
For example, run `make tlc` to check `Canary1`.
You can add new canaries and modify the Makefile accordingly.

## Searching for inductive invariants with Apalache

The original correctness proof is an operational proof that considers entire
executions and is thus hard to formalize (the principle is illustrated in
Figure 8, Section 6, of *Algorithms for distributed termination detection.*).
Instead we are going to look for an inductive invariant that proves the
correctness of the algorithm.

For now, `make verify` checks whether `TypeOK` is inductive (it is) and whether `Safety` is inductive relative to `TypeOK` (it is not).
The goal of the exercise is to strengthen `Safety` until it becomes inductive.

To help you find what to add to `Safety` to make it inductive, run `make verify` and then `./show_cti.sh`.
If `Safety` is not inductive, this will display the counterexample to induction found by Apalache.
You then need to strenghten `Safety` so as to rule out the pre-state.

You can change the number of processes for which Apalache checks the property
by editing [`ApaTermination.tla`](ApaTermination.tla).

## PlusCal version of the specification

The PlusCal language allows writing specifications in a more procedural style than in TLA+, and it transpiles to TLA+.
[`TerminationPlusCal.tla`](TerminationPlusCal.tla) contains PlusCal version of the specification.
It might be easier to read at first.

To transpile to TLA+, run `make transpile`. Note that this will modify the file in place.

## Typesetting

You can also produce PDF versions of the specifications using `make typeset`
