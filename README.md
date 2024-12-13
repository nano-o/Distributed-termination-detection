# Distributed termination detection -- verified with Apalache, Isabelle/HOL, and TLAPS

We formalize and prove correct a simple distributed algorithm using an
inductive invariant. This is a proof pearl that is a great example of
inductive reasoning in distributed algorithms.

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

## Correctness proof with Apalache

The original proof is an operational proof that considers entire executions and
is thus hard to formalize (the principle is illustrated in Figure 8, Section 6,
of *Algorithms for distributed termination detection.*). Instead,
[`Termination.tla`](Termination.tla) shows that there is a very simple
inductive invariant that proves the correctness of the algorithm.

[`Termination.tla`](Termination.tla) contains both the specification of the
algorithm and an inductive invariant that proves its safety.
[`TerminationApalache.tla`](TerminationApalache.tla) fixes the number of
processes and adds type annotations for model-checking with Apalache, which is
able to prove that the invariants are inductive and that they imply the safety
property for up to 6 processes (on a 2022 desktop machine).

To check the proof with apalache, run `make verify`.

## Correctness proof with TLAPS

[`Termination_proof.tla`](Termination_proof.tla) contains an interactive proof
showing that the specification implies the invariants and the safety property,
for an arbitrary set of processes. The proof is checked by TLAPS, the TLA+ Proof
System, and it is very similar to the Isabelle proof described below.

## Correctness proof with Isabelle/HOL

We also prove the algorithm correct for any number of processes using
Isabelle/HOL. You can browse the proof at
[`Termination/browser_info/index.html`](https://htmlpreview.github.io/?https://raw.githubusercontent.com/nano-o/Distributed-termination-detection/master/Termination/browser_info/Termination.html).
The actual theory file (which must be opened using
[Isabelle](https://isabelle.in.tum.de/)) is
[`Termination/Termination.thy`](Termination/Termination.thy)

## PlusCal version of the specification

The PlusCal language allows writing specifications in a more procedural style than in TLA+, and it transpiles to TLA+.
[`TerminationPlusCal.tla`](TerminationPlusCal.tla) contains PlusCal version of the specification.
To transpile to TLA+, run `make transpile`. Note that this will modify the file in place.

## Typesetting

You can also produce PDF versions of the specifications using `make typeset`
