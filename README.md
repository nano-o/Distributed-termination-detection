# Distributed termination detection -- verified with Apalache and Isabelle/HOL

Distributed termination detection of a message-driven computation.  A set of
processes exchange messages.  Initialy there are a few message in the network.
A process can receive a messages and send 0, 1, or more messages as a response
in a single atomic step.  A daemon visits arbitrary nodes one by one, each time
noting how many messages the node has sent to each other node, and how many it
has received from each other node.  When the daemon sees that all numbers
match, it declares that the system has terminated.

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

The original proof is an operational proof that considers entire executions and
is thus hard to formalize (the principle is illustrated in Figure 8, Section 6,
of *Algorithms for distributed termination detection.*). Instead,
[`Termination.tla`](Termination.tla) shows that there is a very simple
inductive invariant that proves the correctness of the algorithm. So this kind
of a proof pearl.

[`Termination.tla`](Termination.tla) contains both the specification of the
algorithm and an inductive invariant that proves its safety.

The specification is annotated for model-checking with Apalache, which is able
to prove all the invariants inductive for 6 processes.

By convention, an invariant of the form `Inv` (e.g. `Inv1`) is inductive
relative to `Inv_` (e.g. `Inv1_`). Moreover, the safety property is implied by
invariants the conjunction of invariants 1 and 2.

To check the whole proof, use `check_proof.sh` To check that e.g. `Inv1` is
inductive relative to `Inv1_` with Apalache, use `check_invariant Inv1
Termination.tla`

We also prove the algorithm correct for any number of processes using
Isabelle/HOL. You can browse the proof at
[`Termination/browser_info/index.html`](https://htmlpreview.github.io/?https://raw.githubusercontent.com/nano-o/Distributed-termination-detection/master/Termination/browser_info/Termination.html).
The actual theory file (which must be opened using
[Isabelle](https://isabelle.in.tum.de/)) is
[`Termination/Termination.thy`](Termination/Termination.thy)
