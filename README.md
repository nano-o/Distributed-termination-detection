# Distributed termination detection -- verified with Apalache

Distributed termination detection of a message-driven computation.  A set of
processes exchange messages.  Initialy there is one message in the network.  A
process can receive a messages and send 0, 1, or more messages as a response in
a single atomic step.  A daemon visits arbitrary nodes one by one, each time
noting how many messages the node has sent to each other node, and how many it
has received from each other node.  When the daemon sees that all numbers
match, it declares that the system has terminated.

This is the algorithm described in Section 4 of: Kumar, Devendra.  *A class of
termination detection algorithms for distributed computations.* International
Conference on Foundations of Software Technology and Theoretical Computer
Science.  Springer, Berlin, Heidelberg, 1985.

The algorithm can also be found in : Mattern, Friedemann. *Algorithms for
distributed termination detection.* Distributed computing 2.3 (1987): 161-175.
In this paper, the algorithm is called the Channel Counting Algorithm and is
described in Section 7.

The original, operational proof is a little mind-bending (the principle is
illustrated in Figure 8, Section 6, of *Algorithms for distributed termination
detection.*). Instead, `Termination.tla` shows that there is a relatively
simple inductive invariant that proves the correctness of the algorithm. So
this kind of a proof pearl.

`Termination.tla` contains both the specification of the algorithm and an
inductive invariant that proves safety.

The specification is annotated for model-checking with Apalache, which is able
to prove all the invariants inductive for 6 processes.

By convention, an invariant of the form `Inv` (e.g. `Inv1`) is inductive
relative to `Inv_` (e.g. `Inv1_`).  To check that `Inv1` is inductive
relative to `Inv1_` with Apalache, run:

```
$APALACHE_HOME/script/run-docker.sh check --init=Inv1_ --inv=Inv1 --length=1 --discard-disabled=false Termination.tla
```

The predicate `All` is the conjuction of all the invariants (including the main correctness property).
So, the fact that it's inductive proves that the main correctness property is an invariant of the protocol.
To check this with Apalache, run:

```
$APALACHE_HOME/script/run-docker.sh check --init=All --inv=All --length=1 --discard-disabled=false Termination.tla
```
