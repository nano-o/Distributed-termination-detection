# Distributed termination detection -- verified with Apalache

Distributed termination detection of a message-driven computation.  A set of
processes exchange messages.  Initialy there is one message in the network.  A
process can receive a messages and send 0, 1, or more messages as a response in
a single atomic step.  A daemon visits arbitrary nodes one by one, each time
noting how many messages the node has sent to each other node, and how many it
has received from each other node.  When the daemon sees that all numbers
match, it declares that the system has terminated.

This is the Channel Counting Algorithm described in: Mattern, Friedemann.
*Algorithms for distributed termination detection.* Distributed computing 2.3
(1987): 161-175.  The first version of this algorithm seems to be found in:
Kumar, Devendra.  *A class of termination detection algorithms for distributed
computations.* International Conference on Foundations of Software Technology
and Theoretical Computer Science.  Springer, Berlin, Heidelberg, 1985.

The original proof is quite mind-bending, but `Termination.tla` shows that
there is a relatively simple inductive invariant that proves the correctness of
the algorithm. So this kind of a proof pearl.

`Termination.tla` contains both the specification of the algorithm and an
inductive invariant that proves safety.

The specification is annotated for model-checking with Apalache, which is able
to prove all the invariants inductive for 5 processes.

By convention, an invariant of the form `InvN` (e.g. `Inv1`) is inductive
relative to `InvN_` (e.g. `Inv1_`).  So, to check that `Inv1_` is inductive
with Apalache, run:

```
$APALACHE_HOME/script/run-docker.sh check --init=Inv1_ --inv=Inv1 --length=1 Termination.tla
```

To check the main correctness property:

```
$APALACHE_HOME/script/run-docker.sh check --init=Correctness_ --inv=Correctness --length=1 Termination.tla
```
