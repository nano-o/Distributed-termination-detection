------------------------ MODULE Termination ------------------------

(***************************************************************************)
(* Distributed termination detection of a message-driven computation.  A   *)
(* set of processes exchange messages.  Initialy there is one message in   *)
(* the network.  A process can receive a messages and send 0, 1, or more   *)
(* messages as a response in a single atomic step.  A daemon visits        *)
(* arbitrary nodes one by one, each time noting how many messages the node *)
(* has sent to each other node, and how many it has received from each     *)
(* other node.  When the daemon sees that all numbers match, it declares   *)
(* that the system has terminated.                                         *)
(*                                                                         *)
(* This is the algorithm described in Section 4 of: Kumar, Devendra.  A    *)
(* class of termination detection algorithms for distributed computations. *)
(* International Conference on Foundations of Software Technology and      *)
(* Theoretical Computer Science.  Springer, Berlin, Heidelberg, 1985.      *)
(*                                                                         *)
(* The algorithm can also be found in : Mattern, Friedemann.  Algorithms   *)
(* for distributed termination detection.  Distributed computing 2.3       *)
(* (1987): 161-175.  In this paper, the algorithm is called the Channel    *)
(* Counting Algorithm and is described in Section 7.                       *)
(*                                                                         *)
(* The original, operational proof is a little mind-bending (the principle *)
(* is illustrated in Figure 8, Section 6, of Algorithms for distributed    *)
(* termination detection.).  Instead, `Termination.tla` shows that there   *)
(* is a relatively simple inductive invariant that proves the correctness  *)
(* of the algorithm.  So this kind of a proof pearl.                       *)
(*                                                                         *)
(* `Termination.tla` contains both the specification of the algorithm and  *)
(* an inductive invariant that proves safety.                              *)
(*                                                                         *)
(* The specification is annotated for model-checking with Apalache, which  *)
(* is able to prove all the invariants inductive for 5 processes.          *)
(*                                                                         *)
(* By convention, an invariant of the form `InvN` (e.g.  `Inv1`) is        *)
(* inductive relative to `InvN_` (e.g.  `Inv1_`).  So, to check that       *)
(* `Inv1_` is inductive with Apalache, run:                                *)
(*                                                                         *)
(*     $APALACHE_HOME/script/run-docker.sh check --init=Inv1_ --inv=Inv1 --length=1 Termination.tla *)
(*                                                                         *)
(* To check the main safety property, we check that the invariants imply   *)
(* it:                                                                     *)
(*                                                                         *)
(*     $APALACHE_HOME/script/run-docker.sh check --init=Safety_precondition --inv=Safety --length=0 Termination.tla *)
(*                                                                         *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Apalache, Sequences

\* @type: Set(P);
\* P == {"P1_OF_P"}
\* P == {"P1_OF_P", "P2_OF_P"}
\* P == {"P1_OF_P", "P2_OF_P", "P3_OF_P"}
P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P"}
\* NOTE: with 5 processes it takes around 1 minute on a powerful machine (powerful in 2022).
\* P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P", "P5_OF_P"}
\* NOTE: with 6 processes it takes around 25 minute on a powerful machine (powerful in 2022).
\* P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P", "P5_OF_P", "P6_OF_P"}

VARIABLES
    \* s[<<p,q>>] is the number of messages sent by p to q as counted by p:
    \* @type: <<P,P>> -> Int;
    s,
    \* r[<<p,q>>] is the number of messages received by p from q as counted by p
    \* @type: <<P,P>> -> Int;
    r,
    \* S[<<p,q>>] is the number of messages sent by p to q as recorded by the daemon in its last visit to p:
    \* @type: <<P,P>> -> Int;
    S,
    \* R[<<p,q>>] is the number of messages received by p from q as recorded by the daemon in its last visit to p:
    \* @type: <<P,P>> -> Int;
    R,
    \* visited is the set of processes that the daemon visited so far:
    \* @type: Set(P);
    visited,
    \* terminated is set to TRUE when the daemon terminates
    \* @type: Bool;
    terminated

\* The number of messages in flight from p to q:
\* @type: (<<P,P>>) => Int;
NumPending(pq) ==
  LET
    \* @type: P;
    p == pq[1]
    \* @type: P;
    q == pq[2]
  IN
    s[<<p,q>>] - r[<<q, p>>]

\* The correstness property: when the daemon terminates, there are no messages in flight (i.e. the distributed computation is finished):
Safety == terminated => \A p,q \in P : NumPending(<<p,q>>) = 0

TypeOkay ==
  /\  s \in [P\times P -> Int]
  /\  \A pq \in P\times P : s[pq] >= 0
  /\  r \in [P\times P -> Int]
  /\  \A pq \in P\times P : r[pq] >= 0
  /\  S \in [P\times P -> Int]
  /\  \A pq \in P\times P : S[pq] >= 0
  /\  R \in [P\times P -> Int]
  /\  \A pq \in P\times P : R[pq] >= 0
  /\  visited \in SUBSET P
  /\  terminated \in BOOLEAN

\* Initially, no messages have been received and the daemon has not started
\* visiting any nodes. However, there may be some messages in flight (otherwise
\* nothing happens).
Init ==
    /\ TypeOkay
    /\ r = [pq \in P\times P |-> 0]
    /\ S = [pq \in P\times P |-> 0]
    /\ R = [pq \in P\times P |-> 0]
    /\ visited = {}
    /\ terminated = FALSE

(***************************************************************************)
(* Receive a message and, in response, pick a set Q of processes and send  *)
(* one new message to each.                                                *)
(***************************************************************************)
process(self) ==
  /\ \E p \in P \ {self} :
      /\ NumPending(<<p,self>>) > 0
      /\ r' = [r EXCEPT ![<<self,p>>] =  @ + 1]
  /\ \E Q \in SUBSET (P \ {self}):
     /\ s' = [t \in P\times P |->
          IF t[1] = self /\ t[2] \in Q THEN s[t]+1 ELSE s[t]]
  /\ UNCHANGED << S, R, visited, terminated >>

(***************************************************************************)
(* While the daemon has not visited all processes, or it has but there is  *)
(* a pair whose message counts, as recorded by the daemon, do not match,   *)
(* visit a new process                                                     *)
(***************************************************************************)
daemon ==
        /\ \neg terminated
        /\ IF visited # P \/ \E p,q \in visited : S[<<p,q>>] # R[<<q,p>>]
              THEN /\ \E p \in P:
                        /\ S' = [t \in P\times P |-> IF t[1] = p THEN s[t] ELSE S[t]]
                        /\ R' = [t \in P\times P |-> IF t[1] = p THEN r[t] ELSE R[t]]
                        /\ visited' = (visited \union {p})
                        /\ UNCHANGED terminated
              ELSE /\ terminated' = TRUE
                   /\ UNCHANGED << S, R, visited >>
        /\ UNCHANGED << s, r >>

Next == daemon
           \/ (\E self \in P : process(self))

vars == << s, r, S, R, visited, terminated >>
Spec == Init /\ [][Next]_vars

\* Test invariants
Test1 == \neg terminated

\* To keep counter-examples small, if needed:
Bounds ==
  /\  \A pq \in P\times P : s[pq] <= 1
  /\  \A pq \in P\times P : r[pq] <= 1

\* Candidate invariants

\* Daemon receive counts are necessarily smaller than real receive counts:
Inv1 == \A p,q \in P :
  /\  R[<<p,q>>] <= r[<<p,q>>]
Inv1_ == TypeOkay /\ Inv1

\* A process cannot receive more than has been sent to it:
Inv2 == \A p,q \in P : r[<<p,q>>] <= s[<<q,p>>]
Inv2_ == TypeOkay /\ Inv2

Consistent(Q) ==
  /\ Q \subseteq visited
  /\ \A q1,q2 \in Q : S[<<q1,q2>>] = R[<<q2,q1>>]

\* If Q is consistent and a member of Q has received or sent more than what the daemon saw,
\* then a message from outside Q that the daemon has not seen has been received:
Inv3 == \A Q \in SUBSET visited :
  (Consistent(Q) /\ \E p \in Q, q \in P : (r[<<p,q>>] # R[<<p,q>>] \/ s[<<p,q>>] # S[<<p,q>>]))
  => \E p \in Q, q \in P \ Q : r[<<p,q>>] > R[<<p,q>>]
Inv3_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv3

Inv4 ==
  terminated => Consistent(P)
Inv4_ == TypeOkay /\ Inv4

\* Then we check that Inv3 and Inv4 imply Safety by using
\* Safety_precondition as init predicate and checking that Safety holds
\* in the initial state.
Safety_precondition == TypeOkay /\ Inv3 /\ Inv4

=============================================================================
\* Modification History
\* Last modified Sun Aug 21 21:44:31 PDT 2022 by nano
\* Created Sun May 22 18:34:58 PDT 2022 by nano
