------------------------ MODULE TerminationNoPlusCal ------------------------

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
(* This is the Channel Counting Algorithm described in: Mattern,           *)
(* Friedemann.  "Algorithms for distributed termination detection."        *)
(* Distributed computing 2.3 (1987): 161-175.  The first version of this   *)
(* algorithm seems to be found in: Kumar, Devendra.  "A class of           *)
(* termination detection algorithms for distributed computations."         *)
(* International Conference on Foundations of Software Technology and      *)
(* Theoretical Computer Science.  Springer, Berlin, Heidelberg, 1985.      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Apalache, Sequences

\* @type: DAEMON;
d == "DAEMON_OF_DAEMON"
\* @type: Set(P);
P == {"P1_OF_P", "P2_OF_P", "P3_OF_P"}
\* @type: P;
pa == "P1_OF_P"
\* @type: P;
pb == "P2_OF_P"

VARIABLES
    \* number of messages in flight for each pair:
    \* @type: P -> P -> Int;
    msgs,
    \* s[p][q] is the number of messages sent by p to q as counted by p:
    \* @type: P -> P -> Int;
    s,
    \* r[p][q] is the number of messages received by p from q as counted by p
    \* @type: P -> P -> Int;
    r,
    \* S[p][q] is the number of messages sent by p to q as recorded by the daemon in its last visit to p:
    \* @type: P -> P -> Int;
    S,
    \* R[p][q] is the number of messages received by p from q as recorded by the daemon in its last visit to p:
    \* @type: P -> P -> Int;
    R,
    \* visited is the set of processes that the daemon visited so far:
    \* @type: Set(P);
    visited,
    \* terminated is set to TRUE when the daemon terminates
    \* @type: Bool;
    terminated

\* The correstness property: when the daemon terminates, there are no messages in flight (i.e. the distributed computation is finished):
Correctness == terminated => \A p,q \in P : msgs[p][q] = 0

Init ==
    /\ msgs = [p \in P |-> [q \in P |->
        IF p = pa /\ q = pb THEN 1 ELSE 0]]
    /\ s = msgs
    /\ r = [p \in P |-> [q \in P |-> 0]]
    /\ S = [p \in P |-> [q \in P |-> 0]]
    /\ R = [p \in P |-> [q \in P |-> 0]]
    /\ visited = {}
    /\ terminated = FALSE

TypeOkay ==
  /\  msgs \in [P -> [P -> Int]]
  /\  s \in [P -> [P -> Int]]
  /\  r \in [P -> [P -> Int]]
  /\  S \in [P -> [P -> Int]]
  /\  R \in [P -> [P -> Int]]
  /\  visited \in SUBSET P
  /\  terminated \in BOOLEAN

\* send one message to each member of Q
\* @type: (Set(P), P, P -> P -> Int) => P -> P -> Int;
SendTo(Q, p, msgs_) ==
  LET
    \* @type: (P -> P -> Int, P) => P -> P -> Int;
    Send(msgs__, q) == [msgs__ EXCEPT ![p] = [@ EXCEPT ![q] = @+1]]
  IN
    ApaFoldSet(Send, msgs_, Q)


(***************************************************************************)
(* Receive a message and, in response, pick a set Q of processes and send  *)
(* one new message to each.                                                *)
(***************************************************************************)
process(self) ==
  /\ \E p \in P \ {self} :
      /\ msgs[p][self] # 0
      /\ r' = [r EXCEPT ![self] = [r[self] EXCEPT ![p] = @ + 1]]
      /\ \E Q \in SUBSET (P \ {self}):
           /\ msgs' = [SendTo(Q, self, msgs) EXCEPT ![p] = [@ EXCEPT ![self] = @-1]]
           /\ s' = [s EXCEPT ![self] = [q \in P |-> IF q \in Q THEN @[q]+1 ELSE @[q]]]
 /\ UNCHANGED << S, R, visited, terminated >>

(***************************************************************************)
(* While the daemon has not visited all processes, or it has but there is  *)
(* a pair whose message counts did not match at the time of the visit,     *)
(* visit a new process                                                     *)
(***************************************************************************)
daemon ==
        /\ \neg terminated
        /\ IF visited # P \/ \E p,q \in visited : p # q /\ S[p][q] # R[q][p]
              THEN /\ \E p \in P:
                        /\ S' = [S EXCEPT ![p] = s[p]]
                        /\ R' = [R EXCEPT ![p] = r[p]]
                        /\ visited' = (visited \union {p})
                        /\ UNCHANGED terminated
              ELSE /\ terminated' = TRUE
                   /\ UNCHANGED << S, R, visited >>
        /\ UNCHANGED << msgs, s, r >>

Next == daemon
           \/ (\E self \in P : process(self))

vars == << msgs, s, r, S, R, visited >>
Spec == Init /\ [][Next]_vars

\* Test invariants
Test1 == \neg terminated

\* Candidate invariants
Inv1 == \A p \in P : msgs[p][p] = 0
Inv2 == \A p,q \in P : s[p][q] - r[q][p] = msgs[p][q]

\* Now the main invariant

Consistent(Q) == \A q1,q2 \in Q : q1 # q2 => S[q1][q2] = R[q2][q1]
Maximal(Qs) == CHOOSE Q \in Qs : \A Q2 \in Qs : Q # Q2 => \neg (Q \subseteq Q2)
MaxConsistent == Maximal({Q \in SUBSET visited : Consistent(Q)})

Inv3 ==
    \/  \A p,q \in MaxConsistent : msgs[p][q] = 0
    \/  \E p \in MaxConsistent, q \in P \ MaxConsistent : r[p][q] > R[p][q]

=============================================================================
\* Modification History
\* Last modified Sun May 22 21:23:23 PDT 2022 by nano
\* Created Sun May 22 18:34:58 PDT 2022 by nano
