------------------------ MODULE Termination2 ------------------------

(***************************************************************************)
(* This is a version of Termination.tla that uses binary functions to      *)
(* represent the state of the algorithm (e.g.\ s[p][q]).  Although this    *)
(* looks better than using pairs, this will not work because of a bug in   *)
(* Apalache: https://github.com/informalsystems/apalache/issues/1801       *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Apalache, Sequences

\* @type: Set(P);
(* P == {"P1_OF_P", "P2_OF_P"} *)
P == {"P1_OF_P", "P2_OF_P", "P3_OF_P"}
(*P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P"}*)
(*P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P", "P5_OF_P"}*)
\* @type: P;
pa == "P1_OF_P"
\* @type: P;
pb == "P2_OF_P"

VARIABLES
    \* s[p][q] is the number of messages sent by p to q as counted by p:
    \* @type: P -> P -> Int;
    s,
    \* r[p][q] is the number of messages received by p from q as counted by p
    \* @type: P -> P -> Int;
    r,
    \* S[p,][q] is the number of messages sent by p to q as recorded by the daemon during its last visit to p:
    \* @type: P -> P -> Int;
    S,
    \* R[p][q] is the number of messages received by p from q as recorded by the daemon during its last visit to p:
    \* @type: P -> P -> Int;
    R,
    \* visited is the set of processes that the daemon visited so far:
    \* @type: Set(P);
    visited,
    \* terminated is set to TRUE when the daemon declares termination
    \* @type: Bool;
    terminated

\* The number of messages in flight from p to q:
\* @type: (P, P) => Int;
Msgs(p, q) == s[p][q] - r[q][p]

\* The correstness property: when the daemon terminates, there are no messages in flight (i.e. the distributed computation is finished):
Correctness == terminated => \A p,q \in P : Msgs(p,q) = 0

Init ==
    /\ s = [p \in P |-> [q \in P |->
        IF p = pa /\ q = pb THEN 1 ELSE 0]]
    /\ r = [p \in P |-> [q \in P |-> 0]]
    /\ S = [p \in P |-> [q \in P |-> 0]]
    /\ R = [p \in P |-> [q \in P |-> 0]]
    /\ visited = {}
    /\ terminated = FALSE

TypeOkay ==
  /\  s \in [P -> [P -> Int]]
  /\  r \in [P -> [P -> Int]]
  /\  S \in [P -> [P -> Int]]
  /\  R \in [P -> [P -> Int]]
  /\  visited \in SUBSET P
  /\  terminated \in BOOLEAN
  /\ \A p,q \in P :
      /\  s[p][q] >= 0
      /\  r[p][q] >= 0
      /\  S[p][q] >= 0
      /\  R[p][q] >= 0

(***************************************************************************)
(* Compute the new count corresponding to sending one message to each      *)
(* member of Q                                                             *)
(***************************************************************************)
\* @type: (Set(P), P) => P -> P -> Int;
SendToFrom(Q, p) ==
  LET
    \* @type: (P -> P -> Int, P) => P -> P -> Int;
    Send(s_, q) == [s_ EXCEPT ![p] = [@ EXCEPT ![q] = @+1]]
  IN
    ApaFoldSet(Send, s, Q)


(***************************************************************************)
(* Receive a message and, in response, pick a set Q of processes and send  *)
(* one new message to each.                                                *)
(***************************************************************************)
process(self) ==
  /\ \E p \in P \ {self} :
      /\ Msgs(p,self) > 0
      /\ r' = [r EXCEPT ![self] = [@ EXCEPT ![p] =  @ + 1]]
      /\ \E Q \in SUBSET (P \ {self}):
           /\ s' = SendToFrom(Q, self)
 /\ UNCHANGED << S, R, visited, terminated >>

\* @type: (P, P -> P -> Int, P -> P -> Int) => P -> P -> Int;
UpdateCount(p, processCount, daemonCount) ==
  LET
    \* @type: (P -> P -> Int, P) => P -> P -> Int;
    \* TODO: no need for the fold here, we can just set it to processCount[p]
    Update(count_, q) == [count_ EXCEPT ![p] = [@ EXCEPT ![q] = processCount[p][q]]]
  IN
    \* For each q in P, update the count
    ApaFoldSet(Update, daemonCount, P)

Consistent(Q) ==
  /\ Q \subseteq visited
  /\ \A q1,q2 \in Q : S[q1][q2] = R[q2][q1]

(***************************************************************************)
(* While the daemon has not visited all processes, or it has but there is  *)
(* a pair whose message counts, as recorded by the daemon, do not match,   *)
(* visit a new process                                                     *)
(***************************************************************************)
daemon ==
        /\ \neg terminated
        /\ IF visited # P \/ \E p,q \in visited : S[p][q] # R[q][p]
              THEN /\ \E p \in P:
                        /\ S' = UpdateCount(p, s, S)
                        /\ R' = UpdateCount(p, r, R)
                        /\ visited' = (visited \union {p})
                        /\ UNCHANGED terminated
              ELSE /\ terminated' = TRUE
                   /\ UNCHANGED << S, R, visited >>
        /\ UNCHANGED << s, r>>

Next == daemon
           \/ (\E self \in P : process(self))

vars == << s, r, S, R, visited, terminated >>
Spec == Init /\ [][Next]_vars

\* Canary invariants

Canary1 == \neg terminated

\* Candidate invariants

\* Daemon counts are zero for unvisited processes:
Inv1 == \A p \in P \ visited : \A q \in P : R[p][q] = 0 /\ S[p][q] = 0
Inv1_ == TypeOkay /\ Inv1

\* Daemon counts are necessarily smaller than real counts:
Inv2 == \A p,q \in P :
  /\  S[p][q] <= s[p][q]
  /\  R[p][q] <= r[p][q]
Inv2_ == TypeOkay /\ Inv2

\* A process cannot receive more than has been sent to it:
Inv3 == \A p,q \in P : r[p][q] <= s[q][p]
Inv3_ == TypeOkay /\ Inv3

\* To keep counter-examples small, if needed:
Bounds ==
  /\  \A p,q \in P : s[p][q] <= 1
  /\  \A p,q \in P : r[p][q] <= 1

\* If Q is consistent and a member of Q has received or sent more than what the daemon saw,
\* then a message from outside Q has been received:
Inv4 == \A Q \in SUBSET visited :
  (Consistent(Q) /\ \E p \in Q, q \in P : (r[p][q] > R[p][q] \/ s[p][q] > S[p][q]))
  => \E p \in Q, q \in P \ Q : r[p][q] > R[p][q]
Inv4_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4

Correctness_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Correctness

=============================================================================
\* Modification History
\* Last modified Sun Aug 21 21:02:43 PDT 2022 by nano
\* Created Sun May 22 18:34:58 PDT 2022 by nano
