------------------------ MODULE TerminationNoPlusCalPairs ------------------------

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

\* @type: Set(P);
(* P == {"P1_OF_P", "P2_OF_P"} *)
P == {"P1_OF_P", "P2_OF_P", "P3_OF_P"}
\* @type: P;
pa == "P1_OF_P"
\* @type: P;
pb == "P2_OF_P"

VARIABLES
    \* number of messages in flight for each pair:
    \* NOTE we could eliminate this, as it's just s - r
    \* @type: <<P,P>> -> Int;
    msgs,
    \* s[p][q] is the number of messages sent by p to q as counted by p:
    \* @type: <<P,P>> -> Int;
    s,
    \* r[p][q] is the number of messages received by p from q as counted by p
    \* @type: <<P,P>> -> Int;
    r,
    \* S[p][q] is the number of messages sent by p to q as recorded by the daemon in its last visit to p:
    \* @type: <<P,P>> -> Int;
    S,
    \* R[p][q] is the number of messages received by p from q as recorded by the daemon in its last visit to p:
    \* @type: <<P,P>> -> Int;
    R,
    \* visited is the set of processes that the daemon visited so far:
    \* @type: Set(P);
    visited,
    \* terminated is set to TRUE when the daemon terminates
    \* @type: Bool;
    terminated,
    \* @type: Bool;
    step

\* The correstness property: when the daemon terminates, there are no messages in flight (i.e. the distributed computation is finished):
Correctness == terminated => \A p,q \in P : msgs[<<p,q>>] = 0

\* @type: Set(<<P,P>>);
AllPairs == {<<p,q>> : p \in P, q \in P}

Init ==
    /\ msgs = [pq \in AllPairs |->
        IF pq[1] = pa /\ pq[2] = pb THEN 1 ELSE 0]
    /\ s = msgs
    /\ r = [pq \in AllPairs |-> 0]
    /\ S = [pq \in AllPairs |-> 0]
    /\ R = [pq \in AllPairs |-> 0]
    /\ visited = {}
    /\ terminated = FALSE
    /\ step = FALSE

TypeOkay ==
  /\  msgs \in [AllPairs -> Int]
  /\  \A pq \in AllPairs : msgs[pq] >= 0
  /\  s \in [AllPairs -> Int]
  /\  \A pq \in AllPairs : s[pq] >= 0
  /\  r \in [AllPairs -> Int]
  /\  \A pq \in AllPairs : r[pq] >= 0
  /\  S \in [AllPairs -> Int]
  /\  \A pq \in AllPairs : S[pq] >= 0
  /\  R \in [AllPairs -> Int]
  /\  \A pq \in AllPairs : R[pq] >= 0
  /\  visited \in SUBSET P
  /\  terminated \in BOOLEAN
  /\  step \in BOOLEAN

(***************************************************************************)
(* Compute the new msgs corresponding to sending one message to each       *)
(* member of Q                                                             *)
(***************************************************************************)
\* @type: (Set(P), P, <<P,P>> -> Int) => <<P,P>> -> Int;
SendTo(Q, p, msgs_) ==
  LET
    \* @type: (<<P,P>> -> Int, P) => <<P,P>> -> Int;
    Send(msgs__, q) == [msgs__ EXCEPT ![<<p,q>>] = @+1]
  IN
    ApaFoldSet(Send, msgs_, Q)


(***************************************************************************)
(* Receive a message and, in response, pick a set Q of processes and send  *)
(* one new message to each.                                                *)
(***************************************************************************)
process(self) ==
  /\ \E p \in P \ {self} :
      /\ msgs[<<p,self>>] # 0
      /\ r' = [r EXCEPT ![<<self,p>>] =  @ + 1]
      /\ \E Q \in SUBSET (P \ {self}):
           /\ msgs' = [SendTo(Q, self, msgs) EXCEPT ![<<p,self>>] = @-1]
           /\ s' = SendTo(Q, self, s)
 /\ UNCHANGED << S, R, visited, terminated, step >>

\* @type: (P, <<P,P>> -> Int, <<P,P>> -> Int) => <<P,P>> -> Int;
UpdateCount(p, processCount, daemonCount) ==
  LET
    \* @type: (<<P,P>> -> Int, P) => <<P,P>> -> Int;
    Update(count_, q) == [count_ EXCEPT ![<<p,q>>] = processCount[<<p,q>>]]
  IN
    ApaFoldSet(Update, daemonCount, P)

Consistent(Q) ==
  /\ Q \subseteq visited
  /\ \A q1,q2 \in Q : S[<<q1,q2>>] = R[<<q2,q1>>]

(***************************************************************************)
(* While the daemon has not visited all processes, or it has but there is  *)
(* a pair whose message counts, as recorded by the daemon, do not match,   *)
(* visit a new process                                                     *)
(***************************************************************************)
daemon ==
        /\ \neg terminated
        /\ IF visited # P \/ \E p,q \in visited : p # q /\ S[<<p,q>>] # R[<<q,p>>]
              THEN /\ \E p \in P:
                        /\ S' = UpdateCount(p, s, S)
                        /\ R' = UpdateCount(p, r, R)
                        /\ visited' = (visited \union {p})
                        /\ UNCHANGED terminated
              ELSE /\ terminated' = TRUE
                   /\ UNCHANGED << S, R, visited >>
        /\ UNCHANGED << msgs, s, r, step >>

Next == daemon
           \/ (\E self \in P : process(self))


vars == << msgs, s, r, S, R, visited, terminated >>
Next_ == UNCHANGED vars /\ step' = TRUE
Spec == Init /\ [][Next]_vars

\* Test invariants
Test1 == \neg terminated

\* let's keep thing small:
Bounds ==
  /\  \A pq \in AllPairs : s[pq] <= 1
  /\  \A pq \in AllPairs : r[pq] <= 1

\* Candidate invariants
Inv1 == \A p \in P :
  /\  msgs[<<p,p>>] = 0
  /\  s[<<p,p>>] = 0 /\  r[<<p,p>>] = 0
  /\  R[<<p,p>>] = 0 /\  S[<<p,p>>] = 0
Inv1_ == TypeOkay /\ Inv1
Inv2 == \A p,q \in P : s[<<p, q>>] - r[<<q,p>>] = msgs[<<p,q>>]
Inv2_ == TypeOkay /\ Inv2
Inv3 == \A p \in P \ visited : \A q \in P : R[<<p,q>>] = 0 /\ S[<<p,q>>] = 0
Inv3_ == TypeOkay /\ Inv3
Inv4 == \A p \in visited : \A q \in P :
  /\  S[<<p,q>>] <= s[<<p,q>>]
  /\  R[<<p,q>>] <= r[<<p,q>>]
Inv4_ == TypeOkay /\ Inv4
\* @type: (P) => Int;
NumNewReceived(p) ==
  LET
    \* @type: (Int, P) => Int;
    Step(n, q) == n + r[<<p,q>>] - R[<<p,q>>]
  IN
    ApaFoldSet(Step, 0, P)
\* @type: (P) => Int;
MaxNewSent(p) ==
  LET
    \* @type: (Int, P) => Int;
    Step(n, q) ==
      LET newSent == s[<<p,q>>] - S[<<p,q>>]
      IN IF n >= newSent THEN n ELSE newSent
  IN
    ApaFoldSet(Step, 0, P)
Inv5 == \A p \in visited : MaxNewSent(p) <= NumNewReceived(p)
Inv5_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv5
\* TODO: generalize Inv5 to sets?

\* Now the main invariant

MainInv == visited # {} => \A Q \in SUBSET P : Consistent(Q) =>
    \/  \A p,q \in Q : msgs[<<p,q>>] = 0
    \/  \E p \in Q, q \in P \ Q : r[<<p,q>>] > R[<<p,q>>]
MainInv_ == TypeOkay /\ Bounds /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv5 /\ MainInv

\* Maximal(Qs) == CHOOSE Q \in Qs : \A Q2 \in Qs : Q # Q2 => \neg (Q \subseteq Q2)
\* MaxConsistent == Maximal({Q \in SUBSET visited : Consistent(Q)})

\* Inv ==
\*     \/  \A p,q \in MaxConsistent : msgs[<<p,q>>] = 0
\*     \/  \E p \in MaxConsistent, q \in P \ MaxConsistent : r[<<p,q>>] > R[<<p,q>>]
\* Inv_ == TypeOkay /\ Inv

=============================================================================
\* Modification History
\* Last modified Sun May 22 21:39:34 PDT 2022 by nano
\* Created Sun May 22 18:34:58 PDT 2022 by nano
