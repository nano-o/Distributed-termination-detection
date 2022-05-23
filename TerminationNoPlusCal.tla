------------------------ MODULE TerminationNoPlusCal ------------------------
\* Bags are multi-sets.
EXTENDS Bags, Naturals, FiniteSets, Apalache, Sequences

\* @type: DAEMON;
d == "DAEMON_OF_DAEMON"
\* @type: Set(PROCESS);
P == {"P1_OF_PROCESS", "P2_OF_PROCESS", "P3_OF_PROCESS"}
\* @type: PROCESS;
pa == "P1_OF_PROCESS"
\* @type: PROCESS;
pb == "P2_OF_PROCESS"

VARIABLES
    \* @type: <<PROCESS, PROCESS>> -> Int;
    msgs,
    \* @type: PROCESS -> PROCESS -> Int;
    s,
    \* @type: PROCESS -> PROCESS -> Int;
    r,
    \* @type: PROCESS -> PROCESS -> Int;
    S,
    \* @type: PROCESS -> PROCESS -> Int;
    R,
    \* @type: Set(PROCESS);
    visited,
    \* @type: Bool;
    terminated

Consistent(Q) == \A q1,q2 \in Q : q1 # q2 => S[q1][q2] = R[q2][q1]
Maximal(Qs) == CHOOSE Q \in Qs : \A Q2 \in Qs : Q # Q2 => \neg (Q \subseteq Q2)
MaxConsistent == Maximal({Q \in SUBSET visited : Consistent(Q)})
Correctness == terminated => msgs = EmptyBag

\* @type: Set(<<PROCESS,PROCESS>>);
AllPairs == {<<p,q>> : p \in P, q \in P}

TypeOkay ==
  /\  msgs \in [AllPairs -> Int]

\* Candidate invariants
Inv1 == \A p \in P : <<p,p>> \notin BagToSet(msgs)
Inv2 == terminated => Consistent(P)
Inv3 ==
    \/  \A p,q \in MaxConsistent : <<p,q>> \notin BagToSet(msgs)
    \/  \E p \in MaxConsistent, q \in P \ MaxConsistent : r[p][q] > R[p][q]
Inv4 == \A p,q \in P : s[p][q] - r[q][p] = CopiesIn(<<p,q>>, msgs)

vars == << msgs, s, r, S, R, visited >>

Init ==
  /\ msgs = SetToBag({<<pa,pb>>})
  /\ s = [p \in P |-> [q \in P |->
             IF p = pa /\ q = pb THEN 1 ELSE 0]]
  /\ r = [p \in P |-> [q \in P |-> 0]]
  /\ S = [p \in P |-> [q \in P |-> 0]]
  /\ R = [p \in P |-> [q \in P |-> 0]]
  /\ visited = {}
  /\ terminated = FALSE

(***************************************************************************)
(* Receive a message and, in response, pick a set Q of processes and send  *)
(* one new message to each.                                                *)
(***************************************************************************)
process(self) == /\ \E m \in BagToSet(msgs):
                      /\ m[2] = self
                      /\ r' = [r EXCEPT ![self] = [r[self] EXCEPT ![m[1]] = @ + 1]]
                      /\ \E Q \in SUBSET (P \ {self}):
                           /\ msgs' = (msgs (-) SetToBag({m})) (+) SetToBag({<<self,p>> : p \in Q})
                           /\ s' = [s EXCEPT ![self] = [p \in P |-> IF p \in Q THEN @[p]+1 ELSE @[p]]]
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

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun May 22 20:34:07 PDT 2022 by nano
\* Created Sun May 22 18:34:58 PDT 2022 by nano
