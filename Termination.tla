---------------------------- MODULE Termination ---------------------------

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

\* Bags are multi-sets.
EXTENDS Bags, Naturals, FiniteSets, TLC

\* P is the set of process indentifiers, d is the identifier of the termination daemon.
CONSTANTS P, d
\* Initially, there will a single message from pa to pb.
pa == CHOOSE p \in P : TRUE
pb == CHOOSE p \in P : p # pa

(*
--algorithm MessageDrivenTermination {
    variables
        \* the state of the network. Messages are of the form <<sender, destination>>
        msgs = SetToBag({<<pa,pb>>});
        \* s[p][q] is the number of messages sent from p to q
        s = [p \in P |-> [q \in P |-> IF <<p,q>> = <<pa,pb>> THEN 1 ELSE 0]];
        \* r[p][q] is the number of messages received by p from q
        r = [p \in P |-> [q \in P |-> 0]];
        \* The numbers recorded by the daemon:
        S = [p \in P |-> [q \in P |-> 0]];
        R = [p \in P |-> [q \in P |-> 0]];
        \* ghost variables:
        \* The largets set of nodes whose numbers match according to what the daemon saw:
        consistent = {};
        \* the set of nodes that the daemon has visited:
        visited = {};
        \* total number of messages ever sent. Used to stop the model-checker:
        total = 1;
    define {
        Consistent(Q, Sent, Rcvd) == \A q1,q2 \in Q : q1 # q2 => Sent[q1][q2] = Rcvd[q2][q1]
        Maximal(Qs) == CHOOSE Q \in Qs : \A Q2 \in Qs : Q # Q2 => \neg (Q \subseteq Q2)
        NotStarted == \A p,q \in P : S[p][q] = 0 /\ R[p][q] = 0
(***************************************************************************)
(*         The correctness condition:                                      *)
(***************************************************************************)
        Correctness == pc[d] = "Done" => msgs = EmptyBag  
(***************************************************************************)
(*         Candidate inductive invariant:                                  *)
(***************************************************************************)
        Inv1 == \A p \in P : <<p,p>> \notin BagToSet(msgs)
        Inv2 == pc[d] = "Done" => consistent = P
        Inv3 ==
            \/  \A p,q \in consistent : <<p,q>> \notin BagToSet(msgs)
            \/  \E p \in consistent, q \in P \ consistent : r[p][q] > R[p][q]
        Inv4 == \A p,q \in P : s[p][q] - r[q][p] = CopiesIn(<<p,q>>, msgs)
    }
    process (node \in P) {
        sendRcv:    with (m \in BagToSet(msgs)) {
                    when (m[2] = self);
                    r[self] := [r[self] EXCEPT ![m[1]] = @ + 1];
                    with (Q \in SUBSET (P \ {self})) {
                        msgs := (msgs (-) SetToBag({m})) (+) SetToBag({<<self,p>> : p \in Q});
                        s[self] := [p \in P |-> IF p \in Q THEN @[p]+1 ELSE @[p]];
                        total := total + Cardinality(Q) \* ghost update 
                    }
                };
                goto sendRcv
    }
    process (daemon = d) {
        loop:   while (NotStarted \/ visited # P \/ \E p,q \in visited : p # q /\ S[p][q] # R[q][p]) {
                    with (p \in P) {
                        S[p] := s[p]; 
                        R[p] := r[p];
                        visited := visited \union {p}  \* ghost update 
                    };
                    if (\E p,q \in P : S[p][q] # 0 \/ R[p][q] # 0)
                        consistent := Maximal({Q \in SUBSET visited : Consistent(Q, S, R)}) \* ghost update
                }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES msgs, s, r, S, R, consistent, visited, total, pc

(* define statement *)
Consistent(Q, Sent, Rcvd) == \A q1,q2 \in Q : q1 # q2 => Sent[q1][q2] = Rcvd[q2][q1]
Maximal(Qs) == CHOOSE Q \in Qs : \A Q2 \in Qs : Q # Q2 => \neg (Q \subseteq Q2)
NotStarted == \A p,q \in P : S[p][q] = 0 /\ R[p][q] = 0



Correctness == pc[d] = "Done" => msgs = EmptyBag



Inv1 == \A p \in P : <<p,p>> \notin BagToSet(msgs)
Inv2 == pc[d] = "Done" => consistent = P
Inv3 ==
    \/  \A p,q \in consistent : <<p,q>> \notin BagToSet(msgs)
    \/  \E p \in consistent, q \in P \ consistent : r[p][q] > R[p][q]
Inv4 == \A p,q \in P : s[p][q] - r[q][p] = CopiesIn(<<p,q>>, msgs)


vars == << msgs, s, r, S, R, consistent, visited, total, pc >>

ProcSet == (P) \cup {d}

Init == (* Global variables *)
        /\ msgs = SetToBag({<<pa,pb>>})
        /\ s = [p \in P |-> [q \in P |-> IF <<p,q>> = <<pa,pb>> THEN 1 ELSE 0]]
        /\ r = [p \in P |-> [q \in P |-> 0]]
        /\ S = [p \in P |-> [q \in P |-> 0]]
        /\ R = [p \in P |-> [q \in P |-> 0]]
        /\ consistent = {}
        /\ visited = {}
        /\ total = 1
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "sendRcv"
                                        [] self = d -> "loop"]

sendRcv(self) == /\ pc[self] = "sendRcv"
                 /\ \E m \in BagToSet(msgs):
                      /\ (m[2] = self)
                      /\ r' = [r EXCEPT ![self] = [r[self] EXCEPT ![m[1]] = @ + 1]]
                      /\ \E Q \in SUBSET (P \ {self}):
                           /\ msgs' = (msgs (-) SetToBag({m})) (+) SetToBag({<<self,p>> : p \in Q})
                           /\ s' = [s EXCEPT ![self] = [p \in P |-> IF p \in Q THEN @[p]+1 ELSE @[p]]]
                           /\ total' = total + Cardinality(Q)
                 /\ pc' = [pc EXCEPT ![self] = "sendRcv"]
                 /\ UNCHANGED << S, R, consistent, visited >>

node(self) == sendRcv(self)

loop == /\ pc[d] = "loop"
        /\ IF NotStarted \/ visited # P \/ \E p,q \in visited : p # q /\ S[p][q] # R[q][p]
              THEN /\ \E p \in P:
                        /\ S' = [S EXCEPT ![p] = s[p]]
                        /\ R' = [R EXCEPT ![p] = r[p]]
                        /\ visited' = (visited \union {p})
                   /\ IF \E p,q \in P : S'[p][q] # 0 \/ R'[p][q] # 0
                         THEN /\ consistent' = Maximal({Q \in SUBSET visited' : Consistent(Q, S', R')})
                         ELSE /\ TRUE
                              /\ UNCHANGED consistent
                   /\ pc' = [pc EXCEPT ![d] = "loop"]
              ELSE /\ pc' = [pc EXCEPT ![d] = "Done"]
                   /\ UNCHANGED << S, R, consistent, visited >>
        /\ UNCHANGED << msgs, s, r, total >>

daemon == loop

Next == daemon
           \/ (\E self \in P: node(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Mon Jul 09 11:17:35 PDT 2018 by nano
\* Created Mon Mar 13 09:03:31 PDT 2017 by nano
