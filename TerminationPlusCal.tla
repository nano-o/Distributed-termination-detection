---------------------------- MODULE TerminationPlusCal ---------------------------

(***************************************************************************)
(* A version of the specification in PlusCal.                              *)
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
        \* the set of nodes that the daemon has visited:
        visited = {};
        \* total number of messages ever sent. This is a ghost variable used to limit state-exploration by TLC:
        total = 1;
    define {
        Correctness == pc[d] = "Done" => msgs = EmptyBag
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
        loop:   while (visited # P \/ \E p,q \in visited : p # q /\ S[p][q] # R[q][p]) {
                    with (p \in P) {
                        S[p] := s[p]; 
                        R[p] := r[p];
                        visited := visited \union {p}
                    }
                }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "cea67973" /\ chksum(tla) = "cabff3a4")
VARIABLES pc, msgs, s, r, S, R, visited, total

(* define statement *)
Correctness == pc[d] = "Done" => msgs = EmptyBag


vars == << pc, msgs, s, r, S, R, visited, total >>

ProcSet == (P) \cup {d}

Init == (* Global variables *)
        /\ msgs = SetToBag({<<pa,pb>>})
        /\ s = [p \in P |-> [q \in P |-> IF <<p,q>> = <<pa,pb>> THEN 1 ELSE 0]]
        /\ r = [p \in P |-> [q \in P |-> 0]]
        /\ S = [p \in P |-> [q \in P |-> 0]]
        /\ R = [p \in P |-> [q \in P |-> 0]]
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
                 /\ UNCHANGED << S, R, visited >>

node(self) == sendRcv(self)

loop == /\ pc[d] = "loop"
        /\ IF visited # P \/ \E p,q \in visited : p # q /\ S[p][q] # R[q][p]
              THEN /\ \E p \in P:
                        /\ S' = [S EXCEPT ![p] = s[p]]
                        /\ R' = [R EXCEPT ![p] = r[p]]
                        /\ visited' = (visited \union {p})
                   /\ pc' = [pc EXCEPT ![d] = "loop"]
              ELSE /\ pc' = [pc EXCEPT ![d] = "Done"]
                   /\ UNCHANGED << S, R, visited >>
        /\ UNCHANGED << msgs, s, r, total >>

daemon == loop

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == daemon
           \/ (\E self \in P: node(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Canary1 == \neg pc[d] = "Done"


=============================================================================
