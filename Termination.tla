---------------------------- MODULE Termination ----------------------------

EXTENDS Bags, Naturals, FiniteSets

CONSTANTS P, d
pa == CHOOSE p \in P : TRUE
pb == CHOOSE p \in P : p # pa

(*
--algorithm MessageDriven {
    variables 
        (* msgs \in {ms \in SubBag([m \in P\times P |-> MaxCopies]) : 
            \A p \in P : <<p,p>> \notin BagToSet(ms)}; *)
        msgs = SetToBag({<<pa,pb>>});
        s = [p \in P |-> [q \in P |-> IF <<p,q>> \in BagToSet(msgs) THEN CopiesIn(<<p,q>>, msgs) ELSE 0]];
        r = [p \in P |-> [q \in P |-> 0]];
        \* The numbers recorded by the daemon:
        S = [p \in P |-> [q \in P |-> 0]];
        R = [p \in P |-> [q \in P |-> 0]];
        \* The processor that the daemon visited:
        visited = {};
        \* ghost variable recording the total number of messages ever sent.
        \* Used to limit the model-checker.
        total = BagCardinality(msgs);
    define {
        Correctness == pc[d] = "Done" => msgs = EmptyBag 
        Inv1 == \A p \in P : <<p,p>> \notin BagToSet(msgs)
        Test == pc[d] = "l2" /\ \E p,q \in P : 
            visited = {p,q} /\ S[p][q] = 1 /\ R[q][p] = 1 /\ <<p,q>> \in BagToSet(msgs)
        Test2 == pc[d] = "l2" /\ \E p,q \in P :
            /\  visited = {p}
            /\  s[p][q] = 2
            /\  S[p][q] = 1
            /\  r[q][p] = 0
        Inv2 == pc[d] = "l2" => \A p,q \in visited : <<p,q>> \notin BagToSet(msgs)
        Inv3 == pc[d] = "l2" => 
            \/  \A p,q \in visited : <<p,q>> \notin BagToSet(msgs)
            \/  \E p \in visited, q \in P \ visited : r[p][q] > R[p][q]
        Inv4 == \A p,q \in P : s[p][q] - r[q][p] = CopiesIn(<<p,q>>, msgs)
    }
    process (proc \in P) {
        l1: with (m \in BagToSet(msgs)) {
                when (m[2] = self);
                r[self] := [r[self] EXCEPT ![m[1]] = @ + 1];
                with (Q \in SUBSET (P \ {self})) {
                    msgs := (msgs (-) SetToBag({m})) (+) SetToBag({<<self,p>> : p \in Q});
                    s[self] := [p \in P |-> IF p \in Q THEN @[p]+1 ELSE @[p]];
                    total := total + Cardinality(Q)
                }
            };
            goto l1
    }
    process (daemon = d) {
        l1: visited := {};
        l2: while (visited # P)
            with (p \in P \ visited) {
                S[p] := s[p]; 
                R[p] := r[p];
                visited := visited \union {p};
                if (\E p1,p2 \in visited : p1 # p2 /\ S[p1][p2] # R[p2][p1])
                    goto l1
            }
    }
}
*)
\* BEGIN TRANSLATION
\* Label l1 of process proc at line 42 col 18 changed to l1_
VARIABLES msgs, s, r, S, R, visited, total, pc

(* define statement *)
Correctness == pc[d] = "Done" => msgs = EmptyBag
Inv1 == \A p \in P : <<p,p>> \notin BagToSet(msgs)
Test == pc[d] = "l2" /\ \E p,q \in P :
    visited = {p,q} /\ S[p][q] = 1 /\ R[q][p] = 1 /\ <<p,q>> \in BagToSet(msgs)
Test2 == pc[d] = "l2" /\ \E p,q \in P :
    /\  visited = {p}
    /\  s[p][q] = 2
    /\  S[p][q] = 1
    /\  r[q][p] = 0
Inv2 == pc[d] = "l2" => \A p,q \in visited : <<p,q>> \notin BagToSet(msgs)
Inv3 == pc[d] = "l2" =>
    \/  \A p,q \in visited : <<p,q>> \notin BagToSet(msgs)
    \/  \E p \in visited, q \in P \ visited : r[p][q] > R[p][q]
Inv4 == \A p,q \in P : s[p][q] - r[q][p] = CopiesIn(<<p,q>>, msgs)


vars == << msgs, s, r, S, R, visited, total, pc >>

ProcSet == (P) \cup {d}

Init == (* Global variables *)
        /\ msgs = SetToBag({<<pa,pb>>})
        /\ s = [p \in P |-> [q \in P |-> IF <<p,q>> \in BagToSet(msgs) THEN CopiesIn(<<p,q>>, msgs) ELSE 0]]
        /\ r = [p \in P |-> [q \in P |-> 0]]
        /\ S = [p \in P |-> [q \in P |-> 0]]
        /\ R = [p \in P |-> [q \in P |-> 0]]
        /\ visited = {}
        /\ total = BagCardinality(msgs)
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "l1_"
                                        [] self = d -> "l1"]

l1_(self) == /\ pc[self] = "l1_"
             /\ \E m \in BagToSet(msgs):
                  /\ (m[2] = self)
                  /\ r' = [r EXCEPT ![self] = [r[self] EXCEPT ![m[1]] = @ + 1]]
                  /\ \E Q \in SUBSET (P \ {self}):
                       /\ msgs' = (msgs (-) SetToBag({m})) (+) SetToBag({<<self,p>> : p \in Q})
                       /\ s' = [s EXCEPT ![self] = [p \in P |-> IF p \in Q THEN @[p]+1 ELSE @[p]]]
                       /\ total' = total + Cardinality(Q)
             /\ pc' = [pc EXCEPT ![self] = "l1_"]
             /\ UNCHANGED << S, R, visited >>

proc(self) == l1_(self)

l1 == /\ pc[d] = "l1"
      /\ visited' = {}
      /\ pc' = [pc EXCEPT ![d] = "l2"]
      /\ UNCHANGED << msgs, s, r, S, R, total >>

l2 == /\ pc[d] = "l2"
      /\ IF visited # P
            THEN /\ \E p \in P \ visited:
                      /\ S' = [S EXCEPT ![p] = s[p]]
                      /\ R' = [R EXCEPT ![p] = r[p]]
                      /\ visited' = (visited \union {p})
                      /\ IF \E p1,p2 \in visited' : p1 # p2 /\ S'[p1][p2] # R'[p2][p1]
                            THEN /\ pc' = [pc EXCEPT ![d] = "l1"]
                            ELSE /\ pc' = [pc EXCEPT ![d] = "l2"]
            ELSE /\ pc' = [pc EXCEPT ![d] = "Done"]
                 /\ UNCHANGED << S, R, visited >>
      /\ UNCHANGED << msgs, s, r, total >>

daemon == l1 \/ l2

Next == daemon
           \/ (\E self \in P: proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Feb 28 16:07:16 PST 2018 by nano
\* Created Mon Mar 13 09:03:31 PDT 2017 by nano
