---------------------------- MODULE Termination ---------------------------

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

=============================================================================
\* Modification History
\* Last modified Sun Aug 21 22:11:24 PDT 2022 by nano
\* Created Mon Mar 13 09:03:31 PDT 2017 by nano
