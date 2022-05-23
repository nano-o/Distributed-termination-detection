---------------------------- MODULE CounterExample ----------------------------

EXTENDS TerminationNoPlusCalPairs

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 ==
  R
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 4>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 2>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 3>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 5>> })
    /\ S
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 7>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 3>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 5>> })
    /\ msgs
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 4>> })
    /\ r
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 4>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 6>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 7>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 10>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 5>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 5>> })
    /\ s
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 8>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 10>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 4>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 6>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 5>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 9>> })
    /\ step = FALSE
    /\ terminated = FALSE
    /\ visited = { "P1_OF_P", "P2_OF_P", "P3_OF_P" }

(* Transition 1 to State1 *)
State1 ==
  R
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 4>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 7>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 3>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 5>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 5>> })
    /\ S
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 7>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 3>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 4>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 5>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 5>> })
    /\ msgs
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 4>> })
    /\ r
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 4>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 6>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 7>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 10>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 5>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 5>> })
    /\ s
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 8>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 10>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 4>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 6>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 5>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 9>> })
    /\ step = FALSE
    /\ terminated = FALSE
    /\ visited = { "P1_OF_P", "P2_OF_P", "P3_OF_P" }

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  ~(visited = {})
    /\ Skolem((\E Q_5 \in SUBSET ({ "P1_OF_P", "P2_OF_P", "P3_OF_P" }):
      ((\A t_s_1 \in Q_5: t_s_1 \in visited)
          /\ (\A q1_4 \in Q_5: \A q2_5 \in Q_5: S[q1_4, q2_5] = R[q2_5, q1_4]))
        /\ (Skolem((\E p_24 \in Q_5:
            Skolem((\E q_26 \in Q_5: ~(msgs[p_24, q_26] = 0)))))
          /\ (\A p_25 \in Q_5:
            \A q_27 \in {
              t_t_1 \in { "P1_OF_P", "P2_OF_P", "P3_OF_P" }:
                ~(t_t_1 \in Q_5)
            }:
              r[p_25, q_27] <= R[p_25, q_27]))))

================================================================================
(* Created by Apalache on Mon May 23 16:12:52 UTC 2022 *)
(* https://github.com/informalsystems/apalache *)
