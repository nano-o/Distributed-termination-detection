---------------------------- MODULE CounterExample ----------------------------

EXTENDS TerminationNoPlusCalPairs

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 ==
  R
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 2>> })
    /\ S
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 1>> })
    /\ debug = {}
    /\ msgs
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 1>> })
    /\ r
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 2>> })
    /\ s
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 2>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 2>> })
    /\ step = TRUE
    /\ terminated = FALSE
    /\ visited = { "P1_OF_P", "P3_OF_P" }

(* Transition 1 to State1 *)
State1 ==
  R
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 2>> })
    /\ S
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 2>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 1>> })
    /\ debug = { { "P1_OF_P", "P3_OF_P" }, {"P1_OF_P"}, {"P3_OF_P"}, {} }
    /\ msgs
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 1>> })
    /\ r
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 2>> })
    /\ s
      = SetAsFun({ <<<<"P1_OF_P", "P2_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 2>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 2>> })
    /\ step = TRUE
    /\ terminated = FALSE
    /\ visited = { "P1_OF_P", "P2_OF_P", "P3_OF_P" }
    /\ step = FALSE

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
(* Created by Apalache on Mon May 23 16:04:36 UTC 2022 *)
(* https://github.com/informalsystems/apalache *)
