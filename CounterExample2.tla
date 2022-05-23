---------------------------- MODULE CounterExample2 ----------------------------

EXTENDS TerminationNoPlusCalPairs

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 ==
  R
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ S
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ msgs
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ r
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ s
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ step = FALSE
    /\ terminated = FALSE
    /\ visited = { "P1_OF_P", "P2_OF_P", "P3_OF_P" }

(* Transition 1 to State1 *)
State1 ==
  R
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ S
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ msgs
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ r
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ s
      = SetAsFun({ <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>> })
    /\ step = FALSE
    /\ terminated = FALSE
    /\ visited = { "P1_OF_P", "P2_OF_P", "P3_OF_P" }

================================================================================
(* Created by Apalache on Mon May 23 19:43:16 UTC 2022 *)
(* https://github.com/informalsystems/apalache *)
