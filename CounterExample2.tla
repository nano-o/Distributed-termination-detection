---------------------------- MODULE CounterExample2 ----------------------------

EXTENDS TerminationNoPlusCalPairs

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 ==
  R
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ S
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ msgs
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ r
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ s
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ step = FALSE
    /\ terminated = FALSE
    /\ visited = {"P1_OF_P"}

(* Transition 0 to State1 *)
State1 ==
  R
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ S
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ msgs
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 2>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ r
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ s
      = SetAsFun({ <<<<"P3_OF_P", "P2_OF_P">>, 1>>,
        <<<<"P1_OF_P", "P3_OF_P">>, 2>>,
        <<<<"P2_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P3_OF_P", "P1_OF_P">>, 1>>,
        <<<<"P2_OF_P", "P3_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P2_OF_P">>, 2>>,
        <<<<"P2_OF_P", "P2_OF_P">>, 0>>,
        <<<<"P1_OF_P", "P1_OF_P">>, 0>>,
        <<<<"P3_OF_P", "P3_OF_P">>, 0>> })
    /\ step = FALSE
    /\ terminated = FALSE
    /\ visited = {"P1_OF_P"}

================================================================================
(* Created by Apalache on Mon May 23 19:27:29 UTC 2022 *)
(* https://github.com/informalsystems/apalache *)
