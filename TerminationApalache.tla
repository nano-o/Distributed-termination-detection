------------------- MODULE TerminationApalache -------------------

P == {"P1_OF_P", "P2_OF_P", "P3_OF_P"}
\* P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P"}
\* P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P", "P5_OF_P"}

VARIABLES
    \* @type: <<P,P>> -> Int;
    s,
    \* @type: <<P,P>> -> Int;
    r,
    \* @type: <<P,P>> -> Int;
    ds,
    \* @type: <<P,P>> -> Int;
    dr,
    \* @type: Set(P);
    visited,
    \* @type: Bool;
    terminated

INSTANCE Termination

=============================================================================
\* Modification History
\* Last modified Wed Dec 14 11:01:29 PST 2022 by nano
\* Created Wed Dec 14 10:55:41 PST 2022 by nano
