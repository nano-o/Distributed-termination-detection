-------------------------- MODULE TerminationTyped --------------------------

\* @type: DAEMON;
d == "DAEMON_OF_DAEMON"
\* @type: Set(PROCESS);
P == {"P1_OF_PROCESS", "P2_OF_PROCESS"}
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

INSTANCE TerminationNoPlusCal

=============================================================================
\* Modification History
\* Last modified Sun May 22 18:44:24 PDT 2022 by nano
\* Created Sun May 22 17:30:18 PDT 2022 by nano
