--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES rmState

vars == <<rmState>>

RMs == {"rm1","rm2"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ rmState = [rm \in RMs |-> "working"]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]

SndCommit(rm) ==
/\ rmState[rm] /= "committed"
/\ UNCHANGED <<rmState>>

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]

SndAbort(rm) ==
/\ rmState[rm] /= "aborted"
/\ UNCHANGED <<rmState>>

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
