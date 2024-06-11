--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES tmState

vars == <<tmState>>

RMs == {"rm1","rm2"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ tmState = "init"

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"

Next ==
\E rm \in RMs :
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
=============================================================================
