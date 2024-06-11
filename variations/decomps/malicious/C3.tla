--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES tmState

vars == <<tmState>>

RMs == {"rm1","rm2","rm3"}

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ tmState = "init"

RcvPrepare(rm) ==
/\ tmState = "init"
/\ UNCHANGED <<tmState>>

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmState' = "committed"

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
=============================================================================
