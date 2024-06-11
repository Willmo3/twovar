--------------------------- MODULE E1 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES tmState, tmPrepared

vars == <<tmState,tmPrepared>>

RMs == {"rm1","rm2","rm3"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
