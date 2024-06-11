--------------------------- MODULE T3 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES tmPrepared

vars == <<tmPrepared>>

RMs == {"rm1","rm2","rm3"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ tmPrepared = {}

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})

SndCommit(rm) ==
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
