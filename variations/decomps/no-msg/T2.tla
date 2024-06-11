--------------------------- MODULE T2 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES tmPrepared

vars == <<tmPrepared>>

RMs == {"rm1","rm2","rm3","rm4","rm5","rm6","rm7","rm8","rm9"}

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
