--------------------------- MODULE C2 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES msgs

vars == <<msgs>>

RMs == {"rm1","rm2","rm3"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ msgs = {}

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ msgs' = (msgs \ {[type |-> "Prepared",theRM |-> rm]})

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit",theRM |-> rm]})

RcvCommit(rm) ==
/\ ([type |-> "Commit",theRM |-> rm] \in msgs)
/\ msgs' = (msgs \ {[type |-> "Commit",theRM |-> rm]})

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort",theRM |-> rm]})

RcvAbort(rm) ==
/\ ([type |-> "Abort",theRM |-> rm] \in msgs)
/\ msgs' = (msgs \ {[type |-> "Abort",theRM |-> rm]})

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))
=============================================================================
