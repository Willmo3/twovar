--------------------------- MODULE C2 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES msgs

vars == <<msgs>>

RMs == {"rm1","rm2","rm3"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ msgs = {}

ErroneousPrepared(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit",theRM |-> rm]})

RcvCommit(rm) ==
/\ ([type |-> "Commit",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort",theRM |-> rm]})

RcvAbort(rm) ==
/\ ([type |-> "Abort",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)
\/ ErroneousPrepared(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))
=============================================================================
