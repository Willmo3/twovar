--------------------------- MODULE T1 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES msgs, tmState, tmPrepared

vars == <<msgs,tmState,tmPrepared>>

RMs == {"rm1","rm2","rm3"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ msgs = {}
/\ tmState = "init"
/\ tmPrepared = {}

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState,tmPrepared>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ msgs' = (msgs \ {[type |-> "Prepared",theRM |-> rm]})
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ msgs' = (msgs \cup {[type |-> "Commit",theRM |-> rm]})
/\ UNCHANGED <<tmPrepared>>

RcvCommit(rm) ==
/\ ([type |-> "Commit",theRM |-> rm] \in msgs)
/\ msgs' = (msgs \ {[type |-> "Commit",theRM |-> rm]})
/\ UNCHANGED <<tmState,tmPrepared>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ msgs' = (msgs \cup {[type |-> "Abort",theRM |-> rm]})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>

RcvAbort(rm) ==
/\ ([type |-> "Abort",theRM |-> rm] \in msgs)
/\ msgs' = (msgs \ {[type |-> "Abort",theRM |-> rm]})
/\ UNCHANGED <<tmState,tmPrepared>>

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
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
