--------------------------- MODULE E1 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES msgs, tmState

vars == <<msgs,tmState>>

RMs == {"rm1","rm2","rm3"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ msgs = {}
/\ tmState = "init"

ErroneousPrepared(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState>>

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ UNCHANGED <<msgs,tmState>>

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ msgs' = (msgs \cup {[type |-> "Commit",theRM |-> rm]})
/\ tmState' = "committed"

RcvCommit(rm) ==
/\ ([type |-> "Commit",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs,tmState>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ msgs' = (msgs \cup {[type |-> "Abort",theRM |-> rm]})
/\ tmState' = "aborted"

RcvAbort(rm) ==
/\ ([type |-> "Abort",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs,tmState>>

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
/\ (tmState \in {"init","committed","aborted"})
=============================================================================
