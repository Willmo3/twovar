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

ErroneousPrepared(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState,tmPrepared>>

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState,tmPrepared>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit",theRM |-> rm]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>

RcvCommit(rm) ==
/\ ([type |-> "Commit",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs,tmState,tmPrepared>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort",theRM |-> rm]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>

RcvAbort(rm) ==
/\ ([type |-> "Abort",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs,tmState,tmPrepared>>

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
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
