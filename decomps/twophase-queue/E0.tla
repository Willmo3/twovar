--------------------------- MODULE E0 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES msgs, tmState, tmPrepared

vars == <<msgs,tmState,tmPrepared>>

RMs == {"rm1","rm2"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ msgs = <<>>
/\ tmState = "init"
/\ tmPrepared = {}

Dequeue == msgs' = SubSeq(msgs,2,Len(msgs))

SndPrepare(rm) ==
/\ msgs' = Append(msgs,[type |-> "Prepared",theRM |-> rm])
/\ UNCHANGED <<tmState,tmPrepared>>

RcvPrepare(rm) ==
/\ Len(msgs) > 0
/\ Head(msgs) = [type |-> "Prepared",theRM |-> rm]
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ Dequeue
/\ UNCHANGED <<tmState>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmPrepared = RMs
/\ msgs' = Append(msgs,[type |-> "Commit",theRM |-> rm])
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>

RcvCommit(rm) ==
/\ Len(msgs) > 0
/\ Head(msgs) = [type |-> "Commit",theRM |-> rm]
/\ Dequeue
/\ UNCHANGED <<tmState,tmPrepared>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ msgs' = Append(msgs,[type |-> "Abort",theRM |-> rm])
/\ UNCHANGED <<tmPrepared>>

RcvAbort(rm) ==
/\ Len(msgs) > 0
/\ Head(msgs) = [type |-> "Abort",theRM |-> rm]
/\ Dequeue
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
