--------------------------- MODULE D1 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES msgs

vars == <<msgs>>

RMs == {"rm1","rm2","rm3"}

Message == (([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit"},theRM : RMs]) \cup [type : {"Abort"},theRM : RMs])

Init ==
/\ msgs = <<>>

Dequeue == msgs' = SubSeq(msgs,2,Len(msgs))

SndPrepare(rm) ==
/\ Len(msgs) < 3
/\ msgs' = Append(msgs,[type |-> "Prepared",theRM |-> rm])

RcvPrepare(rm) ==
/\ Len(msgs) > 0
/\ Head(msgs) = [type |-> "Prepared",theRM |-> rm]
/\ Dequeue

SndCommit(rm) ==
/\ Len(msgs) < 3
/\ msgs' = Append(msgs,[type |-> "Commit",theRM |-> rm])

RcvCommit(rm) ==
/\ Len(msgs) > 0
/\ Head(msgs) = [type |-> "Commit",theRM |-> rm]
/\ Dequeue

SndAbort(rm) ==
/\ Len(msgs) < 3
/\ msgs' = Append(msgs,[type |-> "Abort",theRM |-> rm])

RcvAbort(rm) ==
/\ Len(msgs) > 0
/\ Head(msgs) = [type |-> "Abort",theRM |-> rm]
/\ Dequeue

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
