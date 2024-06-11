------------------------------- MODULE TwoPhaseQueue ----------------------------- 

EXTENDS Sequences, Naturals, Integers

\* TMAborted: transaction manager specifies whether has aborted.
VARIABLES msgs, rmState, tmState, tmPrepared

vars == <<msgs, rmState, tmState, tmPrepared>>

RMs == {"rm1", "rm2"}

Message ==
  [type : {"Prepared"}, theRM : RMs]  
  \cup [type : {"Commit"}, theRM : RMs]
  \cup [type: {"Abort"}, theRM: RMs]

Init ==   
  /\ msgs = <<>>
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}

\* Queue operations
Dequeue ==
  msgs' = SubSeq(msgs, 2, Len(msgs))

\* Message passing
SndPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ msgs' = Append(msgs, [type |-> "Prepared", theRM |-> rm])
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

\* Allow prepare messages to be recieved even after the init state is passed.
\* This way, they are cleared from the queue.
RcvPrepare(rm) ==
  /\ Len(msgs) > 0
  /\ Head(msgs) = [type |-> "Prepared", theRM |-> rm] 
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ Dequeue
  /\ UNCHANGED <<tmState, rmState>>

\* If messages are enqueued / dequeued,
\* Then must send a commit message to each RM.
SndCommit(rm) ==
  /\ tmState \in {"init", "committed"}
  /\ tmPrepared = RMs
  /\ rmState[rm] /= "committed"
  /\ msgs' = Append(msgs, [type |-> "Commit", theRM |-> rm])
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvCommit(rm) ==
  /\ Len(msgs) > 0
  /\ Head(msgs) = [type |-> "Commit", theRM |-> rm]
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ Dequeue
  /\ UNCHANGED <<tmState, tmPrepared>>

SndAbort(rm) ==
  /\ tmState \in {"init", "aborted"}
  /\ rmState[rm] /= "aborted"
  /\ tmState' = "aborted"
  /\ msgs' = Append(msgs, [type |-> "Abort", theRM |-> rm])
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvAbort(rm) ==
  /\ Len(msgs) > 0
  /\ Head(msgs) = [type |-> "Abort", theRM |-> rm]
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ Dequeue
  /\ UNCHANGED <<tmState, tmPrepared>>
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

Next ==
    \E rm \in RMs :
        \/ SndPrepare(rm)
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit(rm)
        \/ SndAbort(rm)
        \/ RcvAbort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ msgs \in SUBSET Message
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs
  
Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")


=============================================================================
