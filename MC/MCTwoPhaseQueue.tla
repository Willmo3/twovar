------------------------------- MODULE MCTwoPhaseQueue ----------------------------- 

EXTENDS Sequences, Naturals, Integers

\* TMAborted: transaction manager specifies whether has aborted.
VARIABLES msgs, rmState, tmState, tmPrepared, tmSentAbort, tmSentCommit

vars == <<msgs, rmState, tmState, tmPrepared, tmSentAbort, tmSentCommit>>

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
  /\ tmSentAbort = {}
  /\ tmSentCommit = {}

\* Queue operations
Dequeue ==
  msgs' = SubSeq(msgs, 2, Len(msgs))

\* Message passing
SndPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ msgs' = Append(msgs, [type |-> "Prepared", theRM |-> rm])
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared, tmSentAbort, tmSentCommit>>

\* Allow prepare messages to be recieved even after the init state is passed.
\* This way, they are cleared from the queue.
RcvPrepare(rm) ==
  /\ Len(msgs) > 0
  /\ Head(msgs) = [type |-> "Prepared", theRM |-> rm] 
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ Dequeue
  /\ UNCHANGED <<tmState, rmState, tmSentAbort, tmSentCommit>>

\* If messages are enqueued / dequeued,
\* Then must send a commit message to each RM.
SndCommit(rm) ==
  /\ tmState \in {"init", "committed"}
  /\ tmPrepared = RMs
  /\ ~(rm \in tmSentCommit)
  /\ msgs' = Append(msgs, [type |-> "Commit", theRM |-> rm])
  /\ tmState' = "committed"
  /\ tmSentCommit' = tmSentCommit \cup {rm}
  /\ UNCHANGED <<tmPrepared, rmState, tmSentAbort>>

RcvCommit(rm) ==
  /\ Len(msgs) > 0
  /\ Head(msgs) = [type |-> "Commit", theRM |-> rm]
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ Dequeue
  /\ UNCHANGED <<tmState, tmPrepared, tmSentAbort, tmSentCommit>>

SndAbort(rm) ==
  /\ tmState \in {"init", "aborted"}
  /\ ~(rm \in tmSentAbort)
  /\ tmState' = "aborted"
  /\ msgs' = Append(msgs, [type |-> "Abort", theRM |-> rm])
  /\ tmSentAbort' = tmSentAbort \cup {rm}
  /\ UNCHANGED <<tmPrepared, rmState, tmSentCommit>>

RcvAbort(rm) ==
  /\ Len(msgs) > 0
  /\ Head(msgs) = [type |-> "Abort", theRM |-> rm]
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ Dequeue
  /\ UNCHANGED <<tmState, tmPrepared, tmSentAbort, tmSentCommit>>
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, tmSentAbort, tmSentCommit>>

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
  /\ tmSentAbort \in SUBSET RMs
  /\ tmSentCommit \in SUBSET RMs

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")



=============================================================================
