------------------------------- MODULE TwoPhaseMsgRemoved ----------------------------- 

\* In this variant, items are removed from the messages set
\* This works!
EXTENDS Sequences, Naturals, Integers

VARIABLES msgs, rmState, tmState, tmPrepared

vars == <<msgs, rmState, tmState, tmPrepared>>

RMs == {"rm1", "rm2", "rm3"}

Message ==
  [type : {"Prepared"}, theRM : RMs]  
  \cup [type : {"Commit"}, theRM: RMs]
  \cup [type: {"Abort"}, theRM: RMs]

Init ==   
  /\ msgs = {}
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}

SndPrepare(rm) == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RcvPrepare(rm) ==
  /\ [type |-> "Prepared", theRM |-> rm] \in msgs
  /\ tmState = "init"
  /\ msgs' = msgs \ {[type |-> "Prepared", theRM |-> rm]}
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState, rmState>>

\* Adding extra prereq that rmState is not committed to be consistent with queue impl.
SndCommit(rm) ==
  /\ tmState \in {"init", "committed"}
  /\ tmPrepared = RMs
  /\ rmState[rm] /= "committed"
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit", theRM |-> rm]}
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvCommit(rm) ==
  /\ [type |-> "Commit", theRM |-> rm] \in msgs
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ msgs' = msgs \ {[type |-> "Commit", theRM |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>

\* Adding extra prereq that rmState is not aborted when abort message sent
\* To be consistent with queue impl.
SndAbort(rm) ==
  /\ tmState \in {"init", "aborted"}
  /\ rmState[rm] /= "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort", theRM |-> rm]}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvAbort(rm) ==
  /\ [type |-> "Abort", theRM |-> rm] \in msgs
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ msgs' = msgs \ {[type |-> "Abort", theRM |-> rm]}
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
