------------------------------- MODULE TwoPhaseNoMsg ----------------------------- 

\* Remove the messages set from this model.
\* Note: this will result in bad behavior BC no enabling conditions = random messages getting sent all the time.
EXTENDS Sequences, Naturals, Integers

VARIABLES rmState, tmState, tmPrepared

vars == <<rmState, tmState, tmPrepared>>

RMs == {"rm1", "rm2", "rm3", "rm4", "rm5", "rm6", "rm7", "rm8", "rm9"}

Init ==   
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}

SndPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RcvPrepare(rm) ==
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState, rmState>>

SndCommit(rm) ==
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvCommit(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared>>

SndAbort(rm) ==
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvAbort(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared>>
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared>>


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
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

=============================================================================
