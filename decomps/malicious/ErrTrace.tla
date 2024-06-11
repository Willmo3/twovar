---- MODULE ErrTrace ----

\* This TwoPhase includes a malicious entity that sabotages the environment by sending bad messages. 

EXTENDS Sequences, Naturals, Integers

VARIABLES msgs, rmState, tmState, tmPrepared

vars == <<msgs, rmState, tmState, tmPrepared>>

RMs == {"rm1", "rm2", "rm3"}

\* For consistency, adding extra type info to messages
Message ==
  [type : {"Prepared"}, theRM : RMs]  
  \cup [type : {"Commit"}, theRM: RMs]
  \cup [type: {"Abort"}, theRM: RMs]

Init ==   
  /\ msgs = {}
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}

\* Oh no! A prepared message is sent, apparently from an RM.
\* But it's really from another outside source.
\* Note: this can happen unlimited times. So we need a model checked version.
ErroneousPrepared(rm) ==
   /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
   /\ UNCHANGED <<tmState, tmPrepared, rmState>>

SndPrepare(rm) == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RcvPrepare(rm) ==
  /\ [type |-> "Prepared", theRM |-> rm] \in msgs
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<msgs, tmState, rmState>>

SndCommit(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Commit", theRM |-> rm]}
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvCommit(rm) ==
  /\ [type |-> "Commit", theRM |-> rm] \in msgs
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>

SndAbort(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Abort", theRM |-> rm]}
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvAbort(rm) ==
  /\ [type |-> "Abort", theRM |-> rm] \in msgs
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  
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
        \/ ErroneousPrepared(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ msgs \in SUBSET Message
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

VARIABLE errCounter
ErrInit ==
    /\ Init
    /\ errCounter = 0
ErrNext ==
    /\ Next
    /\ errCounter' = errCounter + 1
    /\ (errCounter = 0) => ErroneousPrepared("rm1")
    /\ (errCounter = 1) => RcvPrepare("rm1")
    /\ (errCounter = 2) => ErroneousPrepared("rm3")
    /\ (errCounter = 3) => RcvPrepare("rm3")
    /\ (errCounter = 4) => SndPrepare("rm2")
    /\ (errCounter = 5) => RcvPrepare("rm2")
    /\ (errCounter = 6) => SndCommit("rm1")
    /\ (errCounter = 7) => RcvCommit("rm1")
    /\ (errCounter = 8) => SilentAbort("rm3")
    /\ (errCounter = 9) => FALSE
ErrSpec == ErrInit /\ [][ErrNext]_vars
=============================================================================