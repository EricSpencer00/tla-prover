---- MODULE PaxosCommit ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* A simple (but fully typed) definition of the maximum of a set of
\* integers.  This function is used in Phase2a to decide which ballot
\* number the leader should use for the value it proposes.  The definition
\* is intentionally non-recursive to avoid any risk of infinite recursion
\* during model checking.
\* ----------------------------------------------------------------------
Maximum(S) == 
  IF S = {} THEN -1
  ELSE CHOOSE n \in S : \A m \in S : m <= n

\* ----------------------------------------------------------------------
\* CONSTANT DECLARATIONS
\* ----------------------------------------------------------------------
CONSTANT RM,             \* The set of resource managers.
          Acceptor,       \* The set of acceptors.
          Majority,       \* The set of majorities of acceptors
          Ballot          \* The set of ballot numbers

ASSUME
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}

\* ----------------------------------------------------------------------
\* MESSAGE DEFINITION
\* ----------------------------------------------------------------------
Message ==
  [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}] 
  \cup
  [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
   val : {"prepared", "aborted", "none"}, acc : Acceptor] 
  \cup
  [type : {"phase2a"}, ins : RM, bal : Ballot, val : {"prepared", "aborted"}]
  \cup
  [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,  
   val : {"prepared", "aborted"}] 
  \cup
  [type : {"Commit", "Abort"}]

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
  rmState,  \* $rmState[rm]$ is the state of resource manager $rm$.
  aState,   \* $aState[ins][ac]$ is the state of acceptor $ac$ for instance 
            \* $ins$ of the Paxos algorithm 
  msgs      \* The set of all messages ever sent.

\* ----------------------------------------------------------------------
\* TYPE-CORRECTNESS INVARIANT
\* ----------------------------------------------------------------------
PCTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState  \in [RM -> [Acceptor -> [mbal : Ballot,
                                      bal  : Ballot \cup {-1},
                                      val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \in SUBSET Message

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
PCInit ==  
  /\ rmState = [rm \in RM |-> "working"]
  /\ aState  = [ins \in RM |-> 
                 [ac \in Acceptor 
                    |-> [mbal |-> 0, bal  |-> -1, val  |-> "none"]]]
  /\ msgs = {}

\* ----------------------------------------------------------------------
\* SEND ACTION
\* ----------------------------------------------------------------------
Send(m) == msgs' = msgs \cup {m}

\* ----------------------------------------------------------------------
\* RM ACTIONS
\* ----------------------------------------------------------------------
RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> rm, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState

RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ Send([type |-> "phase2a", ins |-> rm, bal |-> 0, val |-> "aborted"])
  /\ UNCHANGED aState

RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<aState, msgs>>

RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<aState, msgs>>

\* ----------------------------------------------------------------------
\* LEADER ACTIONS
\* ----------------------------------------------------------------------
Phase1a(bal, rm) ==
  /\ Send([type |-> "phase1a", ins |-> rm, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, rm) ==
  /\ ~\E m \in msgs : /\ m.type = "phase2a"
                      /\ m.bal = bal
                      /\ m.ins = rm
  /\ \E MS \in Majority :    
        LET mset == {m \in msgs : /\ m.type = "phase1b"
                                  /\ m.ins  = rm
                                  /\ m.mbal = bal 
                                  /\ m.acc  \in MS}
            maxbal == Maximum({m.bal : m \in mset})
            val == IF maxbal = -1 
                     THEN "aborted"
                     ELSE (CHOOSE m \in mset : m.bal = maxbal).val
        IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
            /\ Send([type |-> "phase2a", ins |-> rm, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

Decide == 
  /\ LET Decided(rm, v) ==
           \E b \in Ballot, MS \in Majority : 
             \A ac \in MS : [type |-> "phase2b", ins |-> rm, 
                              bal |-> b, val |-> v, acc |-> ac ] \in msgs
     IN  \/ /\ \A rm \in RM : Decided(rm, "prepared")
            /\ Send([type |-> "Commit"])
         \/ /\ \E rm \in RM : Decided(rm, "aborted")
            /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>

\* ----------------------------------------------------------------------
\* ACCEPTOR ACTIONS
\* ----------------------------------------------------------------------
Phase1b(acc) ==  
  \E m \in msgs : 
    /\ m.type = "phase1a"
    /\ aState[m.ins][acc].mbal < m.bal
    /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal]
    /\ Send([type |-> "phase1b", 
             ins  |-> m.ins, 
             mbal |-> m.bal, 
             bal  |-> aState[m.ins][acc].bal, 
             val  |-> aState[m.ins][acc].val,
             acc  |-> acc])
    /\ UNCHANGED rmState

Phase2b(acc) == 
  /\ \E m \in msgs : 
       /\ m.type = "phase2a"
       /\ aState[m.ins][acc].mbal \leq m.bal
       /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                   ![m.ins][acc].bal  = m.bal,
                                   ![m.ins][acc].val  = m.val]
       /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal, 
                  val |-> m.val, acc |-> acc])
  /\ UNCHANGED rmState

\* ----------------------------------------------------------------------
\* NEXT-STATE ACTION
\* ----------------------------------------------------------------------
PCNext ==  
  \/ \E rm \in RM : \/ RMPrepare(rm) 
                    \/ RMChooseToAbort(rm) 
                    \/ RMRcvCommitMsg(rm) 
                    \/ RMRcvAbortMsg(rm)
  \/ \E bal \in Ballot \ {0}, rm \in RM : Phase1a(bal, rm) \/ Phase2a(bal, rm)
  \/ Decide
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc)

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
PCSpec == PCInit /\ [][PCNext]_<<rmState, aState, msgs>>

THEOREM PCSpec => PCTypeOK

\* ----------------------------------------------------------------------
\* INSTANCE OF TCommit
\* ----------------------------------------------------------------------
TC == INSTANCE TCommit

THEOREM PCSpec => TC!TCSpec
====