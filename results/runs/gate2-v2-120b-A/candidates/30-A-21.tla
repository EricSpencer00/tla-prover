---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT N          \* Number of processes
CONSTANT T          \* Maximum tolerated faults
CONSTANT F          \* Upper bound on actual faults
CONSTANT Values    \* Finite set of proposal values
CONSTANT Bottom    \* Special bottom value, not in Values

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Proc == 1..N

Phase1Msg == [type : "phase1",
              sender : Proc,
              value  : Values]

Phase2Msg == [type      : "phase2",
              sender    : Proc,
              propValue : Values,
              estValue  : Values]

Message == Phase1Msg \/ Phase2Msg

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    pc,            \* Control location of each process
    propVal,       \* Proposed value of each process
    localView,     \* N x N matrix of received values (or Bottom)
    est,           \* Estimated value after phase 1
    decision,      \* Decision value (or Bottom)
    crashedCount,  \* Number of crashed processes
    sent,          \* Set of all sent messages
    recv           \* Received messages per process

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
ControlLocs == {"broadcast1", "wait1", "broadcast2", "wait2",
                "choose", "done", "crashed"}

\* Initial state
Init ==
    /\ pc = [p \in Proc |-> "broadcast1"]
    /\ propVal = [p \in Proc |-> CHOOSE v \in Values : TRUE]
    /\ localView = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

BroadcastPhase1(p) ==
    /\ pc[p] = "broadcast1"
    /\ sent' = sent \cup { [type |-> "phase1",
                           sender |-> p,
                           value  |-> propVal[p]] }
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<propVal, localView, est, decision,
                    crashedCount, recv>>

ReceivePhase1(p) ==
    /\ pc[p] = "wait1"
    /\ \E m \in sent :
          /\ m.type = "phase1"
          /\ m.sender \notin recv[p]
          /\ localView' = [localView EXCEPT ![p][m.sender] = m.value]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, propVal, est, decision,
                    crashedCount, sent>>

Phase1ToPhase2(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({ m \in sent :
                     /\ m.type = "phase1"
                     /\ m.sender \in recv[p] }) >= N - T
    /\ est' = [est EXCEPT ![p] = 
                CHOOSE v \in Values :
                  \A q \in Proc : (localView[p][q] # Bottom) => 
                                   v >= localView[p][q]]
    /\ pc' = [pc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<propVal, localView, decision,
                    crashedCount, sent, recv>>

BroadcastPhase2(p) ==
    /\ pc[p] = "broadcast2"
    /\ est[p] # Bottom
    /\ sent' = sent \cup { [type      |-> "phase2",
                           sender    |-> p,
                           propValue |-> propVal[p],
                           estValue  |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<propVal, localView, est, decision,
                    crashedCount, recv>>

ReceivePhase2(p) ==
    /\ pc[p] = "wait2"
    /\ \E m \in sent :
          /\ m.type = "phase2"
          /\ m.sender \notin recv[p]
          /\ localView' = [localView EXCEPT ![p][m.sender] = m.estValue]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, propVal, est, decision,
                    crashedCount, sent>>

DecideIfThresholdMet(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
          /\ Cardinality({ m \in recv[p] :
                           /\ m.type = "phase2"
                           /\ m.estValue = v }) >= N - T
    /\ LET v == CHOOSE w \in Values :
               Cardinality({ m \in recv[p] :
                             /\ m.type = "phase2"
                             /\ m.estValue = w }) >= N - T
       IN
          /\ decision' = [decision EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<propVal, localView, est, crashedCount,
                    sent, recv>>

MoveToChoose(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({ m \in sent :
                     /\ m.type = "phase2"
                     /\ m.sender \in recv[p] }) = N
    /\ \A v \in Values :
          Cardinality({ m \in recv[p] :
                       /\ m.type = "phase2"
                       /\ m.estValue = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<propVal, localView, est, decision,
                    crashedCount, sent, recv>>

ChooseAndDecide(p) ==
    /\ pc[p] = "choose"
    /\ \E v \in Values :
          /\ \E q \in Proc :
               localView[p][q] = v
    /\ LET v == CHOOSE w \in Values :
               \E q \in Proc : localView[p][q] = w
       IN
          /\ decision' = [decision EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<propVal, localView, est, crashedCount,
                    sent, recv>>

Crash(p) ==
    /\ crashedCount < F
    /\ pc[p] # "crashed"
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<propVal, localView, est, decision,
                    sent, recv>>

Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc : ReceivePhase1(p)
    \/ \E p \in Proc : Phase1ToPhase2(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc : ReceivePhase2(p)
    \/ \E p \in Proc : DecideIfThresholdMet(p)
    \/ \E p \in Proc : MoveToChoose(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

Spec == Init /\ [][Next]_<<pc, propVal, localView, est,
                         decision, crashedCount, sent, recv>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> ControlLocs]
    /\ propVal \in [Proc -> Values]
    /\ localView \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
Validity ==
    \A p \in Proc :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

=============================================================================