---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types and auxiliary definitions
\* ----------------------------------------------------------------------
ProcSet == 1..N

Msg == [type : {"phase1", "phase2"},
        value: Values,
        sender: ProcSet,
        est: Values \cup {Bottom}]

Phase1Msgs(m) == m.type = "phase1"
Phase2Msgs(m) == m.type = "phase2"

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          prop,             \* proposed value of each process
          view,             \* N-by-N matrix of observed values
          est,              \* estimated value after phase 1
          decision,         \* decision value (Bottom if undecided)
          crashedCount,     \* number of crashed processes
          sent,             \* set of all sent messages
          recv               \* messages received by each process

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in ProcSet |-> "bcast1"]
    /\ prop \in [p \in ProcSet -> Values]
    /\ view = [p \in ProcSet, i \in ProcSet |-> Bottom]
    /\ est = [p \in ProcSet |-> Bottom]
    /\ decision = [p \in ProcSet |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in ProcSet |-> {}]

\* ----------------------------------------------------------------------
\* Helper actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
    /\ pc[p] = "bcast1"
    /\ LET m == [type |-> "phase1",
                 value |-> prop[p],
                 sender |-> p,
                 est |-> Bottom]
       IN
          /\ pc' = [pc EXCEPT ![p] = "wait1"]
          /\ sent' = sent \cup {m}
          /\ view' = [view EXCEPT ![p, p] = prop[p]]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
          /\ UNCHANGED <<prop, est, decision, crashedCount>>

Receive1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ Phase1Msgs(m)
    /\ \A mm \in recv[p] : mm.sender # m.sender   \* not received yet
    /\ view' = [view EXCEPT ![p, m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, decision, crashedCount, sent>>

CanEstimate(p) ==
    LET senders == { i \in ProcSet :
                     \E mm \in recv[p] : Phase1Msgs(mm) /\ mm.sender = i }
    IN Cardinality(senders) >= N - T

Estimate(p) ==
    /\ pc[p] = "wait1"
    /\ CanEstimate(p)
    /\ LET vals == { view[p,i] : i \in ProcSet /\ view[p,i] # Bottom }
       IN /\ est' = [est EXCEPT ![p] = Max(vals)]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<prop, view, decision, crashedCount, sent, recv>>

Broadcast2(p) ==
    /\ pc[p] = "bcast2"
    /\ LET m == [type |-> "phase2",
                 value |-> prop[p],
                 sender |-> p,
                 est |-> est[p]]
       IN
          /\ pc' = [pc EXCEPT ![p] = "wait2"]
          /\ sent' = sent \cup {m}
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
          /\ UNCHANGED <<prop, view, est, decision, crashedCount>>

Receive2(p, m) ==
    /\ pc[p] = "wait2"
    /\ m \in sent
    /\ Phase2Msgs(m)
    /\ \A mm \in recv[p] : mm.sender # m.sender   \* not received yet
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, view, est, decision, crashedCount, sent>>

Decide(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
          Cardinality({ m \in recv[p] :
                         Phase2Msgs(m) /\ m.est = v }) >= N - T
    /\ LET v == CHOOSE w \in Values :
                Cardinality({ m \in recv[p] :
                               Phase2Msgs(m) /\ m.est = w }) >= N - T
       IN
          /\ decision' = [decision EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, crashedCount, sent, recv>>

AllPhase2Received(p) ==
    \A i \in ProcSet :
        \E m \in recv[p] : Phase2Msgs(m) /\ m.sender = i

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ AllPhase2Received(p)
    /\ \A v \in Values :
           Cardinality({ m \in recv[p] :
                          Phase2Msgs(m) /\ m.est = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<prop, view, est, decision, crashedCount, sent, recv>>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ LET candidates == { view[p,i] : i \in ProcSet /\ view[p,i] # Bottom }
       IN /\ candidates # {}
    /\ decision' = [decision EXCEPT ![p] = CHOOSE candidates]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, crashedCount, sent, recv>>

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<prop, view, est, decision, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in ProcSet :
        \/ Broadcast1(p)
        \/ Broadcast2(p)
        \/ Crash(p)
        \/ \E m \in sent : Receive1(p,m)
        \/ \E m \in sent : Receive2(p,m)
        \/ Estimate(p)
        \/ Decide(p)
        \/ MoveToChoosing(p)
        \/ Choose(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<pc, prop, view, est, decision, crashedCount, sent, recv>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [p \in ProcSet -> {"bcast1","wait1","bcast2","wait2",
                                 "choosing","done","crashed"}]
    /\ prop \in [p \in ProcSet -> Values]
    /\ view \in [p \in ProcSet, i \in ProcSet -> Values \cup {Bottom}]
    /\ est \in [p \in ProcSet -> Values \cup {Bottom}]
    /\ decision \in [p \in ProcSet -> Values \cup {Bottom}]
    /\ crashedCount \in Nat
    /\ sent \subseteq Msg
    /\ recv \in [p \in ProcSet -> SUBSET Msg]
    /\ \A m \in sent :
          /\ m.type \in {"phase1","phase2"}
          /\ m.value \in Values
          /\ m.sender \in ProcSet
          /\ (m.type = "phase2" => m.est \in Values \cup {Bottom})
          /\ (m.type = "phase1" => m.est = Bottom)

Validity ==
    \A p \in ProcSet :
        decision[p] # Bottom => decision[p] \in { prop[i] : i \in ProcSet }

Agreement ==
    \A p,q \in ProcSet :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
\* The constants are declared above.
\* The specification is named Spec.
\* The invariants to be checked are TypeOK, Validity, Agreement.
=============================================================================