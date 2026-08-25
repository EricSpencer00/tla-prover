---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Proc == 1..N

Locations == {"b1", "w1", "b2", "w2", "done", "crashed", "choosing"}

Message == [type : {"p1","p2"},
            value : Values,
            sender : Proc,
            est   : Values]   \* est = Bottom for phase‑1 messages

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc,               \* [Proc -> Locations]
          view,              \* [Proc -> [Proc -> Values]]
          prop,              \* [Proc -> Values]
          est,               \* [Proc -> Values]
          decision,          \* [Proc -> Values]
          crashedCount,      \* Nat
          sent,              \* SUBSET Message
          recvEstMap         \* [Proc -> [Values -> SUBSET Proc]]

vars == <<loc, view, prop, est, decision, crashedCount, sent, recvEstMap>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in Proc |-> "b1"]
    /\ prop \in [Proc -> Values]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recvEstMap = [p \in Proc |-> [v \in Values |-> {}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NonBottomVals(p) == { view[p][q] : q \in Proc /\ view[p][q] # Bottom }

ReceivedSenders(p) == UNION { recvEstMap[p][v] : v \in Values }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1 ==
    \E p \in Proc :
        /\ loc[p] = "b1"
        /\ loc' = [loc EXCEPT ![p] = "w1"]
        /\ sent' = sent \cup { [type |-> "p1",
                               value |-> prop[p],
                               sender |-> p,
                               est   |-> Bottom] }
        /\ UNCHANGED <<view, prop, est, decision, crashedCount, recvEstMap>>

ReceivePhase1 ==
    \E p \in Proc, m \in sent :
        /\ loc[p] = "w1"
        /\ m.type = "p1"
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ UNCHANGED <<loc, prop, est, decision, crashedCount, sent, recvEstMap>>

ComputeEst ==
    \E p \in Proc :
        /\ loc[p] = "w1"
        /\ Cardinality({ q \in Proc : view[p][q] # Bottom }) >= N - T
        /\ LET vals == NonBottomVals(p) IN
           /\ est' = [est EXCEPT ![p] = Max(vals)]
        /\ loc' = [loc EXCEPT ![p] = "b2"]
        /\ UNCHANGED <<view, prop, decision, crashedCount, sent, recvEstMap>>

BroadcastPhase2 ==
    \E p \in Proc :
        /\ loc[p] = "b2"
        /\ loc' = [loc EXCEPT ![p] = "w2"]
        /\ sent' = sent \cup { [type |-> "p2",
                               value |-> prop[p],
                               sender |-> p,
                               est   |-> est[p]] }
        /\ UNCHANGED <<view, prop, est, decision, crashedCount, recvEstMap>>

ReceivePhase2 ==
    \E p \in Proc, m \in sent :
        /\ loc[p] = "w2"
        /\ m.type = "p2"
        /\ recvEstMap' = [recvEstMap EXCEPT
                           ![p][m.est] = @ \cup { m.sender }]
        /\ UNCHANGED <<loc, view, prop, est, decision, crashedCount, sent>>

Decide ==
    \E p \in Proc, v \in Values :
        /\ loc[p] = "w2"
        /\ Cardinality(recvEstMap[p][v]) >= N - T
        /\ decision' = [decision EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
        /\ UNCHANGED <<view, prop, est, crashedCount, sent, recvEstMap>>

MoveToChoosing ==
    \E p \in Proc :
        /\ loc[p] = "w2"
        /\ (\A v \in Values : Cardinality(recvEstMap[p][v]) < N - T)
        /\ Cardinality(ReceivedSenders(p)) = N
        /\ loc' = [loc EXCEPT ![p] = "choosing"]
        /\ UNCHANGED <<view, prop, est, decision, crashedCount, sent, recvEstMap>>

Choose ==
    \E p \in Proc :
        /\ loc[p] = "choosing"
        /\ LET vals == NonBottomVals(p) IN
           /\ decision' = [decision EXCEPT ![p] = Max(vals)]
        /\ loc' = [loc EXCEPT ![p] = "done"]
        /\ UNCHANGED <<view, prop, est, crashedCount, sent, recvEstMap>>

Crash ==
    \E p \in Proc :
        /\ loc[p] # "crashed"
        /\ crashedCount < F
        /\ loc' = [loc EXCEPT ![p] = "crashed"]
        /\ crashedCount' = crashedCount + 1
        /\ UNCHANGED <<view, prop, est, decision, sent, recvEstMap>>

Next ==
    \/ BroadcastPhase1
    \/ ReceivePhase1
    \/ ComputeEst
    \/ BroadcastPhase2
    \/ ReceivePhase2
    \/ Decide
    \/ MoveToChoosing
    \/ Choose
    \/ Crash

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> Locations]
    /\ view \in [Proc -> [Proc -> Values]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values]
    /\ decision \in [Proc -> Values]
    /\ crashedCount \in Nat
    /\ crashedCount <= F
    /\ sent \subseteq Message
    /\ recvEstMap \in [Proc -> [Values -> SUBSET Proc]]
    /\ Bottom \notin Values

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        decision[p] # Bottom =>
            /\ decision[p] \in Values
            /\ \E q \in Proc : prop[q] = decision[p]

Agreement ==
    \A p, q \in Proc :
        (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
THEOREM SpecIsSpec == Spec
INVARIANT TypeOK
INVARIANT Validity
INVARIANT Agreement

====