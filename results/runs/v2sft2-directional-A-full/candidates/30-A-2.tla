---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC, TLCConfig

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
VARIABLES
    loc,              \* per-process control location
    view,             \* matrix of known values (N x N)
    est,              \* per-process estimated value
    decision,         \* per-process decision value
    crashed,          \* set of crashed processes
    sent,             \* set of all messages that have been sent
    recv              \* per-process set of received messages

\* ----------------------------------------------------------------------
\* Control locations (labels used in the specification)
\* ----------------------------------------------------------------------
BroadcastP1 == "BroadcastP1"
WaitingP1   == "WaitingP1"
BroadcastP2 == "BroadcastP2"
WaitingP2   == "WaitingP2"
Choosing    == "Choosing"
Done        == "Done"
Crashed     == "Crashed"

LocSet == {BroadcastP1, WaitingP1, BroadcastP2, WaitingP2,
           Choosing, Done, Crashed}

\* ----------------------------------------------------------------------
\* Message structure
\* ----------------------------------------------------------------------
Msg == [type : {"P1", "P2"},
        sender : [1..N],
        value : Values \cup {Bottom},
        estValue : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [1..N -> LocSet]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ est  \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in SUBSET 1..N
    /\ sent \in SUBSET Msg
    /\ recv \in [1..N -> SUBSET Msg]
    /\ \A i \in 1..N : loc[i] \in LocSet
    /\ \A i \in 1..N : view[i] \in [1..N -> Values \cup {Bottom}]
    /\ \A i \in 1..N : est[i] \in Values \cup {Bottom}
    /\ \A i \in 1..N : decision[i] \in Values \cup {Bottom}
    /\ sent \subseteq { [type |-> "P1", sender |-> j, value |-> v, estValue |-> Bottom] :
                      j \in 1..N /\ v \in Values
                  } \cup
                 { [type |-> "P2", sender |-> j, value |-> v, estValue |-> e] :
                      j \in 1..N /\ v \in Values /\ e \in Values }
    /\ recv \in [1..N -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [i \in 1..N |-> BroadcastP1]
    /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ est = [i \in 1..N |-> Bottom]
    /\ decision = [i \in 1..N |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [i \in 1..N |-> {}]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
Phase1Msg(i, v) == [type |-> "P1", sender |-> i, value |-> v, estValue |-> Bottom]
Phase2Msg(i, v, e) == [type |-> "P2", sender |-> i, value |-> v, estValue |-> e]

EnoughP1(i) ==
    \E j \in 1..N : (loc[j] = WaitingP1) /\ (\E m \in recv[i] : m.type = "P1" /\ m.sender = j)

EnoughP2(i) ==
    \E e \in Values :
        Cardinality({ j \in 1..N :
                      (\E m \in recv[i] : m.type = "P2" /\ m.sender = j /\ m.estValue = e) }) >= N - T

AllReceivedP2(i) ==
    Cardinality({ j \in 1..N : (\E m \in recv[i] : m.type = "P2" /\ m.sender = j) }) = N

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendP1(i) ==
    /\ loc[i] = BroadcastP1
    /\ \E v \in Values :
          /\ est[i] = Bottom
          /\ decision[i] = Bottom
          /\ \E m \in sent : m = Phase1Msg(i, v)
          /\ loc' = [loc EXCEPT ![i] = WaitingP1]
          /\ sent' = sent \cup { Phase1Msg(i, v) }
          /\ UNCHANGED << view, est, decision, crashed, recv >>

ReceiveP1(i) ==
    /\ loc[i] = WaitingP1
    /\ \E m \in sent :
          /\ m.type = "P1"
          /\ i \notin crashed
          /\ m.sender \notin crashed
          /\ m.sender \notin view[i][m.sender]
          /\ /\ view' = [view EXCEPT ![i][m.sender] = m.value]
             /\ recv' = [recv EXCEPT ![i] = recv[i] \cup { m }]
             /\ UNCHANGED << loc, est, decision, crashed, sent >>

EstP2(i) ==
    /\ loc[i] = WaitingP1
    /\ EnoughP1(i)
    /\ est' = [est EXCEPT ![i] = Max({ view[i][j] : j \in 1..N })]
    /\ loc' = [loc EXCEPT ![i] = BroadcastP2]
    /\ UNCHANGED << view, decision, crashed, sent, recv >>

SendP2(i) ==
    /\ loc[i] = BroadcastP2
    /\ \E e \in Values :
          /\ est[i] = e
          /\ \E m \in sent : m = Phase2Msg(i, est[i], e)
          /\ loc' = [loc EXCEPT ![i] = WaitingP2]
          /\ sent' = sent \cup { Phase2Msg(i, est[i], e) }
          /\ UNCHANGED << view, est, decision, crashed, recv >>

ReceiveP2(i) ==
    /\ loc[i] = WaitingP2
    /\ \E m \in sent :
          /\ m.type = "P2"
          /\ i \notin crashed
          /\ m.sender \notin crashed
          /\ m.sender \notin recv[i]
          /\ /\ recv' = [recv EXCEPT ![i] = recv[i] \cup { m }]
             /\ UNCHANGED << loc, view, est, decision, crashed, sent >>

DecideP2(i) ==
    /\ loc[i] = WaitingP2
    /\ \E e \in Values : EnoughP2(i)
    /\ decision' = [decision EXCEPT ![i] = e]
    /\ loc' = [loc EXCEPT ![i] = Done]
    /\ UNCHANGED << view, est, crashed, sent, recv >>

ChoosingState(i) ==
    /\ loc[i] = WaitingP2
    /\ \A e \in Values : \E m \in recv[i] : m.type = "P2" /\ m.estValue = e => False
    /\ loc' = [loc EXCEPT ![i] = Choosing]
    /\ UNCHANGED << view, est, decision, crashed, sent, recv >>

ChooseValue(i) ==
    /\ loc[i] = Choosing
    /\ \E v \in Values : \E j \in 1..N : view[i][j] = v
    /\ decision' = [decision EXCEPT ![i] = v]
    /\ loc' = [loc EXCEPT ![i] = Done]
    /\ UNCHANGED << view, est, crashed, sent, recv >>

Crash(i) ==
    /\ i \notin crashed
    /\ |\crashed| < F
    /\ loc' = [loc EXCEPT ![i] = Crashed]
    /\ crashed' = crashed \cup {i}
    /\ UNCHANGED << view, est, decision, sent, recv >>

\* ----------------------------------------------------------------------
\* NEXT action (weak fairness is assumed externally)
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in 1..N : SendP1(i)
    \/ \E i \in 1..N : ReceiveP1(i)
    \/ \E i \in 1..N : EstP2(i)
    \/ \E i \in 1..N : SendP2(i)
    \/ \E i \in 1..N : ReceiveP2(i)
    \/ \E i \in 1..N : DecideP2(i)
    \/ \E i \in 1..N : ChoosingState(i)
    \/ \E i \in 1..N : ChooseValue(i)
    \/ \E i \in 1..N : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, view, est, decision, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK == TypeOK

Validity ==
    /\ \A i \in 1..N :
          decision[i] = Bottom \/ IsUpperBound(decision[i])
    /\ (\A i \in 1..N : decision[i] \in Values)

Agreement ==
    \A i, j \in 1..N :
          decision[i] = Bottom \/ decision[j] = Bottom \/ decision[i] = decision[j]

\* ----------------------------------------------------------------------
\* Helper for validity (checks that decision value was proposed)
\* ----------------------------------------------------------------------
IsUpperBound(v) ==
    /\ v \in Values
    /\ \E i \in 1..N : /\ est[i] = v

====