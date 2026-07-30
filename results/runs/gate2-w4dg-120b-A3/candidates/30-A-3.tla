---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME N > 0
ASSUME Bottom \notin Values

Locations == {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choose"}

Msgs == [type : {"ph1", "ph2"}, val : Values \cup {Bottom},
         sender : 1 .. N, est : Values \cup {Bottom}]
Ph1Msgs == {m \in Msgs : m.type = "ph1"}
Ph2Msgs == {m \in Msgs : m.type = "ph2"}

VARIABLES loc, view, prop, est, decision, crashed, sent, rcvd

vars == <<loc, view, prop, est, decision, crashed, sent, rcvd>>

TypeOK ==
  /\ loc \in [1 .. N -> Locations]
  /\ view \in [1 .. N -> [1 .. N -> Values \cup {Bottom}]]
  /\ prop \in [1 .. N -> Values]
  /\ est \in [1 .. N -> Values \cup {Bottom}]
  /\ decision \in [1 .. N -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq Msgs
  /\ rcvd \in [1 .. N -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 1 .. N |-> "bc1"]
  /\ view = [p \in 1 .. N |-> [q \in 1 .. N |-> Bottom]]
  /\ prop \in [1 .. N -> Values]
  /\ est = [p \in 1 .. N |-> Bottom]
  /\ decision = [p \in 1 .. N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [p \in 1 .. N |-> {}]

BroadcastPh1 ==
  /\ \E p \in 1 .. N :
       /\ loc[p] = "bc1"
       /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[p],
                              sender |-> p, est |-> Bottom]}
       /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

ReceivePh1 ==
  /\ \E p \in 1 .. N :
       /\ loc[p] \in {"w1", "prep"}
       /\ \E m \in Ph1Msgs :
            /\ m NOT IN rcvd[p]
            /\ view' = [view EXCEPT ![p][m.sender] = m.val]
            /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

TransToPh2 ==
  /\ \E p \in 1 .. N :
       /\ loc[p] = "w1"
       /\ Cardinality({m \in rcvd[p] : m.type = "ph1"}) >= N - T
       /\ est' = [est EXCEPT ![p] = Max({view[p][q] : q \in 1 .. N})]
       /\ loc' = [loc EXCEPT ![p] = "bc2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, rcvd>>

BroadcastPh2 ==
  /\ \E p \in 1 .. N :
       /\ loc[p] = "bc2"
       /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[p],
                              sender |-> p, est |-> est[p]]}
       /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

ReceivePh2 ==
  /\ \E p \in 1 .. N :
       /\ loc[p] = "w2"
       /\ \E m \in Ph2Msgs :
            /\ m NOT IN rcvd[p]
            /\ view' = [view EXCEPT ![p][m.sender] = m.val]
            /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

Decide ==
  /\ \E p \in 1 .. N :
       /\ loc[p] = "w2"
       /\ Cardinality({m \in rcvd[p] : m.type = "ph2"
                         /\ m.est = est[p]}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = est[p]]
       /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

MoveToChoose ==
  /\ \E p \in 1 .. N :
       /\ loc[p] = "w2"
       /\ {m.sender : m \in rcvd[p]} = (1 .. N)
       /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, sent, rcvd>>

DetPick ==
  /\ \E p \in 1 .. N :
       /\ loc[p] = "choose"
       /\ decision[p] = Bottom
       /\ Cardinality({q \in 1 .. N : view[p][q] # Bottom}) > 0
       /\ decision' = [decision EXCEPT ![p] = CHOOSE view[p]]
       /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

Crash ==
  /\ \E p \in 1 .. N :
       /\ loc[p] # "crashed"
       /\ loc' = [loc EXCEPT ![p] = "crashed"]
       /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, rcvd>>

Next ==
  \/ BroadcastPh1
  \/ ReceivePh1
  \/ TransToPh2
  \/ BroadcastPh2
  \/ ReceivePh2
  \/ Decide
  \/ MoveToChoose
  \/ DetPick
  \/ Crash

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ReceivePh1)
  /\ WF_vars(ReceivePh2)
  /\ WF_vars(Decide)
  /\ WF_vars(DetPick)

Validity ==
  \A p \in 1 .. N : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 1 .. N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
  <>(\A p \in 1 .. N : loc[p] \in {"crashed", "done"})

ConditionC1 ==
  \A v \in Values : (\A p \in 1 .. N : prop[p] <= v /\ (v = Bottom => v \in Values))
      => \E p \in 1 .. N : prop[p] = v /\ v = Max(Values)

====