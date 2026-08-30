---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, value, estimate, decided, crashed, sent, recv

vars == <<loc, view, value, estimate, decided, crashed, sent, recv>>
Phases == {"ph1broadcast", "ph1wait", "prepare", "ph2broadcast", "ph2wait", "done", "crashed", "choosing"}
Types == {"ph1", "ph2"}
Msg == [type: Types, v: Values \cup {Bottom}, sender: 1..N, est: Values \cup {Bottom}]

\* Phase 1 collects values, phase 2 collects maximum estimates; the condition
\* is that enough proposals carry the maximum value for guaranteed termination.
MaxV(v) == \E x \in v : \A y \in v : y <= x /\ (\A y \in v : \E x \in v : y <= x)

TypeOK ==
  /\ loc \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ value \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msg
  /\ recv \in [1..N -> SUBSET Msg]

Init ==
  /\ loc = [i \in 1..N |-> "ph1broadcast"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ value \in [i \in 1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

BroadcastPh1(i) ==
  /\ loc[i] = "ph1broadcast"
  /\ sent' = sent \cup {[type |-> "ph1", v |-> value[i], sender |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "ph1wait"]
  /\ UNCHANGED <<view, value, estimate, decided, crashed, recv>>

\* A message is only applied if its type matches the phase being waited on.
Receive(i, m) ==
  /\ loc[i] \in {"ph1wait", "ph2wait"}
  /\ m \in sent
  /\ m \notin recv[i]
  /\ m.type = (IF loc[i] \in {"ph1wait"} THEN "ph1" ELSE "ph2")
  /\ view' = [view EXCEPT ![i][m.sender] = m.v]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<loc, value, estimate, decided, crashed, sent>>

Prepare(i) ==
  /\ loc[i] = "ph1wait"
  /\ Cardinality({m \in recv[i] : m.type = "ph1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE x \in Values :
                    \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= x]
  /\ loc' = "ph2broadcast"
  /\ UNCHANGED <<view, value, decided, crashed, sent, recv>>

BroadcastPh2(i) ==
  /\ loc[i] = "ph2broadcast"
  /\ sent' = sent \cup {[type |-> "ph2", v |-> value[i], sender |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "ph2wait"]
  /\ UNCHANGED <<view, value, estimate, decided, crashed, recv>>

Decide(i) ==
  /\ loc[i] = "ph2wait"
  /\ \E x \in Values :
        /\ Cardinality({m \in recv[i] : m.type = "ph2" /\ m.est = x}) >= N - T
        /\ decided' = [decided EXCEPT ![i] = x]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, value, estimate, crashed, sent, recv>>

Choose(i) ==
  /\ loc[i] = "ph2wait"
  /\ \A m \in recv[i] : m.type = "ph2"
  /\ Cardinality(recv[i]) = N
  /\ \E x \in Values :
        /\ \E j \in 1..N : view[i][j] = x
        /\ decided' = [decided EXCEPT ![i] = x]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, value, estimate, crashed, sent, recv>>

Crash(i) ==
  /\ loc[i] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, value, estimate, decided, sent, recv>>

Next ==
  \/ \E i \in 1..N : BroadcastPh1(i) \/ Prepare(i) \/ BroadcastPh2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in Msg : Receive(i, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in Msg : Receive(i, m))
  /\ WF_vars(\E i \in 1..N : Prepare(i))
  /\ WF_vars(\E i \in 1..N : Decide(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))

Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : decided[i] = value[j]
Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})

Conditional ==
  /\ (\E i \in 1..N : value[i] = MaxV({value[j] : j \in 1..N}))
  /\ Termination

====