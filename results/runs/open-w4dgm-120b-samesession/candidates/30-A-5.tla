---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposed, estimated, decided, crashed, sent, recv

vars == <<loc, view, proposed, estimated, decided, crashed, sent, recv>>
Phases == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choose"}
MsgTypes == {"p1", "p2"}
AllPhases == {"b1", "w1", "b2", "w2"}

RECURSIVE MaxV(_, _)
MaxV(f, S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE IN IF f[x] = Bottom THEN MaxV(f, S \ {x}) ELSE IF f[x] > MaxV(f, S \ {x}) THEN f[x] ELSE MaxV(f, S \ {x})

TypeOK ==
  /\ loc \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimated \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: MsgTypes, value: Values, sender: 1..N, estimate: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [i \in 1..N |-> "b1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimated = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

BroadcastP1(i) ==
  /\ loc[i] = "b1"
  /\ sent' = sent \cup {[type |-> "p1", value |-> proposed[i], sender |-> i, estimate |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, proposed, estimated, decided, crashed, recv>>

ReceiveP1(i) ==
  /\ loc[i] = "w1"
  /\ \E m \in sent :
       /\ m.type = "p1" /\ m.sender \notin recv[i]
       /\ view' = [view EXCEPT ![i][m.sender] = m.value]
       /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.sender}]
  /\ UNCHANGED <<loc, proposed, estimated, decided, crashed, sent>>

PrepareP2(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality(recv[i]) >= N - T
  /\ estimated' = [estimated EXCEPT ![i] = MaxV(view[i], 1..N)]
  /\ loc' = [loc EXCEPT ![i] = "b2"]
  /\ UNCHANGED <<view, proposed, decided, crashed, sent, recv>>

BroadcastP2(i) ==
  /\ loc[i] = "b2"
  /\ sent' = sent \cup {[type |-> "p2", value |-> proposed[i], sender |-> i, estimate |-> estimated[i]]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, proposed, estimated, decided, crashed, recv>>

ReceiveP2(i) ==
  /\ loc[i] = "w2"
  /\ \E m \in sent :
       /\ m.type = "p2" /\ m.sender \notin recv[i]
       /\ view' = [view EXCEPT ![i][m.sender] = m.estimate]
       /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.sender}]
  /\ UNCHANGED <<loc, proposed, estimated, decided, crashed, sent>>

DecideOnThreshold(i) ==
  /\ loc[i] = "w2"
  /\ \E v \in Values :
       /\ Cardinality({j \in recv[i] : view[i][j] = v}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimated, crashed, sent, recv>>

ChooseValue(i) ==
  /\ loc[i] = "w2"
  /\ recv[i] = 1..N
  /\ decided' = [decided EXCEPT ![i] = MaxV(view[i], 1..N)]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimated, crashed, sent, recv>>

Crash(i) ==
  /\ loc[i] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimated, decided, sent, recv>>

Next ==
  \/ \E i \in 1..N : BroadcastP1(i)
  \/ \E i \in 1..N : ReceiveP1(i)
  \/ \E i \in 1..N : PrepareP2(i)
  \/ \E i \in 1..N : BroadcastP2(i)
  \/ \E i \in 1..N : ReceiveP2(i)
  \/ \E i \in 1..N : DecideOnThreshold(i)
  \/ \E i \in 1..N : ChooseValue(i)
  \/ \E i \in 1..N : Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1..N : WF_vars(ReceiveP1(i))
  /\ \A i \in 1..N : WF_vars(PrepareP2(i))
  /\ \A i \in 1..N : WF_vars(ReceiveP2(i))
  /\ \A i \in 1..N : WF_vars(DecideOnThreshold(i))
  /\ \A i \in 1..N : WF_vars(ChooseValue(i))

Validity ==
  \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : proposed[j] = decided[i]

Agreement ==
  \A i \in 1..N, k \in 1..N : (decided[i] # Bottom /\ decided[k] # Bottom) => decided[i] = decided[k]

Termination ==
  \A i \in 1..N : (loc[i] \in {"crashed", "done"}) ~> (loc[i] \in {"crashed", "done"})

ConditionC1 == Cardinality({i \in 1..N : proposed[i] = MaxV(proposed, 1..N)}) >= F + 1
ConditionalTerminationC1 == ConditionC1 ~> Termination

====