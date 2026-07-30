---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 0 /\ 2 * T < N /\ F =< T

States == {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choose"}
MsgTypes == {"ph1", "ph2"}

VARIABLES loc, view, prop, est, decision, crashed, sent, rcvd

vars == <<loc, view, prop, est, decision, crashed, sent, rcvd>>

MsgSpace == [type: MsgTypes, c: Values, est: Values \cup {Bottom}, sender: 1..N]

RECURSIVE Maxv(_, _)
Maxv(f, S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE
       IN LET m == Maxv(f, S \ {x}) IN
            IF m = Bottom THEN f[x] ELSE IF f[x] > m THEN f[x] ELSE m

WellFormed(g) == \A A \in {g[i] : i \in 1..N} : TRUE

TypeOK ==
  /\ loc \in [1..N -> States]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ WellFormed(view)
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq MsgSpace
  /\ rcvd \in [1..N -> SUBSET MsgSpace]

Init ==
  /\ loc = [i \in 1..N |-> "bc1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]

Broadcast1(i) ==
  /\ loc[i] = "bc1"
  /\ sent' = sent \cup {[type |-> "ph1", c |-> prop[i], est |-> Bottom, sender |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

Receive1(i, m) ==
  /\ loc[i] \in {"w1", "prep"}
  /\ m \in rcvd[i]
  /\ m.type = "ph1"
  /\ view' = [view EXCEPT ![i][m.sender] = m.c]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent, rcvd>>

Transition1(i) ==
  /\ loc[i] \in {"w1", "prep"}
  /\ Cardinality({m.sender : m \in rcvd[i] /\ m.type = "ph1"}) >= N - T
  /\ est' = [est EXCEPT ![i] = Maxv(view[i], {j \in 1..N : view[i][j] # Bottom})]
  /\ loc' = [loc EXCEPT ![i] = "bc2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, rcvd>>

Broadcast2(i) ==
  /\ loc[i] = "bc2"
  /\ sent' = sent \cup {[type |-> "ph2", c |-> prop[i], est |-> est[i], sender |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

Receive2(i, m) ==
  /\ loc[i] \in {"w2", "choose"}
  /\ m \in rcvd[i]
  /\ m.type = "ph2"
  /\ view' = [view EXCEPT ![i][m.sender] = m.est]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent, rcvd>>

Decide(i, v) ==
  /\ loc[i] = "w2"
  /\ v \in {m.est : m \in rcvd[i] /\ m.type = "ph2" /\ Cardinality({m.sender : m \in rcvd[i] /\ m.type = "ph2" /\ m.est = v}) >= N - T}
  /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

Choose(i) ==
  /\ loc[i] = "choose"
  /\ \E v \in Values :
       /\ decision' = [decision EXCEPT ![i] = v]
       /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

Crash(i) ==
  /\ crashed < F
  /\ loc[i] \notin {"done", "crashed"}
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, rcvd>>

Arrive(i) ==
  /\ \E m \in MsgSpace : rcvd' = [rcvd EXCEPT ![i] = @ \cup {m}]

Next ==
  \/ \E i \in 1..N : Broadcast1(i) \/ Broadcast2(i) \/ Transition1(i) \/ Choose(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in MsgSpace : Receive1(i, m) \/ Receive2(i, m) \/ Decide(i, m.est)
  \/ \E i \in 1..N : Arrive(i)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 1..N : Receive1(i, CHOOSE m \in MsgSpace : m))
        /\ WF_vars(\E i \in 1..N : Broadcast1(i))
        /\ WF_vars(\E i \in 1..N : Transition1(i))
        /\ WF_vars(\E i \in 1..N : Receive2(i, CHOOSE m \in MsgSpace : m))
        /\ WF_vars(\E i \in 1..N : Broadcast2(i))
        /\ WF_vars(\E i \in 1..N : Choose(i))
        /\ WF_vars(\E i \in 1..N : Decide(i, CHOOSE v \in Values : v))

Validity ==
  \A i \in 1..N : (decision[i] # Bottom) => \E j \in 1..N : decision[i] = prop[j]

Agreement ==
  \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Terminate == \A i \in 1..N : loc[i] \in {"done", "crashed"}

ConditionC1 ==
  Cardinality({i \in 1..N : prop[i] = Maxv(prop, {j \in 1..N : TRUE})}) >= F + 1

ConditionalTermination == ConditionC1 => Terminate

====