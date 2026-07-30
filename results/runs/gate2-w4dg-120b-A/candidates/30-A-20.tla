---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

States == {"phase1broadcast", "phase1wait", "preparing", "phase2broadcast", "phase2wait", "done", "crashed", "choosing"}

MsgTypes == {"p1", "p2"}

VARIABLES loc, view, prop, est, dec, crashedCount, sent, rcvd

vars == <<loc, view, prop, est, dec, crashedCount, sent, rcvd>>

TypeOK ==
  /\ loc \in [1..N -> States]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ dec \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..N
  /\ sent \subseteq [type: MsgTypes, val: Values \cup {Bottom}, prop: Values, est: Values \cup {Bottom}, from: 1..N]
  /\ rcvd \in [1..N -> SUBSET [type: MsgTypes, val: Values \cup {Bottom}, prop: Values, est: Values \cup {Bottom}, from: 1..N]]

Init ==
  /\ loc = [i \in 1..N |-> "phase1broadcast"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop = [i \in 1..N |-> CHOOSE x \in Values : TRUE]
  /\ est = [i \in 1..N |-> Bottom]
  /\ dec = [i \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]

Broadcast1(i) ==
  /\ loc[i] = "phase1broadcast"
  /\ sent' = sent \cup {[type |-> "p1", val |-> prop[i], prop |-> prop[i], est |-> Bottom, from |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "phase1wait"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, rcvd>>

Receive1(i, m) ==
  /\ loc[i] = "phase1wait"
  /\ m \in sent
  /\ m.type = "p1"
  /\ view[i][m.from] = Bottom
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, sent>>

Estimate(i) ==
  /\ loc[i] = "phase1wait"
  /\ Cardinality({j \in 1..N : view[i][j] # Bottom}) >= N - T
  /\ est' = [est EXCEPT ![i] = CHOOSE v \in Values : \E j \in 1..N : view[i][j] = v /\ \A k \in 1..N : view[i][k] # Bottom => v >= view[i][k]]
  /\ loc' = [loc EXCEPT ![i] = "phase2broadcast"]
  /\ UNCHANGED <<view, prop, dec, crashedCount, sent, rcvd>>

Broadcast2(i) ==
  /\ loc[i] = "phase2broadcast"
  /\ sent' = sent \cup {[type |-> "p2", val |-> prop[i], prop |-> prop[i], est |-> est[i], from |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "phase2wait"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, rcvd>>

Receive2(i, m) ==
  /\ loc[i] = "phase2wait"
  /\ m \in sent
  /\ m.type = "p2"
  /\ view[i][m.from] = Bottom
  /\ view' = [view EXCEPT ![i][m.from] = m.est]
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, sent>>

Decide(i) ==
  /\ loc[i] = "phase2wait"
  /\ \E v \in Values : Cardinality({j \in 1..N : \E m \in rcvd[i] : m.type = "p2" /\ m.est = v}) >= N - T
  /\ \E v \in Values :
       /\ Cardinality({j \in 1..N : \E m \in rcvd[i] : m.type = "p2" /\ m.est = v}) >= N - T
       /\ dec' = [dec EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, rcvd>>

Choose(i) ==
  /\ loc[i] = "phase2wait"
  /\ \A m \in rcvd[i] : m.type = "p2"
  /\ Cardinality({j \in 1..N : view[i][j] # Bottom}) = N
  /\ \A v \in Values :
       Cardinality({j \in 1..N : \E m \in rcvd[i] : m.type = "p2" /\ m.est = v}) < N - T
  /\ \E v \in Values : (\E j \in 1..N : view[i][j] = v) /\ dec' = [dec EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, rcvd>>

Finish(i) ==
  /\ loc[i] = "choosing"
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, sent, rcvd>>

Crash(i) ==
  /\ loc[i] \notin {"crashed", "done"}
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, dec, sent, rcvd>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i)
  \/ \E i \in 1..N, m \in sent : Receive1(i, m)
  \/ \E i \in 1..N : Estimate(i)
  \/ \E i \in 1..N : Broadcast2(i)
  \/ \E i \in 1..N, m \in sent : Receive2(i, m)
  \/ \E i \in 1..N : Decide(i)
  \/ \E i \in 1..N : Choose(i)
  \/ \E i \in 1..N : Finish(i)
  \/ \E i \in 1..N : Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in sent : Receive1(i, m))
  /\ WF_vars(\E i \in 1..N, m \in sent : Receive2(i, m))
  /\ WF_vars(\E i \in 1..N : Estimate(i))
  /\ WF_vars(\E i \in 1..N : Decide(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))

Validity ==
  \A i \in 1..N : dec[i] # Bottom => \E j \in 1..N : prop[j] = dec[i]

Agreement ==
  \A i, j \in 1..N : (dec[i] # Bottom /\ dec[j] # Bottom) => (dec[i] = dec[j])

Terminate ==
  \A i \in 1..N : loc[i] \in {"done", "crashed"}

ConditionC1 ==
  LET MaxV == CHOOSE v \in Values : \A w \in Values : w <= v
  IN Cardinality({i \in 1..N : prop[i] = MaxV}) >= F + 1

====