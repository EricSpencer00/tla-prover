---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES pc, view, proposal, est, decided, crashedCount, sent, recv

vars == <<pc, view, proposal, est, decided, crashedCount, sent, recv>>

MsgId == CHOOSE(N, "msg")
Phases == {"p1", "p2"}
MaxV == CHOOSE v \in Values : \A w \in Values : w <= v

TypeOK ==
  /\ pc \in [1..N -> {"broadcast1", "waiting1", "preparing", "broadcast2", "waiting2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..F
  /\ sent \subseteq [id: MsgId, typ: Phases, val: Values \cup {Bottom}, snd: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET MsgId]

Init ==
  /\ pc = [i \in 1..N |-> "broadcast1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ est = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

Broadcast1(i) ==
  /\ pc[i] = "broadcast1"
  /\ pc' = [pc EXCEPT ![i] = "waiting1"]
  /\ sent' = sent \cup {[id |-> CHOOSE m \in MsgId : m \notin sent], typ |-> "p1", val |-> proposal[i], snd |-> i, est |-> Bottom]
  /\ UNCHANGED <<view, proposal, est, decided, crashedCount, recv>>

Recv1(i, m) ==
  /\ pc[i] = "waiting1"
  /\ [id |-> m, typ |-> "p1", val |-> proposal[i], snd |-> i, est |-> Bottom] \in sent
  /\ m \notin recv[i]
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<pc, proposal, est, decided, crashedCount, sent>>

Estimate(i) ==
  /\ pc[i] = "waiting1"
  /\ Cardinality({m \in recv[i] : m.typ = "p1"}) >= N - T
  /\ est' = [est EXCEPT ![i] = CHOOSE w \in Values : \A k \in 1..N : view[i][k] # Bottom => w >= view[i][k]]
  /\ pc' = [pc EXCEPT ![i] = "broadcast2"]
  /\ UNCHANGED <<view, proposal, decided, crashedCount, sent, recv>>

Broadcast2(i) ==
  /\ pc[i] = "broadcast2"
  /\ pc' = [pc EXCEPT ![i] = "waiting2"]
  /\ sent' = sent \cup {[id |-> CHOOSE m \in MsgId : m \notin sent], typ |-> "p2", val |-> proposal[i], snd |-> i, est |-> est[i]}
  /\ UNCHANGED <<view, proposal, est, decided, crashedCount, recv>>

Recv2(i, m) ==
  /\ pc[i] = "waiting2"
  /\ [id |-> m, typ |-> "p2", val |-> proposal[i], snd |-> i, est |-> est[i]] \in sent
  /\ m \notin recv[i]
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<pc, proposal, est, decided, crashedCount, sent>>

Decide(i) ==
  /\ pc[i] = "waiting2"
  /\ \E w \in Values :
       /\ Cardinality({m \in recv[i] : m.typ = "p2" /\ m.est = w}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = w]
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, est, crashedCount, sent, recv>>

Choose(i) ==
  /\ pc[i] = "waiting2"
  /\ \A w \in Values : Cardinality({m \in recv[i] : m.typ = "p2" /\ m.est = w}) < N - T
  /\ pc' = [pc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, proposal, est, decided, crashedCount, sent, recv>>

Select(i) ==
  /\ pc[i] = "choosing"
  /\ \E w \in Values :
       /\ w \in {view[i][k] : k \in 1..N}
       /\ decided' = [decided EXCEPT ![i] = w]
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, est, crashedCount, sent, recv>>

Crash(i) ==
  /\ pc[i] \notin {"crashed", "done"}
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![i] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, proposal, est, decided, sent, recv>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i) \/ Estimate(i) \/ Broadcast2(i) \/ Decide(i) \/ Choose(i) \/ Select(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in MsgId : Recv1(i, m) \/ Recv2(i, m)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N : Broadcast1(i))
  /\ WF_vars(\E i \in 1..N, m \in MsgId : Recv1(i, m))
  /\ WF_vars(\E i \in 1..N : Estimate(i))
  /\ WF_vars(\E i \in 1..N : Broadcast2(i))
  /\ WF_vars(\E i \in 1..N, m \in MsgId : Recv2(i, m))
  /\ WF_vars(\E i \in 1..N : Decide(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))
  /\ WF_vars(\E i \in 1..N : Select(i))

Validity ==
  \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : decided[i] = proposal[j]

Agreement ==
  \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Terminate ==
  <>(\A i \in 1..N : pc[i] \in {"done", "crashed"})

ConditionC1 ==
  (Cardinality({i \in 1..N : proposal[i] = MaxV}) >= F + 1) ~> (\A i \in 1..N : pc[i] \in {"done", "crashed"})

====