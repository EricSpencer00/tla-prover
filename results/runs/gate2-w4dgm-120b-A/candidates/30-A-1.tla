---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ 2 * T < N
       /\ N > 0
       /\ F \in 0 .. T
       /\ Bottom \notin Values

Msgs == [type: {"p1", "p2"}, val: Values \cup {Bottom}, snd: 1 .. N, est: Values \cup {Bottom}]

VARIABLES loc, view, prop, est, decision, crashed, sent, recv

TypeOK ==
  /\ loc \in [1 .. N -> {"b1", "w1", "pr", "b2", "w2", "done", "crashed", "choose"}]
  /\ view \in [1 .. N -> [1 .. N -> Values \cup {Bottom}]]
  /\ prop \in [1 .. N -> Values]
  /\ est \in [1 .. N -> Values \cup {Bottom}]
  /\ decision \in [1 .. N -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N

Init ==
  /\ loc = [i \in 1 .. N |-> "b1"]
  /\ view = [i \in 1 .. N |-> [j \in 1 .. N |-> Bottom]]
  /\ prop \in [1 .. N -> Values]
  /\ est = [i \in 1 .. N |-> Bottom]
  /\ decision = [i \in 1 .. N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1 .. N |-> {}]

ValidMsgs(m) == m.type \in {"p1", "p2"} /\ m.val \in Values /\ m.snd \in 1 .. N

\* Phase 1: broadcast proposals and compute a local maximum estimate.
BroadcastP1(i) ==
  /\ loc[i] = "b1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> prop[i], snd |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

ReceiveP1(i, m) ==
  /\ loc[i] = "w1"
  /\ m \in sent /\ m.type = "p1"
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

StartP2(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality({m \in recv[i] : m.type = "p1"}) >= N - T
  /\ est' = [est EXCEPT ![i] = CHOOSE x \in Values : \A j \in 1 .. N : view[i][j] # Bottom => view[i][j] <= x]
  /\ loc' = [loc EXCEPT ![i] = "b2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

\* Phase 2: broadcast the estimate and decide when enough agree.
BroadcastP2(i) ==
  /\ loc[i] = "b2"
  /\ sent' = sent \cup {[type |-> "p2", val |-> prop[i], snd |-> i, est |-> est[i]]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

ReceiveP2(i, m) ==
  /\ loc[i] = "w2"
  /\ m \in sent /\ m.type = "p2"
  /\ view' = [view EXCEPT ![i][m.snd] = m.est]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

DecideAgree(i, v) ==
  /\ loc[i] = "w2"
  /\ Cardinality({m \in recv[i] : m.type = "p2" /\ m.est = v}) >= N - T
  /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

DecideChoose(i) ==
  /\ loc[i] = "w2"
  /\ \A k \in 1 .. N : view[i][k] # Bottom
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, sent, recv>>

ChooseVal(i) ==
  /\ loc[i] = "choose"
  /\ decision' = [decision EXCEPT ![i] = CHOOSE x \in Values : \E j \in 1 .. N : view[i][j] = x]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* A process may crash silently, bounded by the fault tolerance.
Crash(i) ==
  /\ loc[i] # "crashed"
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

Next ==
  \/ \E i \in 1 .. N : BroadcastP1(i) \/ StartP2(i) \/ BroadcastP2(i) \/ DecideChoose(i) \/ ChooseVal(i) \/ Crash(i)
  \/ \E i \in 1 .. N, m \in Msgs : ReceiveP1(i, m) \/ ReceiveP2(i, m)
  \/ \E i \in 1 .. N, v \in Values : DecideAgree(i, v)

Spec ==
  /\ Init
  /\ [][Next]_<<loc, view, prop, est, decision, crashed, sent, recv>>
  /\ WF_vars(\E i \in 1 .. N, m \in Msgs : ReceiveP1(i, m))
  /\ WF_vars(\E i \in 1 .. N : StartP2(i))
  /\ WF_vars(\E i \in 1 .. N, m \in Msgs : ReceiveP2(i, m))
  /\ WF_vars(\E i \in 1 .. N : \E v \in Values : DecideAgree(i, v))
  /\ WF_vars(\E i \in 1 .. N : ChooseVal(i))

\* No lost updates: a decided value was actually proposed by someone.
Validity == \A i \in 1 .. N : decision[i] # Bottom => (\E j \in 1 .. N : prop[j] = decision[i])

\* Two processes never decide different values.
Agreement == \A i, j \in 1 .. N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination == <>(\A i \in 1 .. N : loc[i] \in {"done", "crashed"})

\* Under Condition C1 (enough max-proposers), every process decides.
C1Terminates ==
  /\ \A i \in 1 .. N : prop[i] = CHOOSE x \in Values : \A y \in Values : y <= x
  => Termination

====