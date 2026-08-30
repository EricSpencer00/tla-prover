---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Procs == 1..N
MsgTypes == {"phase1", "phase2"}
Controls == {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choosing"}
MaxV == 3
MaxSet(s) == IF s = {} THEN Bottom ELSE CHOOSE x \in s : \A y \in s : y <= x

VARIABLES ctrl, view, prop, est, decision, crashed, sent, recv

vars == <<ctrl, view, prop, est, decision, crashed, sent, recv>>

Init ==
  /\ ctrl = [i \in Procs |-> "bc1"]
  /\ view = [i \in Procs |-> [k \in Procs |-> Bottom]]
  /\ prop \in [i \in Procs |-> Values]
  /\ est = [i \in Procs |-> Bottom]
  /\ decision = [i \in Procs |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in Procs |-> {}]

Broadcast1(i) ==
  /\ ctrl[i] = "bc1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[i], from |-> i]}
  /\ ctrl' = [ctrl EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Receive1(i, m) ==
  /\ m \in sent
  /\ m.type = "phase1"
  /\ ctrl[i] \in {"w1", "prep"}
  /\ view[i][m.from] = Bottom
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<ctrl, prop, est, decision, crashed, sent>>

ReadyPhase2(i) ==
  /\ ctrl[i] = "w1"
  /\ Cardinality({m \in recv[i] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![i] = MaxSet({view[i][k] : k \in Procs})]
  /\ ctrl' = [ctrl EXCEPT ![i] = "bc2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

Broadcast2(i) ==
  /\ ctrl[i] = "bc2"
  /\ est[i] # Bottom
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[i], est |-> est[i], from |-> i]}
  /\ ctrl' = [ctrl EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Decide(i) ==
  /\ ctrl[i] = "w2"
  /\ \E v \in Values :
       /\ Cardinality({m \in recv[i] : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ ctrl' = [ctrl EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Receiving(i, m) ==
  /\ m \in sent
  /\ m.type = "phase2"
  /\ ctrl[i] \in {"w2", "choosing"}
  /\ view[i][m.from] = Bottom
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<ctrl, prop, est, decision, crashed, sent>>

Choosing(i) ==
  /\ ctrl[i] = "w2"
  /\ \A k \in Procs : view[i][k] # Bottom
  /\ \A v \in Values :
       Cardinality({m \in recv[i] : m.type = "phase2" /\ m.est = v}) < N - T
  /\ decision' = [decision EXCEPT ![i] = MaxSet({view[i][k] : k \in Procs})]
  /\ ctrl' = [ctrl EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Finishing(i) ==
  /\ ctrl[i] = "choosing"
  /\ decision[i] # Bottom
  /\ ctrl' = [ctrl EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, sent, recv>>

Crash(i) ==
  /\ crashed < F
  /\ ctrl[i] \notin {"done", "crashed"}
  /\ ctrl' = [ctrl EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

Next ==
  \/ \E i \in Procs : Broadcast1(i)
  \/ \E i \in Procs, m \in sent : Receive1(i, m)
  \/ \E i \in Procs : ReadyPhase2(i)
  \/ \E i \in Procs : Broadcast2(i)
  \/ \E i \in Procs : Decide(i)
  \/ \E i \in Procs, m \in sent : Receiving(i, m)
  \/ \E i \in Procs : Choosing(i)
  \/ \E i \in Procs : Finishing(i)
  \/ \E i \in Procs : Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Procs :
       /\ TRUE
       /\ WF_vars(Finishi(i) \/ Crash(i))
  /\ \A i \in Procs :
       /\ SF_vars(\E m \in sent : Receive1(i, m))
       /\ SF_vars(\E m \in sent : Receiving(i, m))
  /\ \A i \in Procs : WF_vars(\E m \in sent : Receive1(i, m) \/ Receiving(i, m))
  /\ \A i \in Procs : SF_vars(Choosing(i) \/ Deciding(i))

TypeOK ==
  /\ ctrl \in [Procs -> Controls]
  /\ view \in [Procs -> [Procs -> Values \cup {Bottom}]]
  /\ prop \in [Procs -> Values]
  /\ est \in [Procs -> Values \cup {Bottom}]
  /\ decision \in [Procs -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type : MsgTypes, val : Values, est : Values \cup {Bottom}, from : Procs]
  /\ recv \in [Procs -> SUBSET [type : MsgTypes, val : Values, est : Values \cup {Bottom}, from : Procs]]

Validity ==
  \A i \in Procs : decision[i] # Bottom => \E j \in Procs : prop[j] = decision[i]

Agreement ==
  \A i, j \in Procs : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination ==
  \A i \in Procs : (ctrl[i] = "crashed") ~> (ctrl[i] = "done")

ConditionC1 == Cardinality({i \in Procs : prop[i] = MaxV}) >= F + 1

ConditionalTermination == ConditionC1 ~> (\A i \in Procs : ctrl[i] = "done")

====