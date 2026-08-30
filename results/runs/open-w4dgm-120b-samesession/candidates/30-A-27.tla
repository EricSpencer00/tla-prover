---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, est, decision, crashed, sent, recv

Vars == <<loc, view, prop, est, decision, crashed, sent, recv>>
Msgs == [type: {"phase1", "phase2"}, val: Values \cup {Bottom}, sender: 1..N, estv: Values \cup {Bottom}]

Locs == {"bcast1", "wait1", "prepare", "bcast2", "wait2", "done", "crashed", "choosing"}

RECURSIVE MaxIn(_)
MaxIn(S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE
       IN IF MAX(x, MaxIn(S \ {x})) = x THEN x ELSE MaxIn(S \ {x})

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msgs
  /\ recv \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [i \in 1..N |-> "bcast1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

Bcast1(i) ==
  /\ loc[i] = "bcast1"
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[i], sender |-> i, estv |-> Bottom]}
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Receive1(i, m) ==
  /\ loc[i] = "wait1"
  /\ m.type = "phase1"
  /\ m.sender \notin {msg.sender : msg \in recv[i]}
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

Prepare(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality({msg \in recv[i] : msg.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![i] = MaxIn({view[i][j] : j \in 1..N})]
  /\ loc' = [loc EXCEPT ![i] = "bcast2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

Bcast2(i) ==
  /\ loc[i] = "bcast2"
  /\ loc' = [loc EXCEPT ![i] = "wait2"]
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[i], sender |-> i, estv |-> est[i]]}
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Receive2(i, m) ==
  /\ loc[i] = "wait2"
  /\ m.type = "phase2"
  /\ m.sender \notin {msg.sender : msg \in recv[i]}
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

DecideFromVotes(i) ==
  /\ loc[i] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({msg \in recv[i] : msg.type = "phase2" /\ msg.estv = v}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Choose(i) ==
  /\ loc[i] = "wait2"
  /\ {msg.sender : msg \in recv[i]} = 1..N
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, sent, recv>>

MakeChoice(i) ==
  /\ loc[i] = "choosing"
  /\ \E v \in Values :
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(i) ==
  /\ loc[i] \notin {"done", "crashed"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

Next ==
  \/ \E i \in 1..N : Bcast1(i) \/ Prepare(i) \/ Bcast2(i) \/ DecideFromVotes(i) \/ Choose(i) \/ MakeChoice(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in sent : Receive1(i, m) \/ Receive2(i, m)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A i \in 1..N :
       /\ TRUE
       /\ WF_Vars(Receive1(i, [type |-> "phase1", val |-> CHOOSE v \in Values : TRUE, sender |-> 1, estv |-> Bottom])
       /\ WF_Vars(Prepare(i))
       /\ WF_Vars(Receive2(i, [type |-> "phase2", val |-> CHOOSE v \in Values : TRUE, sender |-> 1, estv |-> CHOOSE w \in Values : TRUE]))
       /\ WF_Vars(DecideFromVotes(i))
       /\ WF_Vars(Choose(i))
       /\ WF_Vars(MakeChoice(i))
  /\ \A i \in 1..N : WF_Vars(Bcast1(i))
  /\ \A i \in 1..N : WF_Vars(Bcast2(i))

Validity == \A i \in 1..N : decision[i] # Bottom => (\E j \in 1..N : prop[j] = decision[i])

Agreement == \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})

ConditionC1 == \A v \in Values : (\E i \in 1..N : prop[i] = v) => Cardinality({i \in 1..N : prop[i] = v}) >= F + 1

ConditionalTermination == ConditionC1 ~> Termination

====