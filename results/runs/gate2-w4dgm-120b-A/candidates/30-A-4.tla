---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES pc, view, prop, est, decided, crashed, sent, recv
vars == <<pc, view, prop, est, decided, crashed, sent, recv>>

Locations == {"broadcasting1", "waiting1", "preparing", "broadcasting2", "waiting2", "done", "crashed", "choosing"}
Phases == {"phase1", "phase2"}
Msgs == [type: Phases, val: Values \cup {Bottom}, est: Values \cup {Bottom}, sender: 0..(N - 1)]

RECURSIVE MaxInSet(_)
MaxInSet(S) ==
    IF S = {} THEN Bottom
    ELSE LET x == CHOOSE y \in S : TRUE IN IF x > MaxInSet(S \ {x}) THEN x ELSE MaxInSet(S \ {x})

TypeOK ==
    /\ pc \in [0..(N - 1) -> Locations]
    /\ view \in [0..(N - 1) -> [0..(N - 1) -> Values \cup {Bottom}]]
    /\ prop \in [0..(N - 1) -> Values]
    /\ est \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ decided \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ sent \subseteq Msgs
    /\ recv \in [0..(N - 1) -> SUBSET 0..(N - 1)]

Init ==
    /\ pc = [i \in 0..(N - 1) |-> "broadcasting1"]
    /\ view = [i \in 0..(N - 1) |-> [j \in 0..(N - 1) |-> Bottom]]
    /\ prop \in [0..(N - 1) -> Values]
    /\ est = [i \in 0..(N - 1) |-> Bottom]
    /\ decided = [i \in 0..(N - 1) |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = [i \in 0..(N - 1) |-> {}]

BroadcastPhase1(i) ==
    /\ pc[i] = "broadcasting1"
    /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[i], est |-> Bottom, sender |-> i]}
    /\ pc' = [pc EXCEPT ![i] = "waiting1"]
    /\ UNCHANGED <<view, prop, est, decided, crashed, recv>>

ReceiveMsg(i, m) ==
    /\ pc[i] \in {"waiting1", "waiting2"}
    /\ m.sender \notin recv[i]
    /\ m \in sent
    /\ m.type = (IF pc[i] = "waiting1" THEN "phase1" ELSE "phase2")
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.sender}]
    /\ UNCHANGED <<pc, prop, est, decided, crashed, sent>>

TransitionToPhase2(i) ==
    /\ pc[i] = "waiting1"
    /\ Cardinality(recv[i]) >= N - T
    /\ est' = [est EXCEPT ![i] = MaxInSet({view[i][j] : j \in 0..(N - 1)} \cup {prop[i]})]
    /\ pc' = [pc EXCEPT ![i] = "broadcasting2"]
    /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

BroadcastPhase2(i) ==
    /\ pc[i] = "broadcasting2"
    /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[i], est |-> est[i], sender |-> i]}
    /\ pc' = [pc EXCEPT ![i] = "waiting2"]
    /\ UNCHANGED <<view, prop, est, decided, crashed, recv>>

Decide(i) ==
    /\ pc[i] = "waiting2"
    /\ \E v \in Values :
        /\ Cardinality({j \in 0..(N - 1) : j \in recv[i] /\ view[i][j] = v}) >= N - T
        /\ decided' = [decided EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Choose(i) ==
    /\ pc[i] = "waiting2"
    /\ recv[i] = 0..(N - 1)
    /\ pc' = [pc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED <<view, prop, est, decided, crashed, sent, recv>>

Arbitrate(i, v) ==
    /\ pc[i] = "choosing"
    /\ v \in {view[i][j] : j \in 0..(N - 1)} \cup {prop[i]}
    /\ decided' = [decided EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(i) ==
    /\ crashed < F
    /\ pc[i] \notin {"crashed", "done"}
    /\ crashed' = crashed + 1
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED <<view, prop, est, decided, sent, recv>>

Next ==
    \/ \E i \in 0..(N - 1) : BroadcastPhase1(i) \/ TransitionToPhase2(i) \/ BroadcastPhase2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)
    \/ \E i \in 0..(N - 1), m \in Msgs : ReceiveMsg(i, m)
    \/ \E i \in 0..(N - 1), v \in Values : Arbitrage(i, v)

Spec == Init /\ [][Next]_vars

Validity == \A i \in 0..(N - 1) : decided[i] # Bottom => \E j \in 0..(N - 1) : prop[j] = decided[i]

Agreement == \A i, j \in 0..(N - 1) : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]
====