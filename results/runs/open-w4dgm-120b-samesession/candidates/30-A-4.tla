---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES pc, localView, propose, estimate, decided, crashed, sent, rcvd

vars == <<pc, localView, propose, estimate, decided, crashed, sent, rcvd>>
Locs == {"bcast1", "wait1", "prepare", "bcast2", "wait2", "done", "crashed", "choosing"}
MsgTypes == {"phase1", "phase2"}
Msgs == [type: MsgTypes, val: Values \cup {Bottom}, from: 1..N, est: Values \cup {Bottom}]

TypeOK ==
    /\ pc \in [1..N -> Locs]
    /\ localView \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ propose \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Msgs
    /\ rcvd \in [1..N -> SUBSET Msgs]

Init ==
    /\ pc = [i \in 1..N |-> "bcast1"]
    /\ localView = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ propose \in [1..N -> Values]
    /\ estimate = [i \in 1..N |-> Bottom]
    /\ decided = [i \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ rcvd = [i \in 1..N |-> {}]

Bump(x) == IF x < N THEN x + 1 ELSE 1

Broadcast1(i) ==
    /\ pc[i] = "bcast1"
    /\ sent' = sent \cup {[type |-> "phase1", val |-> propose[i], from |-> i, est |-> Bottom]}
    /\ pc' = [pc EXCEPT ![i] = "wait1"]
    /\ UNCHANGED <<localView, propose, estimate, decided, crashed, rcvd>>

Receive1(i, m) ==
    /\ pc[i] = "wait1"
    /\ m \in rcvd[i]
    /\ m.type = "phase1"
    /\ localView' = [localView EXCEPT ![i][m.from] = m.val]
    /\ UNCHANGED <<pc, propose, estimate, decided, crashed, sent, rcvd>>

Compute(i) ==
    /\ pc[i] = "wait1"
    /\ Cardinality({j \in 1..N : localView[i][j] # Bottom}) >= N - T
    /\ estimate' = [estimate EXCEPT ![i] = CHOOSE v \in Values : \A j \in 1..N : localView[i][j] # Bottom => localView[i][j] <= v]
    /\ pc' = [pc EXCEPT ![i] = "bcast2"]
    /\ UNCHANGED <<localView, propose, decided, crashed, sent, rcvd>>

Broadcast2(i) ==
    /\ pc[i] = "bcast2"
    /\ sent' = sent \cup {[type |-> "phase2", val |-> propose[i], from |-> i, est |-> estimate[i]]}
    /\ pc' = [pc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED <<localView, propose, estimate, decided, crashed, rcvd>>

Receive2(i, m) ==
    /\ pc[i] = "wait2"
    /\ m \in rcvd[i]
    /\ m.type = "phase2"
    /\ localView' = [localView EXCEPT ![i][m.from] = m.val]
    /\ UNCHANGED <<pc, propose, estimate, decided, crashed, sent, rcvd>>

Decide(i) ==
    /\ pc[i] = "wait2"
    /\ \E v \in Values :
         /\ Cardinality({m \in rcvd[i] : m.type = "phase2" /\ m.est = v}) >= N - T
         /\ decided' = [decided EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<localView, propose, estimate, crashed, sent, rcvd>>

Choose(i) ==
    /\ pc[i] = "wait2"
    /\ \A v \in Values :
         Cardinality({m \in rcvd[i] : m.type = "phase2" /\ m.est = v}) < N - T
    /\ \A m \in rcvd[i] : m.type = "phase2" => localView' = [localView EXCEPT ![i][m.from] = m.val]
    /\ pc' = [pc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED <<propose, estimate, decided, crashed, sent, rcvd>>

DoChoose(i) ==
    /\ pc[i] = "choosing"
    /\ \E v \in Values :
         /\ \A j \in 1..N : localView[i][j] # Bottom => localView[i][j] <= v
         /\ decided' = [decided EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<localView, propose, estimate, crashed, sent, rcvd>>

Crash(i) ==
    /\ crashed < F
    /\ pc[i] \notin {"crashed", "done"}
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<localView, propose, estimate, decided, sent, rcvd>>

Arrive(m) ==
    /\ m \in sent
    /\ sent' = sent \ {m}
    /\ rcvd' = [rcvd EXCEPT ![m.from] = @ \cup {m}]
    /\ UNCHANGED <<pc, localView, propose, estimate, decided, crashed>>

Next ==
    \/ \E i \in 1..N : Broadcast1(i)
    \/ \E i \in 1..N, m \in Msgs : Receive1(i, m)
    \/ \E i \in 1..N : Compute(i)
    \/ \E i \in 1..N : Broadcast2(i)
    \/ \E i \in 1..N, m \in Msgs : Receive2(i, m)
    \/ \E i \in 1..N : Decide(i)
    \/ \E i \in 1..N : Choose(i)
    \/ \E i \in 1..N : DoChoose(i)
    \/ \E i \in 1..N : Crash(i)
    \/ \E m \in Msgs : Arrive(m)

Spec == Init /\ [][Next]_vars
    /\ \A i \in 1..N : WF_vars(\E m \in Msgs : Receive1(i, m))
    /\ \A i \in 1..N : SF_vars(Decide(i))
    /\ \A i \in 1..N : SF_vars(DoChoose(i))

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

MaxV == CHOOSE m \in {x \in sent : x.type = "phase1"} : \A x \in {y \in sent : y.type = "phase1"} : x.val <= y.val

Termination == \A i \in 1..N : (pc[i] \in {"wait1", "wait2"}) ~> (pc[i] \in {"done", "crashed"})
C1 == \A i \in 1..N : propose[i] = MaxV => (pc[i] \in {"wait1", "wait2"}) ~> (pc[i] \in {"done", "crashed"})

====