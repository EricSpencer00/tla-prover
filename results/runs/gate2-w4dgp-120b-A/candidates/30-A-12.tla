---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0
ASSUME T \in Nat /\ F \in Nat /\ T > 0
ASSUME 2 * T < N
ASSUME Bottom \notin Values

VARIABLES pc, view, proposed, estimate, decision, crashedCount, sent, recv

vars == <<pc, view, proposed, estimate, decision, crashedCount, sent, recv>>
Views == [N -> Values \cup {Bottom}]
Messages == [type: {1, 2}, val: Values \cup {Bottom}, sender: 1..N, est: Values \cup {Bottom}]

LockFree == Cardinality({i \in 1..N : view[i][pc[i]] = Values})
MaxV == CHOOSE v \in Values : \A w \in Values : v >= w

TypeOK ==
    /\ pc \in [1..N -> {"b1", "w1", "pr", "b2", "w2", "done", "crash", "choose"}]
    /\ view \in [1..N -> Views]
    /\ proposed \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashedCount \in 0..T
    /\ sent \subseteq Messages
    /\ recv \subseteq Messages

Init ==
    /\ pc = [i \in 1..N |-> "b1"]
    /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ proposed \in [1..N -> Values]
    /\ estimate = [i \in 1..N |-> Bottom]
    /\ decision = [i \in 1..N |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = {}

Broadcast1(i) ==
    /\ pc[i] = "b1"
    /\ sent' = sent \cup {[type |-> 1, val |-> proposed[i], sender |-> i, est |-> Bottom]}
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<view, proposed, estimate, decision, crashedCount, recv>>

Receive1(i, m) ==
    /\ pc[i] = "w1"
    /\ m \in sent
    /\ m.type = 1
    /\ m.sender \notin {j \in 1..N : view[i][j] # Bottom}
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ UNCHANGED <<pc, proposed, estimate, decision, crashedCount, sent, recv>>

Transition1(i) ==
    /\ pc[i] = "w1"
    /\ Cardinality({j \in 1..N : view[i][j] # Bottom}) >= N - T
    /\ estimate' = [estimate EXCEPT ![i] = MaxV]
    /\ pc' = [pc EXCEPT ![i] = "pr"]
    /\ UNCHANGED <<view, proposed, decision, crashedCount, sent, recv>>

Broadcast2(i) ==
    /\ pc[i] = "pr"
    /\ sent' = sent \cup {[type |-> 2, val |-> proposed[i], sender |-> i, est |-> estimate[i]]}
    /\ pc' = [pc EXCEPT ![i] = "w2"]
    /\ UNCHANGED <<view, proposed, estimate, decision, crashedCount, recv>>

Receive2(i, m) ==
    /\ pc[i] = "w2"
    /\ m \in sent
    /\ m.type = 2
    /\ m.sender \notin {j \in 1..N : view[i][j] # Bottom}
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ recv' = recv \cup {m}
    /\ UNCHANGED <<pc, proposed, estimate, decision, crashedCount, sent>>

Decide(i, v) ==
    /\ pc[i] = "w2"
    /\ Cardinality({m \in recv : m.est = v}) >= N - T
    /\ decision' = [decision EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, crashedCount, sent, recv>>

Choose(i) ==
    /\ pc[i] = "w2"
    /\ {m \in recv : m.sender = i} = {}
    /\ \A m \in recv : view[i][m.sender] # Bottom
    /\ Cardinality({j \in 1..N : view[i][j] # Bottom}) = N
    /\ \A v \in Values : Cardinality({m \in recv : m.est = v}) < N - T
    /\ pc' = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED <<view, proposed, estimate, decision, crashedCount, sent, recv>>

DecideFromView(i) ==
    /\ pc[i] = "choose"
    /\ decision' = [decision EXCEPT ![i] = CHOOSE v \in Values : view[i][i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, crashedCount, sent, recv>>

Crash(i) ==
    /\ pc[i] # "crash"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![i] = "crash"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, proposed, estimate, decision, sent, recv>>

Next ==
    \/ \E i \in 1..N : Broadcast1(i) \/ Transition1(i) \/ Broadcast2(i)
    \/ \E i \in 1..N, m \in Messages : Receive1(i, m) \/ Receive2(i, m)
    \/ \E i \in 1..N, v \in Values : Decide(i, v)
    \/ \E i \in 1..N : Choose(i) \/ DecideFromView(i) \/ Crash(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E i \in 1..N, m \in Messages : Receive1(i, m))
    /\ WF_vars(\E i \in 1..N, m \in Messages : Receive2(i, m))
    /\ WF_vars(\E i \in 1..N : Transition1(i))
    /\ WF_vars(\E i \in 1..N : Choose(i))
    /\ WF_vars(\E i \in 1..N : Choose(i))

Validity ==
    \A i \in 1..N : decision[i] # Bottom => decision[i] \in Values

Agreement ==
    \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Terminating ==
    \A i \in 1..N : (pc[i] = "crash" \/ pc[i] = "done")

C1 == LockFree >= F + 1

ConditionalTermination ==
    C1 ~> (C1 /\ Terminating)

====