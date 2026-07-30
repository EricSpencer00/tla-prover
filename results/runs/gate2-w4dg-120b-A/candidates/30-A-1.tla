---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A message carries a phase tag, a sender, the sender's proposed value, and, for
\* phase 2, the sender's estimated max.
Msg == [phase: {"p1", "p2"}, sender: 1..N, val: Values, est: Values \cup {Bottom}]

VARIABLES loc, view, prop, est, decision, crashedCount, sent, recv

vars == <<loc, view, prop, est, decision, crashedCount, sent, recv>>

Phase1Locs == {"broadcastP1", "waitingP1"}
Phase2Locs == {"broadcastP2", "waitingP2"}
AllLocs == Phase1Locs \cup Phase2Locs \cup {"done", "crashed", "choosing"}

TypeOK ==
    /\ loc \in [1..N -> AllLocs]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashedCount \in 0..F
    /\ sent \subseteq Msg
    /\ recv \subseteq Msg

Init ==
    /\ loc = [p \in 1..N |-> "broadcastP1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ est = [p \in 1..N |-> Bottom]
    /\ decision = [p \in 1..N |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = {}

BroadcastP1(p) ==
    /\ loc[p] = "broadcastP1"
    /\ sent' = sent \cup {[phase |-> "p1", sender |-> p, val |-> prop[p], est |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "waitingP1"]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, recv>>

\* A phase-1 waiting process updates its local view with phase-1 messages.
ReceiveP1(p, m) ==
    /\ loc[p] \in Phase1Locs
    /\ m \in recv
    /\ m.phase = "p1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = recv \ {m}
    /\ UNCHANGED <<loc, prop, est, decision, crashedCount, sent>>

Estimate(p) ==
    /\ loc[p] = "waitingP1"
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
    /\ est' = [est EXCEPT ![p] = CHOOSE x \in Values : \A y \in Values : (y \in {view[p][q] : q \in 1..N} => y <= x)]
    /\ loc' = [loc EXCEPT ![p] = "broadcastP2"]
    /\ UNCHANGED <<view, prop, decision, crashedCount, sent, recv>>

BroadcastP2(p) ==
    /\ loc[p] = "broadcastP2"
    /\ sent' = sent \cup {[phase |-> "p2", sender |-> p, val |-> prop[p], est |-> est[p]]}
    /\ loc' = [loc EXCEPT ![p] = "waitingP2"]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, recv>>

\* A phase-2 waiting process updates its local view with phase-2 messages.
ReceiveP2(p, m) ==
    /\ loc[p] \in Phase2Locs
    /\ m \in recv
    /\ m.phase = "p2"
    /\ view' = [view EXCEPT ![p][m.sender] = m.est]
    /\ recv' = recv \ {m}
    /\ UNCHANGED <<loc, prop, est, decision, crashedCount, sent>>

QuorumAgree(p) ==
    /\ loc[p] = "waitingP2"
    /\ \E v \in Values :
        /\ Cardinality({m \in recv : m.phase = "p2" /\ m.est = v}) >= N - T
        /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ recv' = {m \in recv : m.phase = "p2" /\ m.sender # p}
    /\ UNCHANGED <<view, prop, est, crashedCount, sent>>

Choose(p) ==
    /\ loc[p] = "waitingP2"
    /\ \A q \in 1..N : [phase |-> "p2", sender |-> q, val |-> prop[q], est |-> est[q]] \in recv
    /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in Values : \E q \in 1..N : view[p][q] = v]
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

\* A crashed process stops participating.
Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashedCount < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

\* The network is asynchronous: any message in flight may be delivered.
Deliver == \E p \in 1..N, m \in recv : ReceiveP1(p, m) \/ ReceiveP2(p, m)

Next ==
    \/ \E p \in 1..N : BroadcastP1(p) \/ BroadcastP2(p) \/ Estimate(p) \/ QuorumAgree(p) \/ Choose(p) \/ Crash(p)
    \/ Deliver

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Deliver)
        /\ WEAK_FAIRNESS(vars, (\E p \in 1..N : BroadcastP1(p)))
        /\ WEAK_FAIRNESS(vars, (\E p \in 1..N : Estimate(p)))
        /\ WEAK_FAIRNESS(vars, (\E p \in 1..N : BroadcastP2(p)))
        /\ WEAK_FAIRNESS(vars, (\E p \in 1..N : QuorumAgree(p)))
        /\ WEAK_FAIRNESS(vars, (\E p \in 1..N : Choose(p)))

Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in {prop[q] : q \in 1..N}

Agreement == \A p \in 1..N : (\E q \in 1..N : decision[p] = decision[q])
             \/ (\A q \in 1..N : decision[q] = Bottom)

Termination == <>(\A p \in 1..N : loc[p] \in {"crashed", "done"})

\* The heavyweight condition from the paper: enough max-proposers for guaranteed
\* termination.
ConditionC1 == \A p \in 1..N :
                  (Cardinality({q \in 1..N : prop[q] = (CHOOSE v \in Values : \A w \in Values : w <= v)}) >= F + 1)
                  => Termination

\* The model's parameters must stay inside the fault-tolerant regime.
ValidParams ==
    /\ 0 <= F /\ F <= T /\ 2 * T < N /\ N > 0
    /\ \A x \in Values : x # Bottom

Properties == Termination /\ ConditionC1

====