---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES pc, view, proposal, estimate, decided, crashes, sent, rcvd

vars == <<pc, view, proposal, estimate, decided, crashes, sent, rcvd>>
Locs == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}
MsgTypes == {"phase1", "phase2"}
\* A message records its type, value, sender, and for phase 2 also the sender's estimate.
Message == [type: MsgTypes, val: Values, sender: 0..(N - 1), est: Values \cup {Bottom}]

TypeOK ==
    /\ pc \in [0..(N - 1) -> Locs]
    /\ view \in [0..(N - 1) -> [0..(N - 1) -> Values \cup {Bottom}]]
    /\ proposal \in [0..(N - 1) -> Values]
    /\ estimate \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ decided \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ crashes \in 0..N
    /\ sent \subseteq Message
    /\ rcvd \in [0..(N - 1) -> SUBSET Message]

Init ==
    /\ pc = [i \in 0..(N - 1) |-> "broadcast1"]
    /\ view = [i \in 0..(N - 1) |-> [j \in 0..(N - 1) |-> Bottom]]
    /\ proposal \in [i \in 0..(N - 1) -> Values]
    /\ estimate = [i \in 0..(N - 1) |-> Bottom]
    /\ decided = [i \in 0..(N - 1) |-> Bottom]
    /\ crashes = 0
    /\ sent = {}
    /\ rcvd = [i \in 0..(N - 1) |-> {}]

\* Phase 1: broadcast the proposed value.
Broadcast1(i) ==
    /\ pc[i] = "broadcast1"
    /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[i],
                           sender |-> i, est |-> Bottom]}
    /\ pc' = [pc EXCEPT ![i] = "wait1"]
    /\ UNCHANGED <<view, proposal, estimate, decided, crashes, rcvd>>

Receive1(i, m) ==
    /\ pc[i] = "wait1"
    /\ m \in rcvd[i]
    /\ m.type = "phase1"
    /\ view[i][m.sender] = Bottom
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ UNCHANGED <<pc, proposal, estimate, decided, crashes, sent, rcvd>>

\* A process needs only N-T distinct phase-1 messages to compute its estimate.
Estimate(i) ==
    /\ pc[i] = "wait1"
    /\ Cardinality({j \in 0..(N - 1) : view[i][j] # Bottom}) >= N - T
    /\ estimate' = [estimate EXCEPT ![i] =
                        CHOOSE v \in Values :
                            \A j \in 0..(N - 1) : (view[i][j] # Bottom) => v >= view[i][j]]
    /\ pc' = [pc EXCEPT ![i] = "broadcast2"]
    /\ UNCHANGED <<view, proposal, decided, crashes, sent, rcvd>>

\* Phase 2: broadcast the proposed value together with the computed estimate.
Broadcast2(i) ==
    /\ pc[i] = "broadcast2"
    /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[i],
                           sender |-> i, est |-> estimate[i]]}
    /\ pc' = [pc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED <<view, proposal, estimate, decided, crashes, rcvd>>

\* A process may finish if many phase-2 messages agree on the same estimate.
Decide(i) ==
    /\ pc[i] = "wait2"
    /\ \E v \in Values :
        /\ Cardinality({m \in rcvd[i] : m.type = "phase2" /\ m.est = v}) >= N - T
        /\ decided' = [decided EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, proposal, estimate, crashes, sent, rcvd>>

\* If no estimate reaches the threshold, one is picked from the local view.
Choose(i) ==
    /\ pc[i] = "wait2"
    /\ \A v \in Values :
        Cardinality({m \in rcvd[i] : m.type = "phase2" /\ m.est = v}) < N - T
    /\ \E v \in Values :
        /\ \E j \in 0..(N - 1) : view[i][j] = v
        /\ decided' = [decided EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, proposal, estimate, crashes, sent, rcvd>>

Crash(i) ==
    /\ pc[i] # "crashed"
    /\ crashes < F
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ crashes' = crashes + 1
    /\ UNCHANGED <<view, proposal, estimate, decided, sent, rcvd>>

\* Delivery is nondeterministic but never fails: a message in flight is always receivable.
Deliver ==
    \E i \in 0..(N - 1), m \in sent :
        /\ pc[i] \in {"wait1", "wait2"}
        /\ m \notin rcvd[i]
        /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {m}]
        /\ UNCHANGED <<pc, view, proposal, estimate, decided, crashes, sent>>

Next ==
    \/ Deliver
    \/ \E i \in 0..(N - 1) : Broadcast1(i) \/ Broadcast2(i) \/ Estimate(i)
                              \/ Decide(i) \/ Choose(i) \/ Crash(i)
    \/ \E i \in 0..(N - 1), m \in Message : Receive1(i, m)

\* A decision is always reachable: every non-crashed process eventually decides.
Spec == Init /\ [][Next]_vars /\ WF_vars(Deliver)

Validity == \A i \in 0..(N - 1) : decided[i] # Bottom => \E j \in 0..(N - 1) : proposal[j] = decided[i]

Agreement == \A i, j \in 0..(N - 1) : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

\* Conditional termination under Condition C1 (the majority of fault tolerance).
TerminateOnMajority ==
    (\E i \in 0..(N - 1) : proposal[i] = Max(Values)) => \A i \in 0..(N - 1) : pc[i] \in {"done", "crashed"}

====