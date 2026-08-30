---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The control location of each process (broadcasting, waiting, crashed, etc.).
Locs == {"bphase1", "wait1", "prepare", "bphase2", "wait2", "done", "crashed", "choose"}

VARIABLES location, view, proposal, estimate, decided, crashedCount, sent, recv

vars == <<location, view, proposal, estimate, decided, crashedCount, sent, recv>>

NONE == "none"

MaxSet(S) == CHOOSE m \in S : \A x \in S : x <= m

TypeOK ==
    /\ location \in [1..N -> Locs]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ proposal \in [1..N -> Values \cup {Bottom}]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashedCount \in 0..F
    /\ sent \subseteq [type: {"phase1", "phase2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, src: 1..N]
    /\ recv \in [1..N -> SUBSET 1..N]

Init ==
    /\ location = [p \in 1..N |-> "bphase1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ proposal \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in 1..N |-> {}]

\* Phase 1: broadcast the proposed value.
BroadcastPhase1(p) ==
    /\ location[p] = "bphase1"
    /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[p], est |-> Bottom, src |-> p]}
    /\ location' = [location EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, proposal, estimate, decided, crashedCount, recv>>

\* Phase 1: receive messages and update the local view.
ReceivePhase1(p, m) ==
    /\ location[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ view[p][m.src] = Bottom
    /\ view' = [view EXCEPT ![p][m.src] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.src}]
    /\ UNCHANGED <<location, proposal, estimate, decided, crashedCount, sent>>

\* Phase 1: once enough messages are in view, estimate the maximum and move on.
Prepare(p) ==
    /\ location[p] = "wait1"
    /\ Cardinality(recv[p]) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxSet({view[p][q] : q \in 1..N})
    /\ location' = [location EXCEPT ![p] = "bphase2"]
    /\ UNCHANGED <<view, proposal, decided, crashedCount, sent, recv>>

\* Phase 2: broadcast the proposal together with the estimated maximum.
BroadcastPhase2(p) ==
    /\ location[p] = "bphase2"
    /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[p], est |-> estimate[p], src |-> p]}
    /\ location' = [location EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, proposal, estimate, decided, crashedCount, recv>>

\* Phase 2: adopt the majority estimated value once it forms an (N-T)-sized set.
Decide(p) ==
    /\ location[p] = "wait2"
    /\ Cardinality({m \in sent : m.src \in recv[p] /\ m.type = "phase2" /\ m.est = estimate[p]}) >= N - T
    /\ decided' = [decided EXCEPT ![p] = estimate[p]]
    /\ location' = [location EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposal, estimate, crashedCount, sent, recv>>

\* Phase 2: if nothing reaches the threshold, choose deterministically from the view.
Choose(p) ==
    /\ location[p] = "wait2"
    /\ Cardinality({m \in sent : m.src \in recv[p] /\ m.type = "phase2"}) = N
    /\ \A e \in Values : Cardinality({m \in sent : m.src \in recv[p] /\ m.type = "phase2" /\ m.est = e}) < N - T
    /\ decided' = [decided EXCEPT ![p] = view[p][p]]
    /\ location' = [location EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, proposal, estimate, crashedCount, sent, recv>>

FinishChoose(p) ==
    /\ location[p] = "choose"
    /\ decided' = [decided EXCEPT ![p] = view[p][p]]
    /\ location' = [location EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposal, estimate, crashedCount, sent, recv>>

\* Crash: a process may crash as long as the fault budget is not spent.
Crash(p) ==
    /\ crashedCount < F
    /\ location[p] \notin {"crashed", "done"}
    /\ crashedCount' = crashedCount + 1
    /\ location' = [location EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, proposal, estimate, decided, sent, recv>>

Next ==
    \/ \E p \in 1..N : BroadcastPhase1(p)
    \/ \E p \in 1..N, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in 1..N : Prepare(p)
    \/ \E p \in 1..N : BroadcastPhase2(p)
    \/ \E p \in 1..N : Decide(p)
    \/ \E p \in 1..N : Choose(p)
    \/ \E p \in 1..N : FinishChoose(p)
    \/ \E p \in 1..N : Crash(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in 1..N : WF_vars(Decide(p))
    /\ \A p \in 1..N : WF_vars(FinishChoose(p))

\* Safety: any decided value was actually proposed by some process.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : proposal[q] = decided[p]

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[p] # decided[q]) => decided[q] = Bottom

\* Liveness: despite crashes, every process eventually crashes or decides.
Termination == \A p \in 1..N : (location[p] \notin {"done", "crashed"}) ~> (location[p] \in {"done", "crashed"})

\* Conditional termination under Condition C1 (F+1 propose the maximum value).
ConditionC1 == (\A p \in 1..N : proposal[p] = MaxSet(Values)) => (\A p \in 1..N : location[p] \in {"done", "crashed"})

====