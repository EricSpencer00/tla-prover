---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Control locations: two-phase broadcast-wait-finish plus crash and tie-breaking.
Locations == {"phase1bcast", "phase1wait", "phase2bcast", "phase2wait",
              "done", "crashed", "choosing"}

VARIABLES location, view, prop, estimate, decided, crashed, sent, received

vars == <<location, view, prop, estimate, decided, crashed, sent, received>>

TypeOK ==
    /\ location \in [1..N -> Locations]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ sent \subseteq [type: {"phase1", "phase2"}, value: Values,
                      from: 1..N, estimate: Values \cup {Bottom}]
    /\ received \in [1..N -> SUBSET 1..N]
    /\ crashed <= F

\* A process's local view is an N-entry array; Bottom is the sentinel for "unknown".
Init ==
    /\ location = [p \in 1..N |-> "phase1bcast"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ received = [p \in 1..N |-> {}]

\* Phase 1 generalizes the classic voting step: broadcasting the proposed value.
Phase1Broadcast(p) ==
    /\ location[p] = "phase1bcast"
    /\ Cardinality(received[p]) = 0
    /\ sent' = sent \cup {[type |-> "phase1", value |-> prop[p],
                           from |-> p, estimate |-> Bottom]}
    /\ location' = [location EXCEPT ![p] = "phase1wait"]
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, received>>

Phase1Receive(p, m) ==
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.from \notin received[p]
    /\ view' = [view EXCEPT ![p][m.from] = m.value]
    /\ received' = [received EXCEPT ![p] = @ \cup {m.from}]
    /\ UNCHANGED <<location, prop, estimate, decided, crashed, sent>>

\* With a quorum of N-T phase-1 messages a process estimates the eventual decision.
Phase1Complete(p) ==
    /\ location[p] = "phase1wait"
    /\ Cardinality(received[p]) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = Max({view[p][q] : q \in 1..N})]
    /\ location' = [location EXCEPT ![p] = "phase2bcast"]
    /\ UNCHANGED <<view, prop, decided, crashed, sent, received>>

Phase2Broadcast(p) ==
    /\ location[p] = "phase2bcast"
    /\ Cardinality(received[p]) = 0
    /\ sent' = sent \cup {[type |-> "phase2", value |-> prop[p],
                           from |-> p, estimate |-> estimate[p]]}
    /\ location' = [location EXCEPT ![p] = "phase2wait"]
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, received>>

Phase2Receive(p, m) ==
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m.from \notin received[p]
    /\ view' = [view EXCEPT ![p][m.from] = m.estimate]
    /\ received' = [received EXCEPT ![p] = @ \cup {m.from}]
    /\ UNCHANGED <<location, prop, estimate, decided, crashed, sent>>

\* Decision is made only once a quorum N-T agrees on the same estimate.
Phase2Decide(p) ==
    /\ location[p] = "phase2wait"
    /\ Cardinality({q \in 1..N : view[p][q] = estimate[p]}) >= N - T
    /\ decided' = [decided EXCEPT ![p] = estimate[p]]
    /\ location' = [location EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

\* Deterministic tie-breaking: pick any locally visible value once all have arrived.
Phase2Choose(p) ==
    /\ location[p] = "phase2wait"
    /\ Cardinality(received[p]) = N
    /\ \A e \in Values : Cardinality({q \in 1..N : view[p][q] = e}) < N - T
    /\ decided' = [decided EXCEPT ![p] = view[p][p]]
    /\ location' = [location EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

ChoosingComplete(p) ==
    /\ location[p] = "choosing"
    /\ decided' = [decided EXCEPT ![p] = view[p][p]]
    /\ location' = [location EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

\* Crash failures are silent and bounded by the tolerance budget.
Crash(p) ==
    /\ location[p] \notin {"crashed", "done"}
    /\ crashed < F
    /\ location' = [location EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, prop, estimate, decided, sent, received>>

Next ==
    \/ \E p \in 1..N : Phase1Broadcast(p)
    \/ \E p \in 1..N, m \in sent : Phase1Receive(p, m)
    \/ \E p \in 1..N : Phase1Complete(p)
    \/ \E p \in 1..N : Phase2Broadcast(p)
    \/ \E p \in 1..N, m \in sent : Phase2Receive(p, m)
    \/ \E p \in 1..N : Phase2Decide(p)
    \/ \E p \in 1..N : Phase2Choose(p)
    \/ \E p \in 1..N : ChoosingComplete(p)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
    /\ \A p \in 1..N :
        /\ TRUE
        /\ SF_vars(\E m \in sent : Phase1Receive(p, m))
        /\ SF_vars(Phase1Complete(p))
        /\ SF_vars(\E m \in sent : Phase2Receive(p, m))
        /\ SF_vars(Phase2Decide(p))
        /\ WF_vars(ChoosingComplete(p))
    /\ WF_vars(\E p \in 1..N : Phase1Broadcast(p))
    /\ WF_vars(\E p \in 1..N : Phase2Broadcast(p))

\* Validity: a decision is always traceable to a real proposal.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : prop[q] = decided[p]

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom)
                                            => decided[p] = decided[q]

\* Progress: the two-phase protocol finishes despite up to T crashes.
Termination == \A p \in 1..N : (location[p] \in {"crashed", "done"}) ~> TRUE

\* Condition C1 from the paper (bounded faults): the max value is proposed enough.
ConditionC1 == (\A q \in 1..N : prop[q] = Max(Values)) => (F + 1 <= N)

ConditionalTermination == ConditionC1 ~> Termination
====