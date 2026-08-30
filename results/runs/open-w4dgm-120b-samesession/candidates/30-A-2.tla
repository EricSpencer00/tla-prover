---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, estimate, decided, crashed, msgs, rcvd

vars == <<loc, view, prop, estimate, decided, crashed, msgs, rcvd>>

TypeOK ==
    /\ loc \in [1..N -> {"b1","w1","prep","b2","w2","done","crashed","choose"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ msgs \subseteq [type: {"p1","p2"}, val: Values, sender: 1..N, est: Values \cup {Bottom}]
    /\ rcvd \in [1..N -> SUBSET 1..N]

Init ==
    /\ loc = [p \in 1..N |-> "b1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ msgs = {}
    /\ rcvd = [p \in 1..N |-> {}]

Emit(m) == msgs' = msgs \cup {m}
Seen(p, t) == {m \in msgs : m.sender \in rcvd[p] /\ m.type = t}

\* Phase 1: broadcast a proposed value and collect a majority of phase-1 messages.
Broadcast1(p) ==
    /\ loc[p] = "b1"
    /\ Emit([type |-> "p1", val |-> prop[p], sender |-> p, est |-> Bottom])
    /\ loc' = [loc EXCEPT ![p] = "w1"]
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, rcvd>>

Receive1(p, m) ==
    /\ loc[p] = "w1"
    /\ m.type = "p1"
    /\ m.sender \notin rcvd[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m.sender}]
    /\ UNCHANGED <<loc, prop, estimate, decided, crashed, msgs>>

\* A process may be slow to collect, but once it has a majority it computes its
\* estimate (the maximum seen) and moves on to phase 2.
Prepare(p) ==
    /\ loc[p] = "w1"
    /\ Cardinality(rcvd[p]) >= N - T
    /\ \E s \in Values :
         /\ \A q \in 1..N : view[p][q] # Bottom => view[p][q] <= s
         /\ estimate' = [estimate EXCEPT ![p] = s]
    /\ loc' = "prep"
    /\ UNCHANGED <<view, prop, decided, crashed, msgs, rcvd>>

\* Phase 2: broadcast both the proposed value and the estimated value.
Broadcast2(p) ==
    /\ loc[p] = "prep"
    /\ Emit([type |-> "p2", val |-> prop[p], sender |-> p, est |-> estimate[p]])
    /\ loc' = "w2"
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, rcvd>>

\* Decide by majority on the agreed-upon estimated value.
DecideMajority(p) ==
    /\ loc[p] = "w2"
    /\ \E s \in Values :
         /\ Cardinality({m \in Seen(p, "p2") : m.est = s}) >= N - T
         /\ decided' = [decided EXCEPT ![p] = s]
    /\ loc' = "done"
    /\ UNCHANGED <<view, prop, estimate, crashed, msgs, rcvd>>

\* If no estimated value reaches the majority, choose from what was actually seen.
ChooseAny(p) ==
    /\ loc[p] = "w2"
    /\ rcvd[p] = 1..N
    /\ \E s \in Values :
         /\ \A q \in 1..N : view[p][q] # Bottom => view[p][q] <= s
         /\ decided' = [decided EXCEPT ![p] = s]
    /\ loc' = "done"
    /\ UNCHANGED <<view, prop, estimate, crashed, msgs, rcvd>>

\* A process may silently crash; the bound on crashed processes is strict.
Crash(p) ==
    /\ crashed < F
    /\ loc[p] \notin {"done","crashed"}
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, prop, estimate, decided, msgs, rcvd>>

Next ==
    \/ \E p \in 1..N : Broadcast1(p)
    \/ \E p \in 1..N, m \in msgs : Receive1(p, m)
    \/ \E p \in 1..N : Prepare(p)
    \/ \E p \in 1..N : Broadcast2(p)
    \/ \E p \in 1..N : DecideMajority(p)
    \/ \E p \in 1..N : ChooseAny(p)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
    /\ \A p \in 1..N :
         /\ TRUE
         /\ WF_vars(\E m \in msgs : Receive1(p, m))
         /\ SF_vars(Prepare(p))
         /\ WF_vars(Broadcast2(p))
         /\ SF_vars(DecideMajority(p) \/ ChooseAny(p))

\* No value is ever decided unless some process actually proposed it.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : prop[q] = decided[p]

\* Two processes never disagree on the outcome of the consensus.
Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Every process either crashes or finishes.
Termination == <>(\A p \in 1..N : loc[p] \in {"done","crashed"})

\* Condition C1 (stated in the system description) guarantees termination.
C1Termination == (\E q \in 1..N : prop[q] = Max(Values)) => Termination

====