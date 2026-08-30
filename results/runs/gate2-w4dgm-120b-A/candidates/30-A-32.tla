---- MODULE cbc_max ----
EXTENDS Naturals, Sequences

CONSTANTS N, T, F, Values, Bottom

\* State variables: loc (control location per process), view (per-process
\* snapshot of every proposal), prop (each process's own proposal, chosen
\* from Values), est (the computed max per process), dec (the record of each
\* process's decision), crashed (count of failures so far), sent (all
\* broadcast messages), and rcvd (messages each process has consumed).
VARIABLES loc, view, prop, est, dec, crashed, sent, rcvd

Locs == {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choosing"}
Msgs == [type: {"p1", "p2"}, val: Values \cup {Bottom}, from: 1..N, ev: Values \cup {Bottom}]

TypeOK ==
    /\ loc \in [1..N -> Locs]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ dec \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Msgs
    /\ rcvd \in [1..N -> SUBSET Msgs]

Init ==
    /\ loc = [p \in 1..N |-> "bc1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ est = [p \in 1..N |-> Bottom]
    /\ dec = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ rcvd = [p \in 1..N |-> {}]

\* Phase 1: broadcast the proposed value.
Broadcast1(p) ==
    /\ loc[p] = "bc1"
    /\ sent' = sent \cup {[type |-> "p1", val |-> prop[p], from |-> p, ev |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "w1"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, rcvd>>

\* Phase 1: absorb an inbound message into the local view.
Receive1(p, m) ==
    /\ loc[p] = "w1"
    /\ m \in rcvd[p]
    /\ m.type = "p1"
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent, rcvd>>

\* Phase 1: once the view is sufficiently filled, compute the max and move
\* on to broadcast phase 2.
Start2(p) ==
    /\ loc[p] = "w1"
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
    /\ est' = [est EXCEPT ![p] = CHOOSE x \in Values :
                  \E q \in 1..N : view[p][q] = x /\ \A r \in 1..N : view[p][r] # Bottom => r <= x]
    /\ loc' = "prep"
    /\ UNCHANGED <<view, prop, dec, crashed, sent, rcvd>>

\* Phase 2: broadcast both the own proposal and the estimated max.
Broadcast2(p) ==
    /\ loc[p] = "prep"
    /\ sent' = sent \cup {[type |-> "p2", val |-> prop[p], from |-> p, ev |-> est[p]]}
    /\ loc' = [loc EXCEPT ![p] = "w2"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, rcvd>>

\* Phase 2: absorb an inbound message.
Receive2(p, m) ==
    /\ loc[p] = "w2"
    /\ m \in rcvd[p]
    /\ m.type = "p2"
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent, rcvd>>

\* Phase 2: decide once enough matching estimates have been seen.
Decide(p) ==
    /\ loc[p] = "w2"
    /\ crashed < F
    /\ \E v \in Values :
         /\ Cardinality({q \in 1..N : \E m \in rcvd[p] : m.type = "p2" /\ m.from = q /\ m.ev = v}) >= N - T
         /\ dec' = [dec EXCEPT ![p] = v]
    /\ loc' = "done"
    /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

\* Phase 2: no estimate reached the threshold; pick any seen value.
Choose(p) ==
    /\ loc[p] = "w2"
    /\ \A v \in Values :
         Cardinality({q \in 1..N : \E m \in rcvd[p] : m.type = "p2" /\ m.from = q /\ m.ev = v}) < N - T
    /\ \E v \in Values : \E q \in 1..N : view[p][q] = v /\ dec' = [dec EXCEPT ![p] = v]
    /\ loc' = "choosing"
    /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

\* A process decides outright (deterministic choice) in the choosing state.
DecideChosen(p) ==
    /\ loc[p] = "choosing"
    /\ loc' = "done"
    /\ UNCHANGED <<view, prop, est, dec, crashed, sent, rcvd>>

Crash(p) ==
    /\ loc[p] \in {"bc1", "w1", "prep", "bc2", "w2"}
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, prop, est, dec, sent, rcvd>>

Next ==
    \/ \E p \in 1..N : Broadcast1(p)
    \/ \E p \in 1..N, m \in Msgs : Receive1(p, m)
    \/ \E p \in 1..N : Start2(p)
    \/ \E p \in 1..N : Broadcast2(p)
    \/ \E p \in 1..N, m \in Msgs : Receive2(p, m)
    \/ \E p \in 1..N : Decide(p)
    \/ \E p \in 1..N : Choose(p)
    \/ \E p \in 1..N : DecideChosen(p)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_<<loc, view, prop, est, dec, crashed, sent, rcvd>>

\* Every decision made is backed by some process's own proposal.
Validity == \A p \in 1..N : dec[p] # Bottom => \E q \in 1..N : prop[q] = dec[p]

\* Two processes that both decide cannot pick different values.
Agreement == \A p, q \in 1..N : (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* Every live process eventually crashes or finishes.
Termination == \A p \in 1..N : (loc[p] \notin {"done", "crashed"}) ~> (loc[p] \in {"done", "crashed"})

\* Under Condition C1 (at least F+1 proposals equal the global max), the
\* protocol always terminates.
ConditionalTermination ==
    (Cardinality({p \in 1..N : \A q \in 1..N : prop[p] >= prop[q]}) >= F + 1) ~> (\A p \in 1..N : loc[p] \in {"done", "crashed"})

====