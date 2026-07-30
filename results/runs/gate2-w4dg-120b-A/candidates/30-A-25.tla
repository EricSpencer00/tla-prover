---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Each process keeps a local view of every other process's value (filled
\* with a special bottom initially); the max of that view is its estimate.
Views == [N -> [N -> Values \cup {Bottom}]]

VARIABLES loc, view, prop, est, decision, crashed, sent, recvd

Message == [type: {"phase1", "phase2"}, val: Values \cup {Bottom}, sender: 1..N, est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [1..N -> {"p1b", "p1w", "prep", "p2b", "p2w", "done", "crashed", "choosing"}]
  /\ view \in Views
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Message
  /\ recvd \in [1..N -> SUBSET Message]

Init ==
  /\ loc = [p \in 1..N |-> "p1b"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [p \in 1..N |-> CHOOSE v \in Values : TRUE]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvd = [p \in 1..N |-> {}]

\* Phase 1 broadcast: proposals announced to the whole system.
Broadcast1(p) ==
  /\ loc[p] = "p1b"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], sender |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "p1w"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recvd>>

\* Phase 1 receive: update the local view with the sender's proposed value.
Deliver1(p, m) ==
  /\ loc[p] = "p1w"
  /\ m.type = "phase1"
  /\ m \notin recvd[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

\* Phase 1 to Phase 2: estimate is the max of what this process has seen.
Compute(p) ==
  /\ loc[p] = "p1w"
  /\ Cardinality({m \in recvd[p] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE_MAX({view[p][q] : q \in 1..N})]
  /\ loc' = [loc EXCEPT ![p] = "p2b"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recvd>>

Broadcast2(p) ==
  /\ loc[p] = "p2b"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], sender |-> p, est |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "p2w"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recvd>>

\* Phase 2 receive: update the local view with the sender's estimate.
Deliver2(p, m) ==
  /\ loc[p] = "p2w"
  /\ m.type = "phase2"
  /\ m \notin recvd[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.est]
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

\* Decision when a strong majority (N-T) agrees on one estimate value.
Decide(p) ==
  /\ loc[p] = "p2w"
  /\ \E v \in Values :
       /\ Cardinality({m \in recvd[p] : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recvd>>

\* When no single estimate reaches the threshold, pick deterministically from
\* the view (guaranteeing progress without further messages).
Choose(p) ==
  /\ loc[p] = "p2w"
  /\ \A v \in Values : Cardinality({m \in recvd[p] : m.type = "phase2" /\ m.est = v}) < N - T
  /\ decision' = [decision EXCEPT ![p] = CHOOSE({view[p][q] : q \in 1..N})]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recvd>>

Crash(p) ==
  /\ crashed < F
  /\ loc[p] \notin {"done", "crashed"}
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, prop, est, decision, sent, recvd>>

Next ==
  \E p \in 1..N :
    \/ Broadcast1(p) \/ Compute(p) \/ Broadcast2(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
    \/ (\E m \in Message : Deliver1(p, m) \/ Deliver2(p, m))

Spec ==
  /\ Init
  /\ [][Next]_<<loc, view, prop, est, decision, crashed, sent, recvd>>
  /\ TRUE

\* Every decision is backed by some process's original proposal.
Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in {prop[q] : q \in 1..N}

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

\* Condition C1: enough processes propose the global maximum to force
\* termination (the paper's sufficient condition).
AssumeC1 == {p \in 1..N : prop[p] = CHOOSE_MAX(Values)} >= F + 1
Conditional == (AssumeC1 => Termination)

====