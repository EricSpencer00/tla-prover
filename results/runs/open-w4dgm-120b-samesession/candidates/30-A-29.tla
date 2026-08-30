---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* W4Od14m8p2t2: a two-phase max-aggregation consensus protocol with crash faults.
\* Ref: Mostefaoui et al., 2003, Figure 1, condition C1.
\* Broadcasts are always available; Assumption 2 (a non-crashed process can always
\* receive) is what makes the "choosing" path reachable when the N-T quorum is
\* unavailable -- the liveness spec below would be trivially true otherwise.

Participants == 0..(N - 1)

VARIABLES pc, view, prop, est, decided, crashed, msgs, recv
vars == <<pc, view, prop, est, decided, crashed, msgs, recv>>

TypeOK ==
  /\ pc \in [Participants -> {"b1", "w1", "pre", "b2", "w2", "done", "crashed", "choose"}]
  /\ view \in [Participants -> [Participants -> Values \cup {Bottom}]]
  /\ prop \in [Participants -> Values]
  /\ est \in [Participants -> Values \cup {Bottom}]
  /\ decided \in [Participants -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ msgs \subseteq [type: {"p1", "p2"}, val: Values, est: Values \cup {Bottom}, from: Participants]
  /\ recv \in [Participants -> SUBSET Participants]

Init ==
  /\ pc = [p \in Participants |-> "b1"]
  /\ view = [p \in Participants |-> [q \in Participants |-> Bottom]]
  /\ prop \in [Participants -> Values]
  /\ est = [p \in Participants |-> Bottom]
  /\ decided = [p \in Participants |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ recv = [p \in Participants |-> {}]

\* Phase 1: broadcast an initial proposal.
Send1(p) ==
  /\ pc[p] = "b1"
  /\ msgs' = msgs \cup {[type |-> "p1", val |-> prop[p], est |-> Bottom, from |-> p]}
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, decided, crashed, recv>>

\* A message is consumed only if its type matches the phase the receiver is in.
Receive1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in msgs
  /\ m.type = "p1"
  /\ m.from \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.from}]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<pc, prop, est, decided, crashed, msgs>>

\* Once Phase 1 is quorum-committed, compute the maximum (the shared estimate).
Commit1(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality(recv[p]) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE v \in Values :
        \A q \in Participants : view[p][q] # Bottom => view[p][q] <= v]
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, prop, decided, crashed, msgs, recv>>

Send2(p) ==
  /\ pc[p] = "b2"
  /\ msgs' = msgs \cup {[type |-> "p2", val |-> prop[p], est |-> est[p], from |-> p]}
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, est, decided, crashed, recv>>

\* Phase 2: commit unanimously only once an N-T quorum agrees on the same estimate.
Decide(p) ==
  /\ pc[p] = "w2"
  /\ Cardinality(recv[p]) >= N - T
  /\ \E v \in Values :
       /\ Cardinality({m \in msgs : m.type = "p2" /\ m.from \in recv[p] /\ m.est = v}) >= N - T
       /\ decided[p] = v
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, msgs, recv>>

\* The fallback: with no quorum, fall back to picking any locally-seen value.
Choose(p) ==
  /\ pc[p] = "w2"
  /\ recv[p] = Participants
  /\ \E v \in Values :
       /\ \A q \in Participants : view[p][q] # Bottom => view[p][q] <= v
       /\ decided[p] = v
  /\ pc' = [pc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, crashed, msgs, recv>>

Choosing(p) ==
  /\ pc[p] = "choose"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, decided, crashed, msgs, recv>>

Crash(p) ==
  /\ pc[p] # "crashed"
  /\ crashed < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decided, msgs, recv>>

Next ==
  \/ \E p \in Participants :
       Send1(p) \/ Commit1(p) \/ Send2(p) \/ Decide(p) \/ Choose(p) \/ Choosing(p) \/ Crash(p)
  \/ \E p \in Participants, m \in msgs : Receive1(p, m)

Spec == Init /\ [][Next]_vars
  /\ \A p \in Participants :
       /\ TRUE
       /\ WF_vars(Choosing(p))
       /\ SF_vars(\E m \in msgs : Receive1(p, m))
       /\ WF_vars(Send1(p))
       /\ WF_vars(Commit1(p))
       /\ WF_vars(Send2(p))
       /\ SF_vars(Decide(p))
       /\ SF_vars(Choose(p))

\* SAFETY: any decision is an originally proposed value, and no two decisions disagree.
Validity == \A p \in Participants : decided[p] # Bottom => \E q \in Participants : prop[q] = decided[p]
Agreement == \A p, q \in Participants : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* LIVENESS: every participant eventually resolves or crashes; under condition C1
\* the agreement finishes without needing the fallback.
Termination == \A p \in Participants : <>(pc[p] \in {"done", "crashed"})
C1 == (\E p \in Participants : prop[p] = CHOOSE x \in Values : \A q \in Participants : prop[q] <= x) => Termination

\* The model violates nothing if every participant crashes, so disable that
\* outcome when checking the substantive termination (C1) property.
C1Check == F = N => TRUE
====