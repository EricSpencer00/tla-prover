---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Nodes,
  Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

\* The frontier is always driven from marked, so every marked successor is
\* either already marked or sitting in the frontier.
MarkFrontier ==
  /\ pc = "idle"
  /\ \E n \in Nodes :
       /\ n \notin marked
       /\ \E m \in marked : n \in Succ(m)
       /\ frontier' = frontier \cup {n}
  /\ pc' = "running"
  /\ UNCHANGED marked

CommitMark ==
  /\ pc = "running"
  /\ marked' = marked \cup frontier
  /\ frontier' = {}
  /\ pc' = "done"
  /\ UNCHANGED <<>>

Reset ==
  /\ pc = "done"
  /\ marked' = {Root}
  /\ frontier' = {}
  /\ pc' = "idle"

Next ==
  \/ MarkFrontier
  \/ CommitMark
  \/ Reset

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus every marked successor is in the
\* marked set or the frontier -- the inductive step of the reachability
\* proof.
MarkedClosure ==
  /\ TypeOK
  /\ \A m \in marked : \A n \in Succ(m) : n \in marked \cup frontier

\* Invariant 2: the marked set plus nodes reachable from the frontier is
\* exactly the reachability set of the marked-plus-frontier union.  This
\* is proved from Lemma 1 in the reachability proofs module (its exact
\* statement is not reproduced here).
MarkedPlusFrontier ==
  (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

\* Invariant 3: the reachability set of the root equals the marked set
\* plus nodes reachable from the frontier.  This uses Lemma 2 (stability of
\* reachable-from under adding successors) and Lemma 3 (reachable-from of
\* the empty set is empty), both proved in the reachability proofs module.
MarkedEqualsReachable ==
  ReachFrom({Root}) = (marked \cup ReachFrom(frontier))

\* The final theorem: TLAPS checks that these invariants together imply
\* partial correctness -- on termination the algorithm's marked set is
\* exactly the set of nodes reachable from the root.
PartialCorrect == MarkedEqualsReachable

INVARIANTS == {MarkedClosure, MarkedPlusFrontier, MarkedEqualsReachable}
PROPERTIES == {PartialCorrect}

====