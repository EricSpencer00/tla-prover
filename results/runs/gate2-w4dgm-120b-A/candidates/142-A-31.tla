---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachabilityProofs, ReachableSearch

CONSTANTS Nodes, Root

\* The state is exactly the algorithm's state; the lemmas live in the
\* reachability module and are imported wholesale.
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"searching", "final"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "searching"

Explore(n) ==
  /\ pc = "searching"
  /\ n \in marked
  /\ n \notin frontier
  /\ frontier' = frontier \cup {n}
  /\ UNCHANGED <<marked, pc>>

Mark(n) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

BacktrackAll ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ \A n \in Nodes : n \in marked
  /\ pc' = "final"
  /\ UNCHANGED <<marked, frontier>>

Restart ==
  /\ pc = "final"
  /\ marked' = {Root}
  /\ frontier' = {}
  /\ pc' = "searching"

Next ==
  \/ \E n \in Nodes : Explore(n) \/ Mark(n)
  \/ BacktrackAll
  \/ Restart

Spec == Init /\ [][Next]_vars

\* Invariant 1 is the true inductive core; invariants 2-3 follow from the lemmas.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

\* Lemma 1 turns the frontier bookkeeping into a reachability identity.
Invariant2 == Lemma1(marked, frontier)

\* Lemmas 2 and 3 turn the frontier bookkeeping into an identity about the
\* reachable-from set itself, so the frontier can be swapped for reachable.
Invariant3 == Lemma2(marked, frontier) /\ Lemma3

Invariants == {Invariant1, Invariant2, Invariant3}

\* The partial correctness claim: termination coincides with having marked
\* exactly the reachable nodes.
TerminationMarkComplete == pc = "final" => marked = ReachFrom(Root)

Properties == {TerminationMarkComplete}

====