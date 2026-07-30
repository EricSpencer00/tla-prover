---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "init"

Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ(n)) \ {n}
  /\ UNCHANGED pc

Start ==
  /\ pc = "init"
  /\ pc' = "running"
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Start
  \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus every successor of a marked node is
\* already marked or waiting in the frontier.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

\* Invariant 2: the marked set plus nodes reachable from the frontier equals
\* the nodes reachable from the union of marked and frontier.  This is proved
\* as a direct consequence of Lemma 1 from ReachableLemmas.
Invariant2 ==
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

\* Invariant 3: the reachable set from the root equals the marked set plus
\* nodes reachable from the frontier.  This uses Lemma 2 (stability of
\* reachable-from under adding successors) and Lemma 3 (reachable from empty
\* is empty).
Invariant3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* The final theorem: partial correctness.  When the algorithm terminates,
\* the marked set equals the reachable set.
PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom({Root}))

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness
====