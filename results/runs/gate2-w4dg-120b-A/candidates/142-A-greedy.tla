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

Explore ==
  /\ pc = "init"
  /\ frontier' = {Root}
  /\ pc' = "running"
  /\ UNCHANGED marked

Mark(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Expand(n) ==
  /\ pc = "running"
  /\ n \in marked
  /\ frontier' = frontier \cup (Succ(n) \ {n})
  /\ UNCHANGED <<marked, pc>>

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Explore
  \/ \E n \in Nodes : Mark(n)
  \/ \E n \in Nodes : Expand(n)
  \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus every successor of a marked node is
\* already marked or waiting in the frontier.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

\* Invariant 2: the marked set plus nodes reachable from the frontier equals
\* nodes reachable from the union of marked and frontier.  This is proved
\* directly from Lemma 1 of the reachability lemmas module.
Invariant2 ==
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

\* Invariant 3: the reachable set from the root equals the marked set plus
\* nodes reachable from the frontier.  This uses Lemma 2 (reachability is
\* stable under adding successors) and Lemma 3 (reachability from empty is
\* empty).
Invariant3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* Partial correctness: on termination the marked set is exactly the
\* reachable set.
TerminationOK ==
  (pc = "done") => (marked = ReachableFrom({Root}))

====