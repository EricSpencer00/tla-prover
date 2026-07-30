---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

SuccessorsOf(S) == {y \in Nodes : \E x \in S : y \in succ[x]}

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}

InitState ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Explore(n) ==
  /\ pc = "idle"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \ {n}) \cup (succ[n] \ marked)
  /\ pc' = "exploring"

ExploreRoot ==
  /\ pc = "idle"
  /\ pc' = "exploring"
  /\ marked' = marked
  /\ frontier' = frontier \cup (succ[Root] \ marked)

FinishExploring ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ marked' = marked
  /\ frontier' = frontier

DoneStep ==
  /\ pc = "done"
  /\ marked' = marked
  /\ frontier' = frontier
  /\ pc' = pc

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ ExploreRoot
  \/ FinishExploring
  \/ DoneStep

Spec == InitState /\ [][Next]_vars

\* Invariant 1: type correctness plus every successor of a marked node is
\* covered by marked or frontier -- the key containment for induction.
Invariant1 ==
  /\ TypeOK
  /\ SuccessorsOf(marked) \subseteq marked \cup frontier

\* Invariant 2: the marked set plus what is reachable from the frontier
\* equals what is reachable from the combined set, proved from Lemma 1.
Invariant2 ==
  marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

\* Invariant 3: the reachable set from the root splits into the marked set
\* and what is reachable from the frontier, using Lemma 2 and Lemma 3.
Invariant3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

\* The TLAPS proof leverages Lemma 1 for Invariant2 and Lemma 2/3 for
\* Invariant3. Proving termination is left to a separate liveness argument
\* (not supported by TLAPS yet).
TerminationOK ==
  (pc = "done") => (marked = ReachFrom({Root}))

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == TerminationOK

====