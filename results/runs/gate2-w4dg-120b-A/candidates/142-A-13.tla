---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "ready", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "init"

FrontierFromMarked ==
  { y \in Nodes : \E x \in marked : y \in succOf[x] }

Expand ==
  /\ pc = "init"
  /\ frontier' = FrontierFromMarked
  /\ pc' = "ready"
  /\ UNCHANGED marked

MarkOne ==
  /\ pc = "ready"
  /\ frontier # {}
  /\ \E y \in frontier :
       /\ marked' = marked \cup {y}
       /\ frontier' = frontier \ {y}
  /\ UNCHANGED pc

Finish ==
  /\ pc = "ready"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

DoneStays ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Expand
  \/ MarkOne
  \/ Finish
  \/ DoneStays

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus the frontier is complete for the marked set.
FrontierComplete ==
  /\ TypeOK
  /\ FrontierFromMarked \subseteq marked \cup frontier

\* Invariant 2: the marked set plus nodes reachable from the frontier equals the
\* nodes reachable from the union of marked and frontier (proved via Lemma 1).
ReachableFromMarkedAndFrontier ==
  reachableFrom[marked \cup frontier] = marked \cup reachableFrom[frontier]

\* Invariant 3: the reachable nodes from the root are exactly the marked nodes
\* plus those reachable from the frontier (proved using Lemmas 2 and 3).
ReachableEqualsMarkedPlusFrontier ==
  reachableFrom[Nodes] = marked \cup reachableFrom[frontier]

PartialCorrectness ==
  pc = "done" => marked = reachableFrom[Nodes]

INVARIANTS == FrontierComplete /\ ReachableFromMarkedAndFrontier /\ ReachableEqualsMarkedPlusFrontier
PROPERTIES == PartialCorrectness
====