---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, ReachableAlgorithm, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

MarkReady ==
  {n \in Nodes : \E m \in marked : n \in succ[m]}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Step ==
  /\ pc # "done"
  /\ frontier # {}
  /\ LET s == UNION { succ[n] : n \in frontier } IN
       marked' = marked \cup frontier
       /\ frontier' = s \ MarkReady
  /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Spec == Init /\ [][Step]_vars

InductiveOK ==
  /\ TypeOK
  /\ frontier \subseteq MarkReady

Invariant2 ==
  marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Invariant3 ==
  Reachable({Root}) = marked \cup Reachable(frontier)

PartialCorrect ==
  (pc = "done") => (marked = Reachable({Root}))

INVARIANTS == InductiveOK /\ Invariant2 /\ Invariant3

PROPERTIES == PartialCorrect

====