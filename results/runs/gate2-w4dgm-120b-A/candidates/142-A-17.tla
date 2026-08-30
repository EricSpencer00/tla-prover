---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableAlgs

CONSTANTS Nodes, Root

Vars == <<marked, frontier, pc>>

Spec == Init /\ [][Step]_Vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "active", "done"}

SuccessorClosed ==
  \A n \in marked : \A m \in Nodes : (n \in marked /\ Edge(n, m)) => (m \in marked \/ m \in frontier)

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

Step ==
  /\ pc # "done"
  /\ (pc' = IF pc = "idle" THEN "active" ELSE IF pc = "active" THEN "done" ELSE "idle")
  /\ UNCHANGED <<marked, frontier>>

Invariant1 == TypeOK /\ SuccessorClosed

Invariant2 == (marked \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

TerminationIsPartial ==
  (pc = "done") => (ReachableFrom({Root}) = marked)

====