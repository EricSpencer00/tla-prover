---- MODULE ReachableProofs ----
EXTENDS Integers, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Explore(n) ==
  /\ pc = "idle"
  /\ n \in marked \ frontier
  /\ frontier' = frontier \cup {n}
  /\ pc' = "exploring"
  /\ UNCHANGED marked

Mark(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = "idle"

Done ==
  /\ pc = "idle"
  /\ frontier = {}
  /\ \A n \in Nodes : n \in marked => \A m \in Nodes : Edge(n, m) => m \in marked
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ \E n \in Nodes : Mark(n)
  \/ Done

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked, m \in Nodes : Edge(n, m) => (m \in marked \/ m \in frontier)

Invariant2 ==
  (marked \cup Reachable(SinceFrontier)) = Reachable(marked \cup frontier)

Invariant3 ==
  Reachable(Nodes) = (marked \cup Reachable(SinceFrontier))

TerminationProperty ==
  pc = "done" => Reachable(Nodes) = marked

====