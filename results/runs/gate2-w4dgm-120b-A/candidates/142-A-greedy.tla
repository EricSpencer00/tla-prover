---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableAlgs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Mark(n) ==
  /\ pc = "idle"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = "working"

Explore(n) ==
  /\ pc = "working"
  /\ frontier' = frontier \cup {m \in Nodes : m \notin marked /\ m \notin frontier /\ n \in Succ(m)}
  /\ pc' = "idle"
  /\ UNCHANGED marked

Finish ==
  /\ pc = "idle"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Mark(n)
  \/ \E n \in Nodes : Explore(n)
  \/ Finish

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == (pc = "done") => (marked = ReachableFrom({Root}))

====