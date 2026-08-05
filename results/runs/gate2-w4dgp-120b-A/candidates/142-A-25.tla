---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "searching"

Explored ==
  /\ frontier = {}
  /\ pc = "done"
  /\ marked = Nodes
  /\ UNCHANGED <<marked, frontier, pc>>

ExploreStep ==
  /\ pc = "searching"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup (Succ(n) \ marked)
  /\ UNCHANGED pc

SearchStep ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ marked # Nodes
  /\ frontier' = {n \in Nodes : \E m \in marked : n \in Succ(m)}
  /\ pc' = "searching"
  /\ UNCHANGED marked

FinishStep ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ marked = Nodes
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explored \/ ExploreStep \/ SearchStep \/ FinishStep

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 ==
  reachableFrom(Root, marked) \cup reachableFrom(Root, frontier) = reachableFrom(Root, marked \cup frontier)

Invariant3 ==
  reachableFrom(Root, Nodes) = marked \cup reachableFrom(Root, frontier)

TerminationPartialCorrectness == (pc = "done") => (marked = reachableFrom(Root, Nodes))

====