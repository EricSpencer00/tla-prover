---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "search", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "init"

InitStep ==
  /\ pc = "init"
  /\ pc' = "search"
  /\ UNCHANGED <<marked, frontier>>

ExpandStep ==
  /\ pc = "search"
  /\ frontier = {}
  /\ \E n \in marked :
       frontier' = {m \in Nodes : Edge(n, m)}
  /\ UNCHANGED <<marked, pc>>

MarkStep ==
  /\ pc = "search"
  /\ frontier # {}
  /\ \E n \in frontier :
       marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

DoneStep ==
  /\ pc = "search"
  /\ frontier = {}
  /\ \A n \in marked : \A m \in Nodes : Edge(n, m) => m \in marked
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == InitStep \/ ExpandStep \/ MarkStep \/ DoneStep

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : \A m \in Nodes : Edge(n, m) => m \in marked \/ m \in frontier

Invariant2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
  ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

PartialCorrectness == (pc = "done") => (marked = ReachableFrom(Root))

====