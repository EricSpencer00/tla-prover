---- MODULE ReachableProofs ----
EXTENDS ReachAlg, ReachProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "working"

Mark(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ UNCHANGED pc

Explore(n, m) ==
  /\ pc = "working"
  /\ n \in marked
  /\ m \notin marked
  /\ m \notin frontier
  /\ frontier' = frontier \cup {m}
  /\ UNCHANGED <<marked, pc>>

Stall ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "stalled"
  /\ UNCHANGED <<marked, frontier>>

Halt ==
  /\ pc = "working"
  /\ frontier = {}
  /\ \A n \in frontier: n \in marked
  /\ pc' = "halted"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes: Mark(n)
  \/ \E n \in Nodes, m \in Nodes: Explore(n, m)
  \/ Stall
  \/ Halt

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", "stalled", "halted"}
  /\ \A n \in marked: frontier \cup marked \subseteq reachableFrom(n)

ReachExpands ==
  reachableFrom(marked \cup frontier) = reachableFrom(marked) \cup reachableFrom(frontier)

ReachDecompose ==
  reachableFrom(Root) = marked \cup reachableFrom(frontier)

PartialCorrectness ==
  /\ pc = "halted"
  => marked = reachableFrom(Root)

INVARIANTS == TypeOK /\ ReachExpands /\ ReachDecompose
PROPERTIES == PartialCorrectness
====