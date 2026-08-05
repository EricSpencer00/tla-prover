---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, ReachableDefs, ReachableProofLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "searching"

Expand(n) ==
  /\ pc = "searching"
  /\ frontier' = frontier \cup (Succ[n] \ marked)
  /\ pc' = "searching"
  /\ UNCHANGED <<marked>>

Mark(n) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ pc' = "searching"

Done ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == \E n \in Nodes: Expand(n) \/ Mark(n) \/ Done

Spec == Init /\ [][Next]_vars

FrontierInvariant ==
  /\ TypeOK
  /\ \A n \in marked: Succ[n] \subseteq (marked \cup frontier)

ReachableFromUnion ==
  reachableFrom(Root, marked) \cup reachableFrom(Root, frontier) = reachableFrom(Root, marked \cup frontier)

ReachableIsMarkedFrontier ==
  reachableFrom(Root, Nodes) = marked \cup reachableFrom(Root, frontier)

PartialCorrectness == (pc = "done") => (marked = reachableFrom(Root, Nodes))

INVARIANTS == {FrontierInvariant, ReachableFromUnion, ReachableIsMarkedFrontier}

PROPERTIES == {PartialCorrectness}
====