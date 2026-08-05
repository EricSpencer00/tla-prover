---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ frontier \cap marked = {}
  /\ pc \in {"search", "finished"}

Succ(n) == {m \in Nodes : <<n, m>> \in Edges}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ(Root)
  /\ pc = "search"

Expand(n) ==
  /\ pc = "search"
  /\ n \notin marked
  /\ (marked' = marked \cup {n})
  /\ frontier' = (frontier \cup Succ(n)) \ {n}
  /\ UNCHANGED pc

Finish ==
  /\ pc = "search"
  /\ frontier = {}
  /\ pc' = "finished"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_vars
Next == \E n \in Nodes : Expand(n) \/ Finish

Inductive ==
  TypeOK /\ \A n \in Nodes : n \in marked => Succ(n) \subseteq (marked \cup frontier)

Invariant2 == marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Invariant3 == Reachable(Root) = marked \cup Reachable(frontier)

PartialCorrectness == pc = "finished" => Reachable(Root) = marked

====