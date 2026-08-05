---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability
CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeInv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "search", "done"}
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)
  /\ \A n \in frontier : Succ(n) \subseteq (marked \cup frontier)

Init ==
  /\ marked = {Root}
  /\ frontier = Succ(Root)
  /\ pc = "search"

Expand(n) ==
  /\ n \in frontier
  /\ frontier' = (frontier \ {n}) \cup Succ(n)
  /\ marked' = marked \cup {n}
  /\ pc' = pc

Finish ==
  /\ pc = "search"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

InitStep == Init
ExpandStep == \E n \in frontier : Expand(n)
Next == InitStep \/ ExpandStep \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(ExpandStep) /\ WF_vars(Finish)

Invariant2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
  ReachableFrom(Root) = marked \cup ReachableFrom(frontier)
====