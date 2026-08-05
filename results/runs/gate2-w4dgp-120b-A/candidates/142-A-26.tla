---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability

CONSTANT Nodes, Root

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Nodes \ {Root}
  /\ pc = "exploring"

ExploreStep ==
  /\ pc = "exploring"
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \ {n}
  /\ pc' = "exploring"

Done ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

Init == Init /\ UNCHANGED << marked, frontier, pc >>  \* Include the unused Init name in the signature
InitStep == Init \/ ExploreStep \/ Done

Spec == Init /\ [][InitStep]_vars

AdjoiningMarked ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

MarkClosure ==
  ReachableFrom[marked] \cup ReachableFrom[frontier] = ReachableFrom[marked \cup frontier]

ExploreComplete ==
  ReachableFrom[Root] = marked \cup ReachableFrom[frontier]

SpecComplete == Spec /\ (\A n \in Nodes : n \in ReachableFrom[Root] <=> n \in marked)
====