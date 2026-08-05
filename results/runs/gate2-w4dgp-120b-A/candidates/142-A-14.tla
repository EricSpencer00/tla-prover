---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "spanning"

Explore(n) ==
  /\ pc = "spanning"
  /\ n \in marked
  /\ frontier' = frontier \cup {n}
  /\ pc' = "exploring"
  /\ UNCHANGED marked

Mark(m) ==
  /\ pc = "exploring"
  /\ m \in frontier
  /\ frontier' = frontier \ {m}
  /\ marked' = marked \cup {m}
  /\ pc' = "spanning"

Done ==
  /\ pc # "done"
  /\ frontier = {}
  /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ \E m \in Nodes : Mark(m)
  \/ Done

Spec == Init /\ [][Next]_vars

InvariantType ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"spanning", "exploring", "done"}
  /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier

InvariantFrontierInclusion ==
  marked \cup Reachability.ReachableFrom(Nodes, frontier) = Reachability.ReachableFrom(Nodes, marked \cup frontier)

InvariantReachesExactly ==
  Reachability.ReachableFrom(Nodes, {Root}) = marked \cup Reachability.ReachableFrom(Nodes, frontier)

PartialCorrect == pc = "done" => marked = Reachability.ReachableFrom(Nodes, {Root})

INVARIANT InvariantType
INVARIANT InvariantFrontierInclusion
INVARIANT InvariantReachesExactly
PROPERTY PartialCorrect
====