---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "start"

Search ==
  /\ pc = "start"
  /\ pc' = "searching"
  /\ UNCHANGED <<marked, frontier>>

ExploreStep(n) ==
  /\ pc = "searching"
  /\ n \in marked
  /\ \E s \in succ[n] :
       /\ s \notin marked
       /\ s \notin frontier
       /\ frontier' = frontier \cup {s}
  /\ UNCHANGED <<marked, pc>>

Mark(n) ==
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Done ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Search
  \/ \E n \in Nodes : ExploreStep(n)
  \/ \E n \in Nodes : Mark(n)
  \/ Done

Spec == Init /\ [][Next]_vars

Inv1 ==
  /\ TypeOK
  /\ \A m \in marked : succ[m] \subseteq (marked \cup frontier)

Inv2 ==
  /\ (marked \cup frontier) \cup Reachable(reachableFrom, frontier) = Reachable(reachableFrom, marked \cup frontier)
  /\ (marked \cup frontier) \cap Reachable(reachableFrom, frontier) = {}

Inv3 ==
  /\ Reachable(reachableFrom, {Root}) = marked \cup Reachable(reachableFrom, frontier)

PartialCorrectness == (pc = "done") => (marked = Reachable(reachableFrom, {Root}))

====