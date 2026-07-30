---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "init"

Explore ==
  /\ pc = "init"
  /\ \E n \in marked \ frontier :
       /\ frontier' = frontier \cup {n}
       /\ pc' = "explore"
  /\ UNCHANGED <<marked>>

Mark ==
  /\ pc = "explore"
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \ {n}
       /\ pc' = "init"

Done ==
  /\ pc = "init"
  /\ frontier = {}
  /\ \A n \in marked : ReachableFrom(n) \subseteq marked
  /\ pc' = "halt"
  /\ UNCHANGED <<marked, frontier>>

InitStep == Init
ExploreStep == Explore
MarkStep == Mark
DoneStep == Done

Next == InitStep \/ ExploreStep \/ MarkStep \/ DoneStep

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "explore", "halt"}

FrontierSuccessorsAreMarkedOrFrontier ==
  \A n \in marked : Successors(n) \subseteq (marked \cup frontier)

Invariant1 == TypeOK /\ FrontierSuccessorsAreMarkedOrFrontier

Invariant2 ==
  \A n \in marked \ frontier :
    ReachableFrom({n}) \subseteq (marked \cup frontier)

Invariant3 ==
  ReachableFrom(Root) = (marked \cup ReachableFrom(frontier))

PartialCorrectness ==
  /\ pc = "halt"
  /\ marked = ReachableFrom(Root)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness
====