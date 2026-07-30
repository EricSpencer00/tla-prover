---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, ReachabilityLemmas, SequentialAlgorithm

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Begin ==
  /\ pc = "idle"
  /\ pc' = "running"
  /\ frontier' = {Root}
  /\ UNCHANGED marked

MarkFrontier ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E u \in frontier :
       /\ marked' = marked \cup {u}
       /\ frontier' = (frontier \ {u}) \cup {v \in Nodes : u \in marked /\ v \in frontier}
  /\ UNCHANGED pc

Finish ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Begin \/ MarkFrontier \/ Finish]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A u \in marked : \A v \in Nodes : (u = v) \/ (v \in marked \/ v \in frontier)

Invariant2 ==
  marked \cup Reachable(fringe) = Reachable(fringe \cup marked)

Invariant3 ==
  Reachable(Root) = marked \cup Reachable(fringe)

AllInvariantsHold == Invariant1 /\ Invariant2 /\ Invariant3

PartialCorrectness ==
  /\ pc = "done"
  /\ marked = Reachable(Root)

====