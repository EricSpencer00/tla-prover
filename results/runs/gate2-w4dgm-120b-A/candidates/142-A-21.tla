---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableAlgs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "marking", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "init"

Expand(n) ==
  /\ pc = "marking"
  /\ n \in marked
  /\ \E m \in nodes[n] : m \notin marked \cup frontier
  /\ frontier' = frontier \cup {m \in nodes[n] : m \notin marked \cup frontier}
  /\ UNCHANGED <<marked, pc>>

MarkFrontier ==
  /\ pc = "marking"
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = {}
  /\ UNCHANGED pc

StartMarking ==
  /\ pc = "init"
  /\ pc' = "marking"
  /\ UNCHANGED <<marked, frontier>>

Halt ==
  /\ pc = "marking"
  /\ frontier = {}
  /\ \A n \in marked : \E m \in nodes[n] : m \in marked
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Expand(n)
  \/ MarkFrontier
  \/ StartMarking
  \/ Halt

Spec == Init /\ [][Next]_vars

Invariants ==
  /\ TypeOK
  /\ \A n \in marked : nodes[n] \subseteq (marked \cup frontier)
  /\ marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)
  /\ ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

Properties ==
  /\ INVARIANTS Invariants
  /\ pc = "done" => marked = ReachableFrom({Root})

====