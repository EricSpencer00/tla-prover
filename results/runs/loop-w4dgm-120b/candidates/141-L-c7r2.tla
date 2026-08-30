---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ (n \notin visited /\ visited' = visited \cup {n} /\ frontier' = frontier \cup Succ[n])
       \/ (n \in visited /\ frontier' = frontier \ {n} /\ visited' = visited)
  /\ pc' = pc

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "terminated"
  /\ UNCHANGED <<visited, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

Inv1 ==
  \A n \in visited : Succ[n] \subseteq visited \cup frontier

Inv2 ==
  (visited \cup frontier) \cup {n \in Nodes : \E m \in visited \cup frontier : n \in Succ[m]} =
    visited \cup {n \in Nodes : \E m \in visited \cup frontier : n \in Succ[m]}

Inv3 ==
  {n \in Nodes : \E m \in visited : n \in Succ[m]} \cup visited = {n \in Nodes : \E m \in frontier : n \in Succ[m]}

PartialCorrectness ==
  visited = {n \in Nodes : \E m \in {Root} : n \in Succ[m]}

Termination ==
  frontier # {} ~> frontier = {}

====