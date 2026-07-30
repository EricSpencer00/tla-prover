---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

Run ==
  /\ \E n \in frontier :
       \/ (n \notin visited /\ visited' = visited \cup {n} /\ frontier' = frontier \cup Succ[n])
       \/ (n \in visited /\ frontier' = frontier \ {n})
  /\ pc' = pc

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<visited, frontier>>

Next == Run \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Run)

Inv1 ==
  \A n \in visited : Succ[n] \subseteq (visited \cup frontier)

Inv2 ==
  (visited \cup frontier) \subseteq (visited \cup (Seq @@ (visited \cup frontier)))

Inv3 ==
  (Nodes \ visited) \subseteq (Nodes \ (visited \cup frontier))

PartialCorrectness ==
  visited \cup (Seq @@ frontier) = Nodes

Termination == (frontier # {}) ~> (frontier = {})

====