---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc
vars == << visited, frontier, pc >>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

ReachFrom(s) ==
  { y \in Nodes : \E x \in s : y \in Succ[x] }

\* The frontier here may overlap visited; the successor case adds successors
\* without ever removing the explored node, which is what makes it parallelizable.
Step ==
  /\ frontier # {}
  /\ pc = "running"
  /\ \E x \in frontier :
       \/ /\ x \notin visited
          /\ visited' = visited \cup {x}
          /\ frontier' = frontier \cup ReachFrom({x})
       \/ /\ x \in visited
          /\ frontier' = frontier \ {x}
          /\ visited' = visited
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED << visited, frontier >>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars

\* A node is reachable from the root exactly when it is visited or reachable
\* from some frontier node -- the invariant that links the algorithm's progress
\* to the graph's reachability structure.
Inv1 == \A x \in visited : ReachFrom({x}) \subseteq visited \cup frontier

Inv2 == ReachFrom(visited \cup frontier)
          = ReachFrom(visited) \cup ReachFrom(frontier)

Inv3 == ReachFrom({Root}) = visited \cup ReachFrom(frontier)

PartialCorrectness == pc = "done" => visited = ReachFrom({Root})

Termination == visited \cup frontier = ReachFrom({Root}) ~> frontier = {}

====