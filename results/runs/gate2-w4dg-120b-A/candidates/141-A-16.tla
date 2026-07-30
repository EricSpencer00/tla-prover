---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES visited, frontier, pc
vars == <<visited, frontier, pc>>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E x \in frontier :
       \/ /\ x \notin visited
           /\ visited' = visited \cup {x}
           /\ frontier' = frontier \cup Succ[x]
       \/ /\ x \in visited
           /\ frontier' = frontier \ {x}
           /\ visited' = visited
  /\ pc' = pc

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<visited, frontier>>

Next ==
  \/ Explore
  \/ Done

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Explore)
  /\ SF_vars(Done)

Inv1 ==
  \A x \in visited : Succ[x] \subseteq visited \cup frontier

Inv2 ==
  (visited \cup frontier) \cup {Root} = Nodes
    =>
      ((visited \cup frontier) \cup {Root})
        \cup {y \in Nodes : \E x \in visited \cup frontier : y \in Succ[x]}

Inv3 ==
  {y \in Nodes : \E x \in visited \cup frontier : y \in Succ[x]}
    \cup visited = {y \in Nodes : \E x \in visited \cup frontier : y \in Succ[x]}

PartialCorrectness ==
  frontier = {} => visited = {y \in Nodes : \E x \in visited \cup {Root} : y \in Succ[x]}

Termination ==
  \A n \in Nat : (\A x \in visited : x \in Nodes) => (visited = Nodes => frontier = {})
====