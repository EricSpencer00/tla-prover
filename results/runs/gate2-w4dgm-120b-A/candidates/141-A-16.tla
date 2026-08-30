---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc
vars == << visited, frontier, pc >>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The current node is added to visited and its successors are spooled into the
\* frontier, but it is NOT removed from the frontier (overlap allowed).
Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ visited' = IF n \in visited THEN visited ELSE visited \cup {n}
       /\ frontier' = frontier \cup Succ[n]
  /\ pc' = IF frontier' = {} THEN "done" else pc

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << visited, frontier >>

Next == Explore \/ Done

Spec == Init /\ [][Next]_vars

\* Every successor of a visited node is either already visited or still in flight.
Inv1 ==
  \A n \in visited : \A m \in Succ[n] : m \in visited \/ m \in frontier

\* The union of visited with the reachable fringe from the frontier is exactly the
\* reachable fringe from the visited/frotnier union.
Inv2 ==
  visited \cup {m \in Nodes : \E n \in frontier : m \in Succ[n]} =
    {m \in Nodes : \E n \in visited \cup frontier : m \in Succ[n]}

\* The fringe of the visited set is exactly the reachable set minus the visited
\* set, so no reachable node is omitted from visited.
Inv3 ==
  {m \in Nodes : \E n \in visited : m \in Succ[n]} = {m \in Nodes : m \notin visited /\ (\E p \in Nodes : m \in Succ[p] /\ p \in visited)}

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Termination == (pc = "running") ~> (pc = "done")

====