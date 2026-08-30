---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* The frontier and the visited set may overlap (it is not a queue), so
\* adding a node's successors never removes the node itself from the
\* frontier; it is only later pruned once marked.

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

ExploreFrontier ==
  \E n \in frontier :
    IF n \notin visited
      THEN /\ visited' = visited \cup {n}
           /\ frontier' = frontier \cup Succ[n]
           /\ pc' = IF (frontier \cup Succ[n]) = {}
                    THEN "done" ELSE pc
      ELSE /\ visited' = visited
           /\ frontier' = frontier \ {n}
           /\ pc' = IF frontier = {n} THEN "done" ELSE pc

Next == ExploreFrontier

Spec == Init /\ [][Next]_vars

\* Every successor of a marked node is already marked or still to explore.
Inv1 ==
  \A n \in Nodes :
    n \in visited => \A m \in Succ[n] : m \in visited \/ m \in frontier

\* The reachable set from the union of visited and frontier is exactly
\* visited plus whatever is reachable from frontier alone.
Inv2 ==
  \A S \subseteq Nodes :
    ReachFrom(Root, visited \cup S) = visited \cup ReachFrom(Root, S)

\* Reachability can be reconstructed from the frontier once visited is removed.
Inv3 ==
  ReachFrom(Root, Nodes) = visited \cup ReachFrom(Root, frontier)

PartialCorrectness == ReachFrom(Root, Nodes) = visited

Termination == (pc = "running") ~> (pc = "done")

\* The companion parallel module needs a bounded but otherwise unrestricted
\* successor set; this override of Seq makes it finite and checkable.
LimitedSeq(n) == n

\* The .cfg replaces Succ with a bounded version for larger graphs:
Succ == ConnectedToSomeButNotAll

====