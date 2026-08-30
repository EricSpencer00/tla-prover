---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Operators that the .cfg file substitutes in, keeping their names on the
\* left and defining the operators on the right.
ConnectedToSomeButNotAll == Succ

FiniteSeq == LimitedSeq

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

\* Misra's twist: a marked node may linger in the frontier and be picked
\* again, which is what keeps the two sets overlapping.
Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ IF n \notin visited
       THEN /\ visited' = visited \cup {n}
            /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
       ELSE /\ visited' = visited
            /\ frontier' = frontier \ {n}
  /\ pc' = IF (frontier \cup ConnectedToSomeButNotAll[n]) = {}
            THEN "done"
            ELSE "running"

Next == \E n \in Nodes: Explore(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in visited : ConnectedToSomeButNotAll[n] \subseteq (visited \cup frontier)

Inv2 ==
  (visited \cup frontier) = Nodes

Inv3 ==
  Nodes \ visited = frontier

PartialCorrectness ==
  (pc = "done") => (visited = Nodes)

Termination ==
  \A n \in Nodes : WF_vars(Explore(n))

====