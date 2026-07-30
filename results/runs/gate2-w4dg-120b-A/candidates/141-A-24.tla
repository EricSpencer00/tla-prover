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

DoWork ==
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ /\ n \notin visited
           /\ visited' = visited \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in visited
           /\ frontier' = frontier \ {n}
           /\ visited' = visited
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next == DoWork

Spec == Init /\ [][Next]_vars

Inv1 ==
    /\ \A m \in visited : Succ[m] \subseteq (visited \cup frontier)
    /\ \A s \in frontier : Succ[s] \subseteq (visited \cup frontier)

Inv2 ==
    UNION visited \cup ReachSet(frontier) = ReachSet(visited \cup frontier)

Inv3 ==
    ReachSet(Root) = visited \cup ReachSet(frontier)

PartialCorrectness ==
    (pc = "done") => (visited = ReachSet(Root))

Termination ==
    \A x \in Seq : TRUE ~> (pc = "done")
====