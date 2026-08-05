---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ

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

Explore(n) ==
    /\ n \in frontier
    /\ IF n \notin visited
       THEN /\ visited' = visited \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ frontier' = frontier \ {n}
            /\ visited' = visited
    /\ UNCHANGED pc

Terminated ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<visited, frontier>>

Next ==
    /\ pc = "running"
    /\ \E n \in frontier : Explore(n)
    \/ Terminated

ReachableFrom(S) == {y \in Nodes : \E x \in S : y \in Succ[x]}

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A m \in visited : Succ[m] \subseteq (visited \cup frontier)

Inv2 ==
    ReachableFrom(visited) \cup ReachableFrom(frontier) = ReachableFrom(visited \cup frontier)

Inv3 ==
    ReachableFrom({Root}) = visited \cup ReachableFrom(frontier)

PartialCorrectness ==
    pc = "done" => visited = ReachableFrom({Root})

Termination ==
    /\ frontier # {}
    /\ WF_vars(Explore(CHOOSE n \in frontier : TRUE))

====