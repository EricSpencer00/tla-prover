---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "halted"}

Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Misra's variant: visited and frontier may overlap, so a marked node can
\* still be picked from the frontier and simply removed.
Explore ==
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ frontier' = frontier \ {n}
         /\ IF n \notin visited
              THEN visited' = visited \cup {n} \cup Succ[n]
                   /\ frontier' = frontier' \cup Succ[n]
              ELSE visited' = visited
    /\ pc' = IF frontier' = {} THEN "halted" ELSE "running"

Next == Explore

Spec == Init /\ [][Next]_vars

\* Every successor of a visited node is either visited or still in the frontier.
Inv1 ==
    \A n \in visited : Succ[n] \subseteq visited \cup frontier

\* Adding the frontier spreads no new reachability beyond adding the frontier.
Inv2 ==
    (visited \cup frontier) \cup (VisitedReachable \cup FrontierReachable) =
        VisitedReachable \cup FrontierReachable

\* Reachable-from-root = visited plus whatever the frontier can still reach.
Inv3 ==
    (VisitedReachable \cup FrontierReachable) = VisitedReachable

VisitedReachable == {n \in Nodes : \E m \in visited : n \in Succ[m] \cup {m}}
FrontierReachable == {n \in Nodes : \E m \in frontier : n \in Succ[m] \cup {m}}

PartialCorrectness ==
    visited \cup (VisitedReachable \cup FrontierReachable) = VisitedReachable

Termination == (VisitedReachable # {}) ~> (VisitedReachable = {})

====