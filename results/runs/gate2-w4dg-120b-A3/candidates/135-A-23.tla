---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Bump(pc) == IF pc < 4 THEN pc + 1 ELSE 4

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = 0

Explore(n) ==
    /\ n \in frontier
    /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
    /\ marked' = marked \cup Succ[n]
    /\ pc' = Bump(pc)

Final == marked = Nodes

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ (Final /\ pc' = Bump(pc) /\ UNCHANGED <<marked, frontier>>)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in 0..4

Inv1 ==
    \A n \in marked : \E m \in frontier : n \in Succ[m]

Inv2 ==
    \A n \in marked : (marked \ {n}) \cup frontier = marked

Inv3 ==
    marked = frontier

PartialCorrectness ==
    Final => marked = Nodes

Termination ==
    <>(pc = 4)

====