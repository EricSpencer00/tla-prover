---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Succ is left free in the spec and is substituted to a finite bound by the
\* .cfg file; Reachable is the property, not an operator.
VARIABLES marked, frontier, pc

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"running", "done"}

Init == /\ marked = {}
        /\ frontier = {Root}
        /\ pc = "running"

\* Misra's twist: the frontier and the visited set may overlap, so the node
\* is never removed from the frontier when first discovered -- only later.
Explore == /\ frontier # {}
           /\ \E n \in frontier :
                /\ n \in marked
                /\ frontier' = frontier \ {n}
                /\ marked' = marked
           /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Discover == /\ frontier # {}
            /\ \E n \in frontier :
                 /\ n \notin marked
                 /\ marked' = marked \cup {n}
                 /\ frontier' = frontier \cup Succ[n]
            /\ pc' = "running"

Next == Explore \/ Discover

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Every neighbor of a visited node is either already visited or still to be
\* explored -- nothing reachable is ever lost to both.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The union of visited nodes and the nodes reachable from the current
\* frontier is exactly the set reachable from the union of the two.
Inv2 == (marked \cup frontier) \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* The reachable set is partitioned into the visited part and the frontier
\* part; when the frontier drains, the visited part is the whole reachable set.
Inv3 == Reachable(Nodes) = (marked \cup Reachable(frontier))

PartialCorrectness == Reachable(Nodes) = (marked \cup Reachable(frontier))

\* Exhaustion of the frontier is the only way out of the loop; with a finite
\* reachable set and weak fairness it happens.
Termination == (frontier # {}) ~> (frontier = {})

====