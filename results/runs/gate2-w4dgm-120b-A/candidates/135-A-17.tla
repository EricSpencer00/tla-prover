---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANT Nodes, Root, Succ

\* Configured for a finite, bounded state space: the graph is a concrete
\* 4-node ring where each node has 2 deterministic successors, and sequences
\* are cut off at the number of nodes. This is the model-checking
\* configuration overriding the unbounded version from the core algo spec.

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"active", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "active"

\* The algorithm marks one new reachable node per step, always making progress
\* toward covering the whole reachable set.
Step ==
    /\ pc = "active"
    /\ frontier # {}
    /\ frontier' = {}
    /\ marked' = marked \cup frontier
    /\ LET newFrontier == { y \in Nodes : \E x \in frontier : y \in Succ[x] } \ frontier
       IN frontier' = newFrontier
    /\ UNCHANGED pc

Done ==
    /\ pc = "active"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Reset ==
    /\ pc = "done"
    /\ pc' = "active"
    /\ frontier' = {Root}
    /\ marked' = {Root}

Next == Step \/ Done \/ Reset

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Inv1 == \A x \in marked : \E y \in frontier : x \in Succ[y]
Inv2 == \A x \in marked : \E y \in marked : x \in Succ[y]
Inv3 == \A x \in Nodes \ marked : \E y \in marked : x \in Succ[y]
PartialCorrectness == marked \subseteq Nodes

Termination == (pc = "active") ~> (pc = "done")

====