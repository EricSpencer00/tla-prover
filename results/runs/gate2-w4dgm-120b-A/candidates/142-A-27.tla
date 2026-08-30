---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableAlgs

CONSTANTS Nodes, Root

Spec == Init /\ [][Step]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "halted"}

Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked : \A m \in succ[n] : m \in marked \/ m \in frontier

Invariant2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == (pc = "halted") => (marked = ReachableFrom({Root}))
====