---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

Step ==
    \E n \in Nodes :
        /\ n \in marked
        /\ n \notin frontier
        /\ frontier' = frontier \cup {n}
        /\ UNCHANGED <<marked, pc>>

Mark ==
    \E n \in frontier :
        /\ frontier' = frontier \ {n}
        /\ marked' = marked \cup {n}
        /\ pc' = IF frontier \ {n} = {} THEN "term" ELSE "active"

Next == Step \/ Mark

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "active", "term"}
    /\ frontier \cap marked = {}
    /\ \A n \in marked, m \in Nodes : (n \in marked /\ Adj(n, m)) => (m \in marked \/ m \in frontier)

Inv1 == TypeOK

ReachableFromMarked == ReachableFrom(marked)

Inv2 == ReachableFromMarked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 == ReachableFrom({Root}) = ReachableFromMarked \cup ReachableFrom(frontier)

ReachableClaim == ReachableFrom({Root}) = marked

Properties == ReachableClaim
====