---- MODULE ReachableProofs ----
EXTENDS Integers, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "frontierEmpty"

Explore(n) ==
    /\ frontier = {}
    /\ frontier' = {n}
    /\ pc' = "expandingFrontier"
    /\ UNCHANGED marked

Visit(n) ==
    /\ pc = "expandingFrontier"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ pc' = IF frontier = {n} THEN "frontierEmpty" ELSE "expandingFrontier"

Grow(n) ==
    /\ pc = "expandingFrontier"
    /\ n \in frontier
    /\ frontier' = frontier \cup {n}
    /\ UNCHANGED <<marked, pc>>

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ \E n \in Nodes : Visit(n)
    \/ \E n \in Nodes : Grow(n)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"frontierEmpty", "expandingFrontier"}

ReachableViaMarked ==
    \A n \in marked : \A m \in Nodes :
        (Edge(n, m) /\ m \notin marked) => m \in frontier

Invariant1 == TypeOK /\ ReachableViaMarked

Invariant2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

ReachabilityPartial == (pc = "frontierEmpty") ~> (marked = ReachableFrom(Root))

====