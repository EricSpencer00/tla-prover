---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE
         IN ReachableFrom(S \ {x}) \cup {x} \cup (IF x \in Nodes THEN Edges[x] ELSE {})

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = 0

ExpandFrontier(n) ==
    /\ pc = 0
    /\ n \in marked \ frontier
    /\ frontier' = frontier \cup {n}
    /\ pc' = 1
    /\ UNCHANGED marked

GrowFrontier ==
    /\ pc = 1
    /\ frontier # {}
    /\ \E m \in frontier :
        /\ marked' = marked \cup {m}
        /\ frontier' = frontier \ {m}
    /\ UNCHANGED pc

Done ==
    /\ frontier = {}
    /\ pc = 0
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : ExpandFrontier(n)
    \/ GrowFrontier
    \/ Done

Spec == Init /\ [][Next]_vars

Partial ==
    /\ frontier = {}
    /\ marked = ReachableFrom({Root})

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {0, 1}

Closure ==
    /\ \A n \in marked : Edges[n] \subseteq marked \cup frontier
    /\ \A n \in Nodes : Edges[n] \subseteq Nodes

Invariant1 == TypeOK /\ Closure

Invariant2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == Partial

====