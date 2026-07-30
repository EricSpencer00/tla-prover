---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes, Root

VARIABLES
    marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    LET loop[T \in SUBSET Nodes] ==
        IF \E n \in Nodes : n \in S /\ n \notin T
        THEN LET x == CHOOSE n \in Nodes : n \in S /\ n \notin T
                 MayReach(y) == y \in marked \/ y \in frontier \/ y \in S
             IN loop[T \cup {x} \cup {y \in Nodes : MayReach(y)}]
        ELSE T
    IN loop[*][{}]

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

ExpandFrontier ==
    /\ frontier = {}
    /\ pc = "idle"
    /\ frontier' = {n \in Nodes : n \notin marked}
    /\ pc' = "expanding"
    /\ UNCHANGED marked

MarkNode ==
    /\ pc = "expanding"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

Finish ==
    /\ pc = "expanding"
    /\ frontier = {}
    /\ pc' = "idle"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ ExpandFrontier
    \/ MarkNode
    \/ Finish

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "expanding"}
    /\ \A n \in marked : \A m \in Nodes : (m \in frontier \/ m \in marked) \/ (n # Root => TRUE)

Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : \E m \in Nodes : (m \in frontier \/ m \in marked) => TRUE

Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == pc = "idle" => marked = ReachableFrom({Root})

INVARIANTS == Inv1 /\ Inv2 /\ Inv3
PROPERTIES == PartialCorrectness
====