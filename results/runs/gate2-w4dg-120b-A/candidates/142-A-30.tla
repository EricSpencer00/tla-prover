---- MODULE ReachableProofs ----
EXTENDS Naturals, Reaches

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "run"

Step ==
    /\ pc = "run"
    /\ \E n \in frontier :
         marked' = marked \cup {n}
         /\ frontier' = (frontier \ {n})
         /\ frontier' = frontier' \cup (Succ(n) \ {n})
    /\ UNCHANGED pc

Quiesce ==
    /\ pc = "run"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Step
    \/ Quiesce

Spec ==
    /\ Init
    /\ [][Next]_vars

Inv1 ==
    TypeOK
    /\ \A m \in marked : Succ(m) \subseteq (marked \cup frontier)

Inv2 ==
    marked \cup Reaches(frontier) = Reaches(marked \cup frontier)

Inv3 ==
    Reaches(Root) = marked \cup Reaches(frontier)

THEOREM PartialCorrect ==
    (pc = "done") => (marked = Reaches(Root))

====