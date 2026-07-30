---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, ReachableImpl
CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "running"

Explore ==
    /\ pc = "running"
    /\ \E n \in (marked \cup frontier) \ {Root} :
         /\ n \notin frontier
         /\ frontier' = frontier \cup {n}
    /\ UNCHANGED <<marked, pc>>

Mark ==
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

Done ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Mark \/ Done
Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A m \in marked : Succ(m) \subseteq (marked \cup frontier)

Invariant2 ==
    (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

Invariant3 ==
    ReachFrom(Root) = (marked \cup ReachFrom(frontier))

PartialCorrectness == (pc = "done") => (marked = ReachFrom(Root))

====