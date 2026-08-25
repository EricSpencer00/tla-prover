---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Reachability operator (transitive closure using the successor function)
\* ----------------------------------------------------------------------
RECURSIVE Reach(_)
Reach(S) ==
    IF S = {} THEN {}
    ELSE S \cup Reach({ m \in Nodes : \E n \in S : m \in Succ[n] })

\* ----------------------------------------------------------------------
\* Main step of Misra's algorithm
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "run"
       /\ frontier /= {}
       /\ \E n \in frontier :
            /\ n \notin marked
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc'       = "run"
    \/ /\ pc = "run"
       /\ frontier /= {}
       /\ \E n \in frontier :
            /\ n \in marked
            /\ marked'   = marked
            /\ frontier' = frontier \ {n}
            /\ pc'       = IF frontier' = {} THEN "done" ELSE "run"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>
Spec ==
    Init /\
    [][Next]_vars /\
    WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file
\* ----------------------------------------------------------------------
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \/ frontier

Inv2 ==
    (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    (frontier = {} => marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

====