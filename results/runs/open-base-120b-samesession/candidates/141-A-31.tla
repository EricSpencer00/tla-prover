---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Nodes,      \* The set of all graph nodes
    Root,       \* The distinguished start node (Root \\in Nodes)
    Succ        \* A total function Nodes -> SUBSET Nodes giving successors

\* ----------------------------------------------------------------------
\* Operator that the .cfg substitutes for Succ
ConnectedToSomeButNotAll(n) == Succ[n]

\* Finite version of Seq (used only to satisfy the .cfg substitution)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

\* ----------------------------------------------------------------------
\* Derived relations and helper operators
SuccRel == { <<x, y>> : x \in Nodes /\ y \in ConnectedToSomeButNotAll(x) }

Reach(S) == TC(SuccRel, S)    \* Nodes reachable from any element of S via Succ

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    marked,    \* Set of nodes that have been marked (visited)
    frontier,  \* Set of frontier nodes (may overlap with marked)
    pc         \* Program counter: "run" or "done"

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Main actions
\*   A: pick an unmarked node from the frontier
A ==
    \E n \in frontier :
        /\ n \notin marked
        /\ marked'   = marked \cup {n}
        /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
        /\ pc'       = pc

\*   B: pick a node that is already marked and remove it from the frontier
B ==
    \E n \in frontier :
        /\ n \in marked
        /\ marked'   = marked
        /\ frontier' = frontier \ {n}
        /\ pc'       = pc

\*   C: termination step when the frontier becomes empty
C ==
    /\ frontier = {}
    /\ pc = "run"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

\*   D: stuttering after termination
D ==
    /\ pc = "done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == A \/ B \/ C \/ D

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
Inv1 ==
    \A m \in marked :
        ConnectedToSomeButNotAll(m) \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    (pc = "done") => marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property (termination)
Termination == []<>(pc = "done")

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
SPECIFICATION == Spec
INVARIANTS == TypeOK, Inv1, Inv2, Inv3, PartialCorrectness
PROPERTIES == Termination

=============================================================================