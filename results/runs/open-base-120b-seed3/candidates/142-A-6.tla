---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

\* The graph's successor relation (provided by the algorithm module)
CONSTANT Succ
ASSUME Succ \in [Nodes -> SUBSET Nodes]

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Step"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Step" /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
            /\ pc'       = "Step"
    \/ /\ pc = "Step" /\ frontier = {}
       /\ marked'   = marked
       /\ frontier' = frontier
       /\ pc'       = "Done"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Helper definitions for reachability
\* ----------------------------------------------------------------------
succRel == { <<i, j>> : i \in Nodes /\ j \in Succ[i] }

ReachableFromSet(S) ==
    LET R == TC(succRel) IN
        { y \in Nodes : \E x \in S : <<x, y>> \in R } \cup S

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv1 ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
    marked \cup ReachableFromSet(frontier) =
        ReachableFromSet(marked \cup frontier)

Inv3 ==
    ReachableFromSet({Root}) = marked \cup ReachableFromSet(frontier)

\* ----------------------------------------------------------------------
\* Final theorem (partial correctness)
\* ----------------------------------------------------------------------
FinalTheorem ==
    (pc = "Done") => (marked = ReachableFromSet({Root}))

\* ----------------------------------------------------------------------
\* Collections required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == {Inv1, Inv2, Inv3}
PROPERTIES == {FinalTheorem}

====