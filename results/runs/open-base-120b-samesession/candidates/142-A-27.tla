---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC
EXTENDS ReachAlg, ReachabilityProofs   \* modules containing the algorithm definition and graph lemmas

CONSTANTS Nodes, Root, Edge

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Types and basic definitions
\* ----------------------------------------------------------------------
TypeCorrectness ==
    /\ marked ⊆ Nodes
    /\ frontier ⊆ Nodes
    /\ pc ∈ {"Init", "Loop", "Done"}

Succ[n \in Nodes] == { m \in Nodes : <<n, m>> \in Edge }

\* Reachable nodes from a set S using the transitive closure of Edge
ReachFrom(S \subseteq Nodes) ==
    { y \in Nodes :
        \E x \in S : <<x, y>> \in Edge^* }

\* ----------------------------------------------------------------------
\* Initial state (as in the sequential reachability algorithm)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"
    /\ TypeCorrectness

\* ----------------------------------------------------------------------
\* Next-state relation (simplified version of the algorithm)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Loop"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup Succ[n]
            /\ pc' = "Loop"
            /\ TypeCorrectness
    \/ /\ pc = "Loop"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
       /\ TypeCorrectness

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv1 ==
    /\ TypeCorrectness
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

INVARIANTS == { Inv1, Inv2, Inv3 }

\* ----------------------------------------------------------------------
\* Partial correctness property (final theorem)
\* ----------------------------------------------------------------------
PartialCorrectness ==
    pc = "Done" => marked = ReachFrom({Root})

PROPERTIES == { PartialCorrectness }

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>

Spec ==
    Init /\ [][Next]_vars

====