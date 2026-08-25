---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Nodes,            \* the set of all nodes in the graph
    Root,             \* distinguished start node
    Edge              \* binary relation Edge ⊆ Nodes × Nodes (successor relation)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    Marked,           \* set of nodes already marked as reachable
    Frontier,         \* set of nodes discovered but not yet marked
    pc                \* program counter (abstract)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Successors(n) == { m ∈ Nodes : <<n, m>> ∈ Edge }

\* Reachable(S) is the smallest set containing S and closed under Edge
Reachable(S) == 
    LET
        Closed(T) == 
            /\ S ⊆ T
            /\ ∀ n ∈ T : Successors(n) ⊆ T
    IN
        CHOOSE T ∈ SUBSET Nodes : Closed(T)

\* ----------------------------------------------------------------------
\* Initial state (unspecified in natural‑language description;
\* a reasonable concrete choice is provided)
\* ----------------------------------------------------------------------
Init == 
    /\ Marked = {Root}
    /\ Frontier = {}
    /\ pc = "start"

\* ----------------------------------------------------------------------
\* Actions (abstracted version of the sequential Misra algorithm)
\* ----------------------------------------------------------------------
Expand ==
    ∃ n ∈ Frontier :
        LET succ == Successors(n) IN
        /\ Marked' = Marked
        /\ Frontier' = (Frontier \ {n}) ∪ succ
        /\ pc' = "expand"

MarkNode ==
    ∃ n ∈ Frontier :
        /\ Marked' = Marked ∪ {n}
        /\ Frontier' = Frontier \ {n}
        /\ pc' = "mark"

Next == Expand \/ MarkNode

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv1 == 
    /\ Marked ⊆ Nodes
    /\ Frontier ⊆ Nodes
    /\ ∀ n ∈ Marked :
          ∀ m ∈ Nodes :
              <<n, m>> ∈ Edge => m ∈ Marked \/ m ∈ Frontier

Inv2 == Marked ∪ Reachable(Frontier) = Reachable(Marked ∪ Frontier)

Inv3 == Reachable({Root}) = Marked ∪ Reachable(Frontier)

INVARIANTS == {Inv1, Inv2, Inv3}

\* ----------------------------------------------------------------------
\* Property expressing the partial‑correctness theorem
\* ----------------------------------------------------------------------
TerminationProp == (Frontier = {} => Marked = Reachable({Root}))

PROPERTIES == TerminationProp

====