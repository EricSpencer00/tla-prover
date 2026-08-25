---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Nodes,            \* the set of all nodes in the graph
    Root,             \* distinguished start node
    Edge              \* binary relation Edge \subseteq Nodes \times Nodes (successor relation)

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
Successors(n) == { m \in Nodes : <<n, m>> \in Edge }

\* Reachable(S) is the smallest set containing S and closed under Edge
Reachable(S) == 
    LET
        Closed(T) == 
            /\ S \subseteq T
            /\ \A n \in T : Successors(n) \subseteq T
    IN
        CHOOSE T \in SUBSET Nodes : Closed(T)

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
    \E n \in Frontier :
        LET succ == Successors(n) IN
        /\ Marked' = Marked
        /\ Frontier' = (Frontier \ {n}) \cup succ
        /\ pc' = "expand"

MarkNode ==
    \E n \in Frontier :
        /\ Marked' = Marked \cup {n}
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
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A n \in Marked :
          \A m \in Nodes :
              <<n, m>> \in Edge => m \in Marked \/ m \in Frontier

Inv2 == Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS == {Inv1, Inv2, Inv3}

\* ----------------------------------------------------------------------
\* Property expressing the partial‑correctness theorem
\* ----------------------------------------------------------------------
TerminationProp == (Frontier = {} => Marked = Reachable({Root}))

PROPERTIES == TerminationProp

====