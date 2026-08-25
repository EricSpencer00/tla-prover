---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, 
        ReachabilityAlg,   \* the sequential reachability algorithm definition
        ReachabilityLemmas \* graph‑theoretic lemmas used in the proofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Initial state (as defined by the algorithm)
\*--------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"

\*--------------------------------------------------------------------
\* Algorithmic steps (abstracted)
\*--------------------------------------------------------------------
MarkStep ==
    /\ pc = "mark"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \ {n}
        /\ pc' = "expand"

ExpandStep ==
    /\ pc = "expand"
    /\ frontier' = frontier \cup ( \{ m \in Succ[marked] : m \notin marked } )
    /\ UNCHANGED << marked, pc >>

TerminateStep ==
    /\ pc = "terminate"
    /\ frontier = {}
    /\ UNCHANGED << marked, frontier, pc >>

Next ==
    \/ MarkStep
    \/ ExpandStep
    \/ TerminateStep

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
\* Invariant 1: type correctness and successor property
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Invariant 2: marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier)
Inv2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* Invariant 3: Reachable({Root}) = marked ∪ Reachable(frontier)
Inv3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

\* Combined invariant operator required by the .cfg file
INVARIANTS ==
    Inv1 /\ Inv2 /\ Inv3

\*--------------------------------------------------------------------
\* Property: partial correctness upon termination
\*--------------------------------------------------------------------
TerminationCorrectness ==
    (frontier = {} => marked = Reachable({Root}))

PROPERTIES ==
    TerminationCorrectness

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

====