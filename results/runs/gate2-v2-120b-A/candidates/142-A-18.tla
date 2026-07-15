---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root

\* State variables
VARIABLES marked, frontier, pc

\* Helper definitions
\* The set of marked and frontier nodes together
MarkedFrontier == marked \cup frontier

\* The set of nodes reachable from a given set via the graph
\* This uses the standard inductive definition of reachability
ReachableFrom(S) ==
    LET R == { n \in Nodes : n \in S } \cup
            UNION { ReachableFrom(Succ[n]) : n \in S }
    IN R

\* Successors of a node: by default every node can succeed any node
Succ[n_] == Nodes

\* Initial state
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

\* Algorithm actions (not fully specified in description, but sufficient for invariants)
Mark ==
    /\ pc = "Step"
    /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
    /\ pc' = "Step"

Done ==
    /\ pc = "Step"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Step ==
    /\ pc = "Init"
    /\ pc' = "Step"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Step
    \/ Mark
    \/ Done

\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Invariant 1 (type correctness + successor property)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Invariant 2 (graph-theoretic Lemma 1)
Inv2 ==
    (marked \cup ReachableFrom(frontier)) = ReachableFrom(MarkedFrontier)

\* Invariant 3 (Lemma 2 and Lemma 3)
Inv3 ==
    ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

\* The set of INVARIANTS as required by the .cfg
INVARIANTS == Inv1 /\ Inv2 /\ Inv3

\* The property that termination implies marked equals the reachable set
PartialCorrectness ==
    (pc = "Done") => (marked = ReachableFrom({Root}))

PROPERTIES == PartialCorrectness

====