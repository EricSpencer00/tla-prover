---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*-------------------------------------------------
\* Constants (declared in the .cfg)
\*-------------------------------------------------
CONSTANTS Nodes, Root

\*-------------------------------------------------
\* Types
\*-------------------------------------------------
Node == Nodes

\*-------------------------------------------------
\* State variables
\*-------------------------------------------------
VARIABLES marked, frontier, pc

\*-------------------------------------------------
\* Helper definitions
\*-------------------------------------------------
Unmarked == Nodes \ marked

\* Successors relation (placeholder; should be defined in the
\* module that this file extends, but we provide a generic version)
Succ == [n \in Nodes |-> {}] \* replace with actual successor function

\*-------------------------------------------------
\* Invariant 1: type correctness and the frontier property
\*-------------------------------------------------
Inv1 == /\ marked \subseteq Nodes
        /\ frontier \subseteq Nodes
        /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

\*-------------------------------------------------
\* Invariant 2: reachable equivalence lemma
\*-------------------------------------------------
Inv2 == ReachableFromRoot == marked \cup ReachableFromFrontier

\*-------------------------------------------------
\* Invariant 3: reachable-from-root equality
\*-------------------------------------------------
Inv3 == ReachableFromRoot == marked \cup ReachableFromFrontier

\*-------------------------------------------------
\* Reachability definitions (graph-theoretic lemmas)
\*-------------------------------------------------
REACH == [n \in Nodes |-> REACH[n]]
REACH == [n \in Nodes |-> 
            IF n = Root THEN {Root}
            ELSE { n } \cup 
                 UNION { REACH[m] : m \in Nodes, 
                         \E p \in frontier : n \in Succ[p] }]

ReachableFromFrontier == UNION { REACH[n] : n \in frontier }
ReachableFromRoot == REACH[Root]

\*-------------------------------------------------
\* Initial predicate
\*-------------------------------------------------
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"

\*-------------------------------------------------
\* Actions
\*-------------------------------------------------
Next == 
    \/ /\ pc = "Loop"
       /\ \E n \in frontier :
            /\ frontier' = frontier \ {n}
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier' \cup (Succ[n] \ Unmarked)
            /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

\*-------------------------------------------------
\* Specification
\*-------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*-------------------------------------------------
\* Theorem (partial correctness)
\*-------------------------------------------------
THEOREM PartialCorrectness ==
    Spec => [] (pc = "Done" => marked = ReachableFromRoot)

====