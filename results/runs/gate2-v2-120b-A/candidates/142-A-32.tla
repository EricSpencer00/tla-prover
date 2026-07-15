---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* A helper to denote the set of all successors of a set of nodes
Succ(S) == { y \in Nodes : \E x \in S : y \in SuccOf[x] }

\* A placeholder definition of the graph's adjacency relation.
\* In a concrete model this would be defined in an imported module.
SuccOf == [n \in Nodes |-> {}]

\* ----------------------------------------------------------------------
\* Initial state (the concrete algorithm's INIT, here sketched)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "Start"

\* ----------------------------------------------------------------------
\* Actions (the concrete algorithm's NEXT, sketched)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Start"
       /\ frontier' = Succ({Root})
       /\ marked' = marked
       /\ pc' = "Explore"
    \/ /\ pc = "Explore"
       /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup { y \in Succ({n}) : y \notin marked }
            /\ pc' = "Explore"
    \/ /\ pc = "Explore"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor property
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A x \in marked : Succ({x}) \subseteq marked \cup frontier

\* Invariant 2: reachability decomposition (Lemma 1)
Inv2 ==
    ReachableFrom(marked) \cup ReachableFrom(frontier) =
    ReachableFrom(marked \cup frontier)

\* Invariant 3: marked set equals reachable set at termination (partial correctness)
Inv3 ==
    (pc = "Done") => marked = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Helper definition of reachable nodes from a set of sources
\* ----------------------------------------------------------------------
ReachableFrom(S) ==
    LET NextStep(T) == T \cup { y \in Nodes : \E x \in T : y \in SuccOf[x] } IN
    CHOOSE X \in SUBSET Nodes :
        /\ X = NextStep(X)
        /\ S \subseteq X
        /\ \A Y \in SUBSET Nodes :
                /\ Y = NextStep(Y)
                /\ S \subseteq Y
                => X \subseteq Y

\* ----------------------------------------------------------------------
\* Theorem: partial correctness (marked equals reachable set upon termination)
\* ----------------------------------------------------------------------
THEOREM PartialCorrectness ==
    Spec => []Inv3

\* ----------------------------------------------------------------------
\* Additional definitions required by TLC (optional)
\* ----------------------------------------------------------------------
INVARIANTS == Inv1 /\ Inv2 /\ Inv3

=============================================================================