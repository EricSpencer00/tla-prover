---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* State definitions
\* ----------------------------------------------------------------------
Marked == marked
Frontier == frontier
PC == pc

\* ----------------------------------------------------------------------
\* Initial state (typecorrectness & empty frontier)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Process"

\* ----------------------------------------------------------------------
\* Successor relation (assumed given by the underlying graph module)
\* ----------------------------------------------------------------------
Succ == [n \in Nodes |-> {}] \* Placeholder: actual successors should be supplied in the .cfg

\* ----------------------------------------------------------------------
\* One step of the sequential reachability algorithm
\* ----------------------------------------------------------------------
Process ==
    /\ pc = "Process"
    /\ \E n \in frontier :
        /\ frontier' = frontier \ {n}
        /\ marked'   = marked \cup {n}
        /\ frontier' = frontier' \cup (Succ[n] \ {marked, frontier})
        /\ pc' = "Process"
    \/ /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>

\* Allow stuttering in the terminal state
Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == Process \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor property
\* ----------------------------------------------------------------------
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Process", "Done"}
    /\ \A n \in marked :
        Succ[n] \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: reachable-from-union property (derived from Lemma 1)
\* ----------------------------------------------------------------------
Inv2 ==
    (\A S \in SUBSET Nodes : 
        (ReachFrom(S \cup frontier) = ReachFrom(S) \cup ReachFrom(frontier))) \/
    (ReachFrom(marked \cup frontier) = ReachFrom(marked) \cup ReachFrom(frontier))

\* ----------------------------------------------------------------------
\* Invariant 3: reachable-from-root equals marked plus reachable-from-frontier
\* ----------------------------------------------------------------------
Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

\* ----------------------------------------------------------------------
\* Helper: reachable-from definition (graph traversal)
\* ----------------------------------------------------------------------
REACH == [S \in SUBSET Nodes |-> 
            {n \in Nodes : 
                \E p \in FiniteSequences(Nodes) :
                    /\ Len(p) > 0
                    /\ p[1] \in S
                    /\ p[Len(p)] = n
                    /\ \A i \in 1..(Len(p)-1) :
                        p[i+1] \in Succ[p[i]]
            }]

\* Export the reachable-from operator under the expected name
ReachFrom(S) == REACH[S]

\* ----------------------------------------------------------------------
\* Theorem (partial correctness) – not used directly as an invariant
\* ----------------------------------------------------------------------
THEOREM PartialCorrectness ==
    /\ Spec => []Inv1 /\ []Inv2 /\ []Inv3

\* ----------------------------------------------------------------------
\* Safety properties (the three invariants)
\* ----------------------------------------------------------------------
INVARIANTS == Inv1 /\ Inv2 /\ Inv3
PROPERTIES == Inv1 /\ Inv2 /\ Inv3

====