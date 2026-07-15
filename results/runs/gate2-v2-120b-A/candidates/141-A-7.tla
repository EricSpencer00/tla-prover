---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,      \* The set of all graph nodes
    Root,       \* The distinguished start node
    Succ,       \* Succ \in [Nodes -> SUBSET Nodes], the successor function
    Seq         \* An auxiliary constant used only to illustrate that the cfg may list it

VARIABLES
    marked,     \* Set of nodes that have been visited
    frontier,   \* Set of nodes that are pending exploration (may overlap with marked)
    pc          \* Program counter: either "Running" or "Done"

\* ----------------------------------------------------------------------
\* Type correctness invariant (required)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Initial state (required)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Main action (the only nondeterministic step of the algorithm)
\* ----------------------------------------------------------------------
Main ==
    /\ pc = "Running"
    /\ frontier # {}
    /\ \E n \in frontier :
        IF n \notin marked THEN
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc'       = "Running"
        ELSE
            /\ marked'   = marked
            /\ frontier' = frontier \ {n}
            /\ pc'       = "Running"

\* ----------------------------------------------------------------------
\* Termination (stuttering) step
\* ----------------------------------------------------------------------
Terminate ==
    /\ pc = "Running"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Next-state relation (required)
\* ----------------------------------------------------------------------
Next == Main \/ Terminate

\* ----------------------------------------------------------------------
\* Safety invariants (required)
\* ----------------------------------------------------------------------
\* Inv1: every successor of a marked node is either already marked or in the frontier
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: the union of marked and the nodes reachable from frontier equals the nodes reachable from the union of marked and frontier
Inv2 ==
    ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)

\* Inv3: the set of nodes reachable from the root equals the marked set plus nodes reachable from the frontier
Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

\* PartialCorrectness: when the algorithm has terminated, the marked set equals exactly the reachable nodes from the root
PartialCorrectness ==
    pc = "Done" => marked = ReachFrom({Root})

\* ----------------------------------------------------------------------
\* Reachability helper (recursive definition)
\* ----------------------------------------------------------------------
RECURSIVE ReachFrom(_)

ReachFrom(S) ==
    IF S = {} THEN {}
    ELSE
        LET n == CHOOSE x \in S : TRUE IN
        {n} \cup ReachFrom((S \ {n}) \cup Succ[n])

\* ----------------------------------------------------------------------
\* Specification (required)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Properties (required)
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

====