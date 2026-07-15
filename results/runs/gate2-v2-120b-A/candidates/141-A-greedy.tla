---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Node == Nodes

\* ----------------------------------------------------------------------
\* State predicates
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \in SUBSET Node
    /\ frontier \in SUBSET Node
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Reachability helper
\* ----------------------------------------------------------------------
\* ReachableFrom(S) = set of nodes reachable from any node in S via Succ
ReachableFrom(S) ==
    LET
        step(X) == { y \in Node : \E x \in X : y \in Succ[x] }
    IN
        UNION { step^i[S] : i \in Nat }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Explore ==
    \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = "Running"
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = "Running"

Terminate ==
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Explore
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Inv1: every successor of a marked node is in marked or frontier
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: union of marked and nodes reachable from frontier equals nodes reachable from marked ∪ frontier
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Inv3: nodes reachable from root equal marked plus nodes reachable from frontier
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* Partial correctness: when terminated, marked equals exactly the reachable set
PartialCorrectness ==
    pc = "Done" => marked = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

====