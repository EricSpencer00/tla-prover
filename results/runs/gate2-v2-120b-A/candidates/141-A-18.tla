---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc, visited

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsNode == \A n \in marked : n \in Nodes
               /\ \A n \in frontier : n \in Nodes

\* The set of nodes reachable from a given set of nodes via the Succ relation
ReachFrom(S) == 
    LET R == S 
    IN  UNION { S } \cup
        \IF S = {} THEN {}
        ELSE
          UNION { R \cup ReachFrom( { y \in Nodes : 
                (\E x \in R : y \in Succ[x]) } ) }

\* Initial state
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"
    /\ visited = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Explore ==
    \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ visited' = visited
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ visited' = visited

Terminate ==
    /\ frontier = {}
    /\ pc = "Terminated"
    /\ UNCHANGED <<marked, visited>>

Next ==
    \/ pc = "Running" /\ Explore
    \/ pc = "Running" /\ Terminate
    \/ pc = "Terminated" /\ UNCHANGED <<marked, frontier, pc, visited>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, visited>>

\* ----------------------------------------------------------------------
\* Safety invariants (as described)
\* ----------------------------------------------------------------------
\* Type correctness: marked and frontier contain only valid nodes
TypeOK == marked \subseteq Nodes /\ frontier \subseteq Nodes

\* Inv1: every successor of a marked node is in marked or frontier
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: the union of marked and nodes reachable from frontier equals nodes reachable from marked ∪ frontier
Inv2 == ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)

\* Inv3: nodes reachable from root equal marked ∪ nodes reachable from frontier
Inv3 == ReachFrom({Root}) = marked \cup ReachFrom(frontier)

\* Partial correctness: upon termination, marked is exactly the reachable set
PartialCorrectness == pc = "Terminated" => marked = ReachFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == 
    \A n \in Nodes : n \in visited => n \in marked

\* visited is updated only when a node is added to marked (optional auxiliary)
VISITED_UPDATE == visited' = visited \cup { n \in marked' : n \notin visited }

\* ----------------------------------------------------------------------
\* THEOREMS (optional, but keep identifier names)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness

====