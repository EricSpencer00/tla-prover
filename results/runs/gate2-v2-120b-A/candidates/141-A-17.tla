---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Nodes,   \* The set of all graph nodes
    Root,    \* The distinguished start node
    Succ,    \* Successor relation: a function mapping each node to a set of its successors
    Seq      \* A finite sequence containing all nodes of the graph (used for type checking)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Node == Nodes
ReachableFrom[n] ==
    IF n \in Nodes THEN
        { m \in Nodes :  <<n, m>> \in Graph }
    ELSE {}

Graph == { <<i, j>> : i \in Nodes /\ j \in Succ[i] }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    visited,    \* Set of marked (visited) nodes
    frontier,   \* Set of nodes pending exploration (may overlap with visited)
    pc          \* Program counter: "Running" or "Done"

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "Running"
    /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
AddNode ==
    \E n \in frontier :
        /\ n \notin visited
        /\ visited' = visited \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc' = pc

RemoveNode ==
    \E n \in frontier :
        /\ n \in visited
        /\ visited' = visited
        /\ frontier' = frontier \ {n}
        /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ visited' = visited
    /\ frontier' = frontier
    /\ pc' = "Done"

Next ==
    \/ AddNode
    \/ RemoveNode
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<visited, frontier, pc>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
\* Type correctness: visited and frontier contain only graph nodes
TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}

\* Inv1: every successor of a visited node is either visited or in the frontier
Inv1 ==
    \A n \in visited : Succ[n] \subseteq visited \cup frontier

\* Inv2: the union of visited and the nodes reachable from the frontier
\* equals the nodes reachable from the union of visited and frontier.
Inv2 ==
    (visited \cup { m \in Nodes : \E n \in frontier : m \in Succ[n] })
    =
    { m \in Nodes :
        \E n \in visited \cup frontier :
            m \in Succ[n] }

\* Inv3: nodes reachable from the root equal visited plus nodes reachable from frontier
Inv3 ==
    (visited \cup { m \in Nodes : \E n \in frontier : m \in Succ[n] })
    =
    { m \in Nodes : \E n \in {Root} \cup visited \cup frontier : m \in Succ*[<<n>>] }

\* PartialCorrectness: when the algorithm terminates, visited equals the set
\* of nodes reachable from the root.
PartialCorrectness ==
    /\ pc = "Done"
    /\ frontier = {}
    /\ visited = { n \in Nodes :
                    \E p \in Seq :
                        (<<Root>> \in p) /\ (<<n>> \in p) /\ p[1] = Root /\ 
                        \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in Graph }

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by the cfg but useful for sanity)
\* ----------------------------------------------------------------------
THEOREM Spec => []PartialCorrectness

====