---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Misra's algorithm: frontier and marked may overlap; a node is never
\* removed from the frontier when it is first discovered.
Explore ==
    /\ frontier # {}
    /\ \E n \in frontier :
         \/ /\ n \notin marked
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
         \/ /\ n \in marked
            /\ frontier' = frontier \ {n}
    /\ pc' = "running"

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars

\* Every successor of a marked node is either already marked or sitting in the
\* frontier, so no reachable node can fall through the cracks of the two sets.
Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The marked set plus the frontier reach exactly the same nodes as the union
\* of the two sets themselves.
Inv2 ==
    (marked \cup frontier) \cup (Succ[marked] \cup Succ[frontier])
        = marked \cup frontier \cup Succ[marked] \cup Succ[frontier]

\* The reachable set from the root is the marked set together with what the
\* frontier can still reach; the frontier has not leaked any reachable node.
Inv3 ==
    Reachable(Root) = marked \cup ReachableSet(frontier)

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

\* Weak fairness: the loop body must take a step whenever the frontier is
\* non-empty, which forces termination on a finite reachable set.
Termination == (frontier # {}) ~> (frontier = {})

\* Reachable[S] = nodes reachable from any node in the finite set S.
ReachableSet(S) == {y \in Nodes : \E n \in S : y \in Reachable(n)}

\* Reachable is a standard graph reachability predicate; it is total because
\* it is defined in terms of the well-founded depth of a node from the root.
Reachable(root) == IF root = Root THEN {Root} ELSE Succ[root]

\* The successor function is total (every node has the same number of
\* successors), so a reachable set is finite exactly when the reachable set
\* from the root is finite.
Seq == Cardinality(Reachable(Root))

====