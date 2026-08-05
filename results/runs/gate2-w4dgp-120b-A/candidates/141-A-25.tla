---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "looping"

\* The main action of Misra's reachable set algorithm. The frontier and
\* marked sets may overlap, which is what distinguishes this variant from the
\* standard BFS where a node is removed from the frontier as soon as it is
\* marked.
Step(n) ==
    /\ n \in frontier
    /\ IF n \in marked
       THEN /\ frontier' = frontier \ {n}
            /\ marked' = marked
       ELSE /\ frontier' = frontier \cup Succ[n]
            /\ marked' = marked \cup {n}
    /\ pc' = "looping"

Quiesce ==
    /\ frontier = {}
    /\ pc = "looping"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in frontier : Step(n)
    \/ Quiesce

Spec == Init /\ [][Next]_vars

\* Stronger-than-usual invariants: a node's successors are never lost.
Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The nodes reachable from the frontier are exactly the nodes reachable
\* from the union of the visited and frontier sets.
Inv2 ==
    (marked \cup frontier)^{*} = marked \cup (frontier^{*})

Inv3 ==
    {Root} \cup Succ^{*} = marked \cup frontier^{*}

\* Partial correctness: when the algorithm terminates the marked set is
\* exactly the reachable set.
PartialCorrectness ==
    (frontier = {}) => (marked = {Root} \cup Succ^{*})

\* Termination only holds for finite reachable sets.
Termination ==
    (finite({Root} \cup Succ^{*})) ~> (frontier = {})

SpecInv == Spec /\ TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

====