---- MODULE Reachable ----
EXTENDS FiniteSets

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

Postpone(m, n) == Cardinality(m) < Cardinality(n)

Next ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
         \/ /\ n \notin marked
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
         \/ /\ n \in marked
            /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \uparrow (marked \cup frontier) = marked \cup frontier

Inv3 ==
    (marked \cup frontier) \uparrow {Root} = marked \cup (frontier \uparrow {Root})

PartialCorrectness ==
    frontier = {} => marked = {Root} \uparrow {Root}

Termination == (marked \cup frontier) \uparrow {Root} = {} \cup (marked \cup frontier) => (marked \cup frontier) \uparrow {Root} = {}

====