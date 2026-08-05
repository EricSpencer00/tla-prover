---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

SuccSet == {<<x, y>> \in Succ : x \in Nodes /\ y \in Nodes}
Neighbors(x) == {y \in Nodes : <<x, y>> \in SuccSet}
Directed ~= TRUE

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "searching", "completed"}

Init ==
    /\ marked = {Root}
    /\ frontier = Neighbors(Root)
    /\ pc = "searching"

Step(x) ==
    /\ x \in frontier
    /\ x \notin marked
    /\ marked' = marked \cup {x}
    /\ frontier' = (frontier \cup Neighbors(x)) \ {x}
    /\ pc' = IF marked' = Nodes THEN "completed" ELSE "searching"

Complete ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ marked = Nodes
    /\ pc' = "completed"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E x \in Nodes : Step(x)
    \/ Complete

Spec == Init /\ [][Next]_vars

Inv1 == \A x \in marked : \E y \in Frontier : <<x, y>> \in SuccSet
Inv2 == \A x \in Nodes :
    x \in marked =>
        (x \in frontier \/ \E y \in marked : <<y, x>> \in SuccSet)
Inv3 == \A x \in Nodes :
    (x \in frontier \/ \E y \in marked : <<y, x>> \in SuccSet) => x \in marked
PartialCorrectness == pc = "completed" => marked = Nodes

Termination == <>(pc = "completed")
====