---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "active"

Explore(n) ==
    /\ pc = "active"
    /\ n \in frontier
    /\ frontier' = (frontier \cup Succ[n]) \ marked
    /\ marked' = marked \cup Succ[n]
    /\ pc' = IF frontier' = {} THEN "completed" ELSE pc

Halt ==
    /\ pc = "active"
    /\ frontier = {}
    /\ pc' = "completed"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes: Explore(n)
    \/ Halt

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"active", "completed"}

Inv1 ==
    frontier \subseteq \cup_{n \in marked} Succ[n]

Inv2 ==
    marked = {Root} \cup \cup_{n \in marked} Succ[n]

Inv3 ==
    marked \cup frontier = Nodes

PartialCorrectness ==
    \A n \in Nodes: n \in marked => (n = Root \/ \E m \in marked: n \in Succ[m])

Termination == <>(pc = "completed")

ConnectedToSomeButNotAll(m) == Succ[m]

LimitedSeq(S) == IF S = {} THEN <<>> ELSE CHOOSE f \in [1..Cardinality(S) -> S] : TRUE

====