---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_, _)
ReachFrom(S, F) ==
    IF S = {} THEN {}
    ELSE
        LET x == CHOOSE y \in S : TRUE
            rest == ReachFrom(S \ {x}, F)
            succs == Succ[x]
        IN
            IF x \in F THEN {x} \cup (succs \cap F) \cup (succs \ rest)
            ELSE {x} \cup (succs \cap F) \cup (succs \ rest)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Step ==
    /\ frontier # {}
    /\ pc' = "running"
    /\ \E x \in frontier :
         \/ /\ x \notin marked
            /\ marked' = marked \cup {x}
            /\ frontier' = frontier \cup Succ[x]
         \/ /\ x \in marked
            /\ frontier' = frontier \ {x}
    /\ UNCHANGED <<pc>>

Terminate ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Step
    \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Inv1 == \A x \in marked : Succ[x] \subseteq (marked \cup frontier)
Inv2 == ReachFrom(marked \cup frontier, frontier) = ReachFrom(Nodes, marked \cup frontier)
Inv3 == ReachFrom(Nodes, {Root}) = marked \cup ReachFrom(frontier, frontier)
PartialCorrectness == pc = "done" => marked = ReachFrom(Nodes, {Root})

Termination == \A n \in Nat : frontier = {} \/ Cardinality(marked) >= n

====