---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "expanding", "done"}

Inv1 ==
    \A u \in frontier: \A v \in Succ[u]: v \in marked

Inv2 ==
    \A u \in Nodes: u \in marked => (u = Root \/ \E v \in Nodes: v \in frontier /\ u \in Succ[v])

Inv3 ==
    marked = {u \in Nodes : \E p \in LimitedSeq(Nodes) : p[1] = Root /\ p[Len(p)] = u /\ \A i \in 1..(Len(p) - 1): p[i+1] \in Succ[p[i]]}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "start"

Expand ==
    /\ pc = "start"
    /\ \E v \in Nodes:
        /\ frontier = {}
        /\ v \notin marked
        /\ \E u \in frontier: v \in Succ[u]
        /\ marked' = marked \cup {v}
        /\ frontier' = frontier \cup {v}
        /\ pc' = "expanding"
    /\ UNCHANGED <<pc>>

Recurse ==
    /\ pc = "expanding"
    /\ frontier # {}
    /\ frontier' = frontier \ {CHOOSE v \in frontier : TRUE}
    /\ pc' = "start"
    /\ UNCHANGED <<marked>>

Complete ==
    /\ pc = "expanding"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Expand \/ Recurse \/ Complete \/ Done

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "done")

PartialCorrectness == FrontierReachable == marked \/ frontier

====