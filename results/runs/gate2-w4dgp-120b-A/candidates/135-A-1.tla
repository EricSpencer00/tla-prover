---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

Seq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Inv1 ==
    \A n \in Nodes : n \in Frontier => \E m \in Marked : n \in Succ[m]

Inv2 ==
    \A n \in Nodes : n \in Marked => \E p \in Seq(Nodes) : p[1] = Root /\ p[Len(p)] = n /\ \A i \in 1 .. (Len(p)-1) : p[i+1] \in Succ[p[i]]

Inv3 ==
    \A n \in Nodes :
        \A p \in Seq(Nodes) : (p[1] = Root /\ p[Len(p)] = n /\ \A i \in 1 .. (Len(p)-1) : p[i+1] \in Succ[p[i]]) => n \in Marked

Init ==
    /\ Marked = {Root}
    /\ Frontier = {Root}
    /\ pc = "running"

ExpandFrontier ==
    /\ pc = "running"
    /\ Frontier # {}
    /\ \E n \in Frontier :
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = Frontier \cup Succ[n]
    /\ pc' = pc

MarkDone ==
    /\ pc = "running"
    /\ Frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<Marked, Frontier>>

Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

PartialCorrectness == pc = "done"

Termination == <>(pc = "done")

====