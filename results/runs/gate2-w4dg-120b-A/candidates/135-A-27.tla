---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "running"

Expand(n) ==
    /\ n \in frontier
    /\ \E m \in Succ[n] : m \notin marked
    /\ marked' = marked \cup Succ[n]
    /\ frontier' = (frontier \cup Succ[n]) \ {n}
    /\ pc' = pc

Complete ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Expand(n)
    \/ Complete

Spec == Init /\ [][Next]_vars

Inv1 ==
    /\ frontier \subseteq marked
    /\ \A a \in marked : \E b \in frontier : b \in Succ[a]
    /\ \A a \in marked, b \in frontier, c \in Nodes :
         (c \in Succ[a] /\ c \in Succ[b]) => a = b

Inv2 ==
    /\ marked = {Root}
    /\ \A a \in marked, b \in Nodes : b \in Succ[a] => b \in marked

Inv3 ==
    /\ \A b \in Nodes :
         (\E s \in Seq : s[1] = Root /\ Head(s) = b /\ \A i \in DOMAIN s : s[i] \in marked)
         => b \in marked

PartialCorrectness ==
    \A b \in Nodes :
        (\E s \in Seq : s[1] = Root /\ Head(s) = b /\ \A i \in DOMAIN s : s[i] \in marked)
        => b \in marked

Termination ==
    <>(pc = "done")

====