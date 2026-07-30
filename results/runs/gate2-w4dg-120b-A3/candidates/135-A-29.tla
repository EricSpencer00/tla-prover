---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "running", "done"}

Complete == pc = "done"

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore(n) ==
    /\ pc \in {"idle", "running"}
    /\ n \in frontier
    /\ frontier' = (frontier \cup Succ[n]) \ marked
    /\ marked' = marked \cup Succ[n]
    /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier = {n} /\ Succ[n] \subseteq marked THEN "done" ELSE pc

Step ==
    \E n \in Nodes : Explore(n)

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Inv1 == frontier \subseteq marked

Inv2 ==
    \A a \in marked :
        \E s \in Seq(Nodes) :
            /\ Len(s) >= 1
            /\ s[1] = Root
            /\ s[Len(s)] = a
            /\ \A k \in 1 .. (Len(s) - 1) : s[k + 1] \in Succ[s[k]]

Inv3 ==
    \A a \in Nodes :
        (a \in marked) => (\E s \in Seq(Nodes) :
            /\ Len(s) >= 1
            /\ s[1] = Root
            /\ s[Len(s)] = a
            /\ \A k \in 1 .. (Len(s) - 1) : s[k + 1] \in Succ[s[k]])

PartialCorrectness == \A a \in Nodes : a \in marked

Termination == Complete

ConnectedToSomeButNotAll == ConnectedToSomeButNotAll

LimitedSeq == LimitedSeq

====