---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore ==
    /\ pc = "idle"
    /\ frontier # {}
    /\ pc' = "working"
    /\ UNCHANGED <<marked, frontier>>

Mark(n) ==
    /\ pc = "working"
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \ {n}) \cup {m \in Succ[n] : m \notin marked}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "working"

IdleStep == UNCHANGED vars

Next ==
    \/ IdleStep
    \/ Explore
    \/ \E n \in Nodes : Mark(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A s \in frontier : s \notin marked

Inv2 ==
    \A n \in marked : \E m \in frontier : n \in Succ[m]

Inv3 ==
    \A n \in Nodes : (n \in marked) <=> (n \in ReachableFrom(Root))

PartialCorrectness ==
    \A n \in Nodes : (n \in marked) => (n \in ReachableFrom(Root))

Termination == <>(pc = "done")

ReachableFrom(r) ==
    {r} \cup
    {n \in Nodes :
        \E k \in 1..Cardinality(Nodes):
            \E p \in LimitedSeq(Nodes): Len(p) = k /\ p[1] = r /\ p[k] = n
                /\ \A i \in 1..(k - 1): p[i + 1] \in Succ[p[i]]}

ConnectedToSomeButNotAll ==
    {n \in Nodes : Cardinality(Succ[n]) > 0 /\ Cardinality(Succ[n]) < Cardinality(Nodes)}

LimitedSeq(S) ==
    {s \in Seq(S) : Len(s) <= Cardinality(Nodes)}

====