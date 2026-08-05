---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "running", "done"}

Inv1 ==
    \A j \in frontier : j \in marked

Inv2 ==
    \A j \in Nodes \ frontier : j \notin marked

Inv3 ==
    \A j \in Nodes : j \in marked <=> (j = Root \/ \E i \in frontier : j \in Succ[i])

PartialCorrectness ==
    \A j \in Nodes : (j \in marked) => (j = Root \/ \E i \in frontier : j \in Succ[i])

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore ==
    \/ \E i \in frontier :
        /\ pc = "idle" \/ pc = "running"
        /\ frontier' = frontier \cup Succ[i]
        /\ marked' = marked \cup Succ[i]
        /\ pc' = "running"
    \/ \E i \in frontier :
        /\ pc = "running"
        /\ \A n \in Succ[i] : n \in marked
        /\ frontier' = frontier \ {i}
        /\ pc' = IF frontier = {i} THEN "done" ELSE "running"
        /\ UNCHANGED marked

Next == Explore

Spec == Init /\ [][Next]_vars

Termination == (pc = "idle") ~> (pc = "done")

ConnectedToSomeButNotAll ==
    {n \in Nodes : Cardinality({i \in Nodes : n \in Succ[i]}) >= 1 /\ Cardinality({i \in Nodes : n \in Succ[i]}) <= Cardinality(Nodes) - 1}

LimitedSeq(S) == /\ Len(S) <= Cardinality(Nodes)
                 /\ \A i \in DOMAIN S : S[i] \in ConnectedToSomeButNotAll

====