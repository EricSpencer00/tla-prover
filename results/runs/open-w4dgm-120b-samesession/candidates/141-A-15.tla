---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, Reachability

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
         \/ IF n \notin marked
            THEN /\ marked' = marked \cup {n}
                 /\ frontier' = frontier \cup Succ[n]
            ELSE /\ marked' = marked
                 /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next ==
    \/ Explore

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The frontier may overlap with the marked set, so the invariant is phrased
\* in terms of the reachable set of the frontier rather than the frontier itself.
Inv2 ==
    Reachable(Nodes, {x \in frontier : x \in Nodes}) \cup marked
        = Reachable(Nodes, marked \cup frontier)

Inv3 ==
    Reachable(Nodes, {Root}) = marked \cup Reachable(Nodes, frontier)

PartialCorrectness ==
    \A n \in Nodes : (n \in Reachable(Nodes, {Root}) <=> n \in marked)

Termination ==
    WF_vars(Explore)

LimitedSeq(n) == CHOOSE s \in Seq(Nodes) : Len(s) = n /\ \A i \in 1..n : s[i] \in Nodes

====