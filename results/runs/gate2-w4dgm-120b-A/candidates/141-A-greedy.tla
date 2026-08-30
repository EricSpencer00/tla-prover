---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next ==
    \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) = Nodes

Inv3 ==
    Nodes = marked \cup {m \in Nodes : \E n \in frontier : m \in Succ[n]}

PartialCorrectness ==
    \A n \in Nodes : (n \in marked) <=> (\E k \in Nat : k <= Cardinality(Nodes) /\ \E seq \in LimitedSeq(Nodes) : seq[k] = n)

Termination ==
    \A n \in Nodes : ConnectedToSomeButNotAll(n) ~> (n \in marked)

ConnectedToSomeButNotAll(n) ==
    \E m \in Nodes : n \in Succ[m]

LimitedSeq(S) == {s \in Seq(S) : Len(s) <= Cardinality(S)}

====