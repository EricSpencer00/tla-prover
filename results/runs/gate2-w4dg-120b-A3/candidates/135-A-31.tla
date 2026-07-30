---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences, Naturals, Reach

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

ASSUME Cardinality(Nodes) = 4

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "exploring"

Step ==
    \/ \E n \in frontier :
         /\ frontier' = frontier \ {n}
         /\ marked' = marked \cup Succ[n]
         /\ frontier' = frontier \cup (Succ[n] \ marked)
         /\ pc' = IF frontier \ {n} = {} /\ \A m \in Nodes : Succ[m] \subseteq marked THEN "done" ELSE pc
    \/ \E n \in marked :
         /\ frontier = {}
         /\ marked' = marked \cup Succ[n]
         /\ frontier' = frontier \cup (Succ[n] \ marked)
         /\ pc' = IF marked' = Nodes THEN "done" ELSE pc
    \/ pc' = "done"

Next == Step

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"exploring", "done"}

Inv1 ==
    \A n \in marked : \A m \in Succ[n] : m \in marked

Inv2 ==
    \A n \in marked : \A m \in frontier : n \in Succ[m]

Inv3 ==
    marked = Nodes

PartialCorrectness ==
    pc = "done" => marked = Nodes

Termination ==
    (pc = "exploring") ~> (pc = "done")

ConnectedToSomeButNotAll(x) == Succ[x]

\* The .cfg overrides Seq with a finite version, so we must keep EXTENDS Sequences
\* but never actually use Seq in this module; everything is bounded.
LimitedSeq(n) == CHOOSE s \in Seq(Nodes) : Len(s) = n

====